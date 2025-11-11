open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for 
     compiling local variable declarations
*)

type elt = 
  | L of Ll.lbl             (* block labels *)
  | I of uid * Ll.insn      (* instruction *)
  | T of Ll.terminator      (* block terminators *)
  | G of gid * Ll.gdecl     (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn      (* hoisted entry block instructions *)

type stream = elt list
let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x,i) -> I (x,i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  =
    let gs, einsns, insns, term_opt, blks = List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l ->
           begin match term_opt with
           | None -> 
              if (List.length insns) = 0 then (gs, einsns, [], None, blks)
              else failwith @@ Printf.sprintf "build_cfg: block labeled %s has\
                                               no terminator" l
           | Some term ->
              (gs, einsns, [], None, (l, {insns; term})::blks)
           end
        | T t  -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid,insn)  -> (gs, einsns, (uid,insn)::insns, term_opt, blks)
        | G (gid,gdecl) ->  ((gid,gdecl)::gs, einsns, insns, term_opt, blks)
        | E (uid,i) -> (gs, (uid, i)::einsns, insns, term_opt, blks)
      ) ([], [], [], None, []) code
    in
    match term_opt with
    | None -> failwith "build_cfg: entry block has no terminator" 
    | Some term -> 
       let insns = einsns @ insns in
       ({insns; term}, blks), gs


(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct

  type t = (Ast.id * (Ll.ty * Ll.operand)) list
  let empty = []

  (* Add a binding to the context *)
  let add (c:t) (id:id) (bnd:Ll.ty * Ll.operand) : t = (id,bnd)::c

  (* Lookup a binding in the context *)
  let lookup (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> Ptr (Fun (args, ret)), g
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id:Ast.id) (c:t) : (Ll.ty * Ll.operand) option = (* Same as lookup_function, but does not give an error *)
    try Some (lookup_function id c) with _ -> None
  
end


let rec ctxt_num_types (c:Ctxt.t) (t:Ll.ty) : int =
  begin match c with
   | [] -> 0
   | (_, (t, _))::xs -> 1 + (ctxt_num_types xs t)
   | _ -> ctxt_num_types c t
  end
(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The 
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool  -> I1
  | Ast.TInt   -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString  -> I8
  | Ast.RArray u -> Struct [I64; Array(0, cmp_ty u)]
  | Ast.RFun (ts, t) -> 
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid  -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty =
  List.map cmp_ty ts, cmp_ret_ty r


let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot       -> (TBool, TBool)

(* Compiler Invariants

   The LLVM IR type of a variable (whether global or local) that stores an Oat
   array value (or any other reference type, like "string") will always be a
   double pointer.  In general, any Oat variable of Oat-type t will be
   represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
   x : int will be represented by an LLVM IR value of type i64*, y : string will
   be represented by a value of type i8**, and arr : int[] will be represented
   by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
   "single" or "double" pointer depends on whether t is a reference type.

   We can think of the compiler as paying careful attention to whether a piece
   of Oat syntax denotes the "value" of an expression or a pointer to the
   "storage space associated with it".  This is the distinction between an
   "expression" and the "left-hand-side" of an assignment statement.  Compiling
   an Oat variable identifier as an expression ("value") does the load, so
   cmp_exp called on an Oat variable of type t returns (code that) generates a
   LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
   does not do the load, so cmp_lhs called on an Oat variable of type t returns
   and operand of type (cmp_ty t)*.  Extending these invariants to account for
   array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
   left-hand-side, so we compile it as follows: compile e1 as an expression to
   obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
   compile e2 as an expression to obtain an operand of type i64, generate code
   that uses getelementptr to compute the offset from the array value, which is
   a pointer to the "storage space associated with e1[e2]".

   On the other hand, compiling e1[e2] as an expression (to obtain the value of
   the array), we can simply compile e1[e2] as a left-hand-side and then do the
   load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
   writing this, I think it could make sense to factor the Oat grammar in this
   way, which would make things clearer, I may do that for next time around.]]

 
   Consider globals7.oat

   /--------------- globals7.oat ------------------ 
   global arr = int[] null;

   int foo() { 
     var x = new int[3]; 
     arr = x; 
     x[2] = 3; 
     return arr[2]; 
   }
   /------------------------------------------------

   The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
   the corresponding LLVM IR declaration will look like:

   @arr = global { i64, [0 x i64] }* null

   This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
   which is consistent with the type of a locally-declared array variable.

   The local variable x would be allocated and initialized by (something like)
   the following code snippet.  Here %_x7 is the LLVM IR uid containing the
   pointer to the "storage space" for the Oat variable x.

   %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
   %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
   %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
   store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

   (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has 
       the same type as @arr 

   (2) @oat_alloc_array allocates len+1 i64's 

   (3) we have to bitcast the result of @oat_alloc_array so we can store it
        in %_x7 

   (4) stores the resulting array value (itself a pointer) into %_x7 

  The assignment arr = x; gets compiled to (something like):

  %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
  store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

  (5) load the array value (a pointer) that is stored in the address pointed 
      to by %_x7 

  (6) store the array value (a pointer) into @arr 

  The assignment x[2] = 3; gets compiled to (something like):

  %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
  %_index_ptr11 = getelementptr { i64, [0 x  i64] }, 
                  { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
  store i64 3, i64* %_index_ptr11                                 ;; (9)

  (7) as above, load the array value that is stored %_x7 

  (8) calculate the offset from the array using GEP

  (9) store 3 into the array

  Finally, return arr[2]; gets compiled to (something like) the following.
  Note that the way arr is treated is identical to x.  (Once we set up the
  translation, there is no difference between Oat globals and locals, except
  how their storage space is initially allocated.)

  %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
  %_index_ptr14 = getelementptr { i64, [0 x i64] },                
                 { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
  %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
  ret i64 %_index15

  (10) just like for %_x9, load the array value that is stored in @arr 

  (11)  calculate the array index offset

  (12) load the array value at the index 

*)

(* Global initialized arrays:
    
  There is another wrinkle: To compile global initialized arrays like in the
  globals4.oat, it is helpful to do a bitcast once at the global scope to
  convert the "precise type" required by the LLVM initializer to the actual
  translation type (which sets the array length to 0).  So for globals4.oat,
  the arr global would compile to (something like):

  @arr = global { i64, [0 x i64] }* bitcast 
           ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* ) 
  @_global_arr5 = global { i64, [4 x i64] } 
                  { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }

*) 



(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s:string) -> incr c; Printf.sprintf "_%s%d" s (!c)

(* Amount of space an Oat type takes when stored in the satck, in bytes.  
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t:Ast.ty) (size:Ll.operand) : Ll.ty * operand * stream =
  let ans_id, arr_id = gensym "array", gensym "raw_array" in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ans_ty, Id ans_id, lift
    [ arr_id, Call(arr_ty, Gid "oat_alloc_array", [I64, size])
    ; ans_id, Bitcast(arr_ty, Id arr_id, ans_ty) ]

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression. 

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a 
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions

*)
  
let ast_to_ll_binop (ast_op : Ast.binop) : Ll.bop =
  begin match ast_op with
  | Add -> Ll.Add
  | Sub -> Ll.Sub
  | Mul -> Ll.Mul
  | Eq -> failwith "ast_to_ll_binop case not implemented"
  | Neq -> failwith "ast_to_ll_binop neq not implemented"
  | Lt -> failwith "ast_to_ll_binop case not implemented"
  | Lte -> failwith "ast_to_ll_binop case not implemented"
  | Gt -> failwith "ast_to_ll_binop case not implemented"
  | Gte -> failwith "ast_to_ll_binop case not implemented"
  | And -> Ll.And
  | Or -> Ll.Or
  | IAnd -> failwith "ast_to_ll_binop case not implemented"
  | IOr -> failwith "ast_to_ll_binop case not implemented"
  | Shl -> Ll.Shl
  | Shr -> Ll.Lshr
  | Sar -> Ll.Ashr
  end

let rec exp_type (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty = (* only to be used for args*)
  begin match exp.elt with
  | CNull(_) -> failwith "exp_type of CNull not implemented"
  | CBool(_) -> Ll.I1
  | CInt(_) -> Ll.I64
  | CStr(_) -> Ll.Ptr(Ll.I8)
  | CArr(t, _) -> Ll.Ptr(cmp_ty t)
  | NewArr(t,_) -> Ll.Ptr(cmp_ty t)
  | Id(id) -> let (Ll.Ptr(ret_ty), ret_oper) = Ctxt.lookup id c in ret_ty
  | Bop(_, exp1_node, exp2_node) -> exp_type c exp1_node
  | Uop(_, exp_node) -> exp_type c exp_node
  | _ -> failwith "cmp_exp_type case unimplemented"
  end

let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ctxt.t * Ll.ty * Ll.operand * stream =
  let rem_exp = exp.elt in
  begin match rem_exp with
    | CInt i -> let arg_name = gensym "int" in
                let cnew = (Ctxt.add c arg_name (cmp_ty TInt, Id arg_name)) in
                c = cnew;
                (c,(cmp_ty TInt), Ll.Id arg_name, [I (arg_name,  Ll.Binop (Ll.Add ,(cmp_ty TInt), Const(i), Const(0L)))])
    | CBool b -> let v = if(b) then 1L else 0L in
                 let arg_name = gensym "bool" in
                 let cnew = (Ctxt.add c arg_name (cmp_ty TBool, Id arg_name)) in
                 c = cnew;
                 (c,(cmp_ty TBool), Ll.Id arg_name, [I (arg_name, Ll.Binop(Ll.Or, (cmp_ty TBool), Const(v), Const(0L) ))])
    | CStr s -> failwith "cmp_exp string case not implemented"
    | CNull r -> failwith "cmp_exp null case not implemented"
    | Bop(_) -> cmp_exp_bop c rem_exp 
    | Uop(_) -> cmp_exp_uop c rem_exp
    | Id(id) -> let (var_ty_ptr, var_ptr_oper) = Ctxt.lookup id c in
                let Ll.Ptr(var_ty) = var_ty_ptr in
                let var_val_id = gensym "id" in
                let c1 = Ctxt.add c var_val_id (var_ty, Ll.Id(var_val_id)) in
                let insn = I(var_val_id, Load(Ll.Ptr(var_ty), var_ptr_oper)) in
                (c1, var_ty, Ll.Id(var_val_id), [insn])
    | Index(_) -> failwith "cmp_exp index not implemented"
    | Call(_) -> cmp_exp_call c rem_exp
    | _ -> failwith "cmp_exp case unimplemented"
  end
and cmp_exp_call (c:Ctxt.t) (exp:Ast.exp) : Ctxt.t * Ll.ty * Ll.operand * stream = failwith "cmp_exp call unimplemented"

and cmp_exp_bop (c:Ctxt.t) (exp:Ast.exp) : Ctxt.t * Ll.ty * Ll.operand * stream =
  let Ast.Bop(op, exp1_node, exp2_node) = exp in
  let (exp1, exp2) = (exp1_node.elt, exp2_node.elt) in
  let (c1, exp1_ty, exp1_oper, exp1_stream) = cmp_exp c exp1_node in
  let (c2,exp2_ty, exp2_oper, exp2_stream) = cmp_exp c1 exp2_node in
  let arg_name = gensym "bop" in
  let arg_type = exp1_ty in
  c = Ctxt.add c2 arg_name (exp1_ty, (Ll.Id arg_name));
  let ll_bop = ast_to_ll_binop op in
  (c, exp1_ty, (Ll.Id arg_name), exp1_stream@exp2_stream@[I (arg_name, Ll.Binop(ll_bop, exp1_ty, exp1_oper, exp2_oper))])
and cmp_exp_uop (c:Ctxt.t) (exp:Ast.exp) : Ctxt.t * Ll.ty * Ll.operand * stream =
  let Ast.Uop(op, exp_node) = exp in
  let exp = exp_node.elt in
  let (c1, exp_ty, exp_oper, exp_stream) = cmp_exp c exp_node in
  let arg_name = gensym "uop" in
  let arg_type = exp_ty in
  c = Ctxt.add c1 arg_name (exp_ty, (Ll.Id arg_name));
  (c, exp_ty, (Ll.Id arg_name), exp_stream@[I (arg_name, Ll.Binop(Ll.Xor, Ll.I64, Ll.Const(-1L), exp_oper)); E(arg_name, Ll.Binop(Ll.Add, Ll.I64, Ll.Const(1L), Ll.Id(arg_name)))])
(* Compile a statement in context c with return typ rt. Return a new context, 
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarations, you will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a bindings to the context for local variable 
     declarations
   
   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!

 *)
(*  let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ll.ty * Ll.operand * stream = *)

let cmp_ret (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt) : Ctxt.t * stream =
  begin match stmt with
  | Ret(None) -> (c, [T(Ret(Void,None))])
  | Ret(Some(exp_node)) -> let exp = exp_node.elt in
          begin match exp with
          | CBool b -> let v = if(b) then 1L else 0L in
               (c, [T(Ret(I1, Some(Ll.Const(v))))])
          | CInt i -> (c, [T(Ret(I64, Some(Ll.Const(i))))])
          | CNull n -> failwith "cmp_ret null not implemented"
          | CStr s -> failwith "cmp_ret string not implemented"
          | Bop(_) -> let (ret_ctxt,ret_ty, ret_oper, ret_stream) = cmp_exp c exp_node in
                      (ret_ctxt, ret_stream@[T (Ll.Ret(rt, Some(ret_oper)))])
          | Uop(_) -> let (ret_ctxt,ret_ty, ret_oper, ret_stream) = cmp_exp c exp_node in
                      (ret_ctxt, ret_stream@[T (Ll.Ret(rt, Some(ret_oper)))]) 
          | Id(ret_id) -> let (ret_ty_ptr, ret_oper) = Ctxt.lookup ret_id c in
                          let Ptr(ret_ty) = ret_ty_ptr in
                          let val_name = ret_id^".val" in
                          let c1 = Ctxt.add c val_name (ret_ty, Ll.Id(val_name)) in
                          (c1, [I (val_name, Ll.Load(ret_ty_ptr, ret_oper)); T(Ll.Ret(ret_ty, Some(Ll.Id(val_name))))])
          | _ -> failwith "cmp_ret case not implemented"
          end
  end
  
let cmp_assn (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt) : Ctxt.t * stream =
  let Assn(var_node, exp_node) = stmt in
  let (c1, exp_ty, exp_oper, exp_stream) = cmp_exp c exp_node in
  let var = var_node.elt in
  begin match var with
    | Id(id) -> let (var_ty, var_oper) = Ctxt.lookup id c1 in
                (c1, exp_stream@[I ("", Ll.Store(exp_ty, exp_oper, var_oper))])
    | _ -> failwith "cmp_assn case unimplemented"           
  end
let cmp_decl (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt) : Ctxt.t * stream =
  let Decl(var_id, exp_node) = stmt in
  let (c1, exp_ty, exp_oper, exp_stream) = cmp_exp c exp_node in
  let (var_ptr_ty, var_ptr_oper) = Ctxt.lookup var_id c1 in
  (c1, exp_stream@[I("", Ll.Store(exp_ty, exp_oper, var_ptr_oper))])
(* let rec cmp_exp (c:Ctxt.t) (exp:Ast.exp node) : Ctxt.t * Ll.ty * Ll.operand * stream = *)
(* cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream = *)

let rec cmp_param (c:Ctxt.t) (exp_node_list : exp node list) : (Ctxt.t)*((Ll.ty * Ll.operand) list)*stream =
  begin match exp_node_list with
  | [] -> (c,[], [])
  | x::xs -> let arg_exp = x.elt in
             let (c1, arg_ty, arg_oper, arg_stream) = cmp_exp c x in
             let (rec_ctxt, rec_list, rec_stream) = cmp_param c1 xs in
             (rec_ctxt, (arg_ty, arg_oper)::rec_list, arg_stream@rec_stream)
  end

  
let rec cmp_stmt (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt node) : Ctxt.t * stream =
  let rem_stmt = stmt.elt in
  begin match rem_stmt with
    | Ret(_) -> let (c_ret, ret_stream) = cmp_ret c rt rem_stmt in
                (c_ret, List.rev(ret_stream))
    | Assn(_) -> let (c_ret, ret_stream) = cmp_assn c rt rem_stmt in
                 (c_ret, List.rev(ret_stream))
    | Decl(_) -> let (c_ret, ret_stream) = cmp_decl c rt rem_stmt in
                 (c_ret, List.rev(ret_stream))
    | SCall(_) -> let (c_ret, ret_stream) = cmp_scall c rt rem_stmt in
                 (c_ret, List.rev(ret_stream))
    | If(_) -> let (c_ret, ret_stream) = cmp_if c rt rem_stmt in
                 (c_ret, List.rev(ret_stream))
    | For(_) ->  failwith "cmp_stmt For not implemented"
    | While(_) -> let (c_ret, ret_stream) = cmp_while c rt rem_stmt in
                 (c_ret, List.rev(ret_stream))
    |_ -> failwith "cmp_stmt non matching case not implemented, should not be the case"
  end

(* Compile a series of statements *)
and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream =
  List.fold_left (fun (c, code) s -> 
      let c, stmt_code = cmp_stmt c rt s in
      c, code >@ stmt_code
    ) (c,[]) stmts

and cmp_while (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt) : Ctxt.t * stream =
  (* create two labels, one for the while loop, the other for the exit *)
  let while_label = gensym "while" in
  let exit_label = gensym "exit" in
  let While(exp_node, stmt_node_list) = stmt in
  let (c1, b_ty, b_oper, b_stream) = cmp_exp c exp_node in
  let check_insn = T(Ll.Cbr(b_oper, while_label, exit_label)) in
  let (c2, while_stream) = cmp_block c1 (Ll.Void) stmt_node_list in
  (c2, check_insn::(L(while_label))::[]@while_stream@[check_insn; L(exit_label)])

and cmp_if (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt) : Ctxt.t * stream =
  let If(exp_node, then_node_list, else_node_list) = stmt in
  let then_label = gensym "then" in
  let else_label = gensym "else" in
  let exit_label = gensym "exit" in
  let (c1, b_ty, b_oper, b_stream) = cmp_exp c exp_node in
  let check_insn = T(Ll.Cbr(b_oper, then_label, else_label)) in
  let last_insn = T(Ll.Br(exit_label)) in
  let (c2, then_stream) = cmp_block c1 (Ll.Void) then_node_list in
  let (c3, else_stream) = cmp_block c2 (Ll.Void) else_node_list in
  (c3, b_stream@[check_insn; L(then_label)]@then_stream@[T(Ll.Br(exit_label));L(else_label)]@else_stream@[last_insn; L(exit_label)])

(*  let lookup_function (id:Ast.id) (c:t) : Ll.ty * Ll.operand = *)
and cmp_scall (c:Ctxt.t) (rt:Ll.ty) (stmt:Ast.stmt) : Ctxt.t * stream =
  let SCall(func_node, arg_node_list) = stmt in
  let Id(func_name) = func_node.elt in
  let (func_ty, func_oper) = Ctxt.lookup_function func_name c in
  let (c1,args_list, args_stream) = cmp_param c arg_node_list in

  (c1, args_stream@[I("",Ll.Call (func_ty, func_oper, args_list))])

(* Adds each function identifer to the context at an
   appropriately translated type.  

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
    List.fold_left (fun c -> function
      | Ast.Gfdecl { elt={ frtyp; fname; args } } ->
         let ft = TRef (RFun (List.map fst args, frtyp)) in
         Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c
    ) c p 

(* Populate a context with bindings for global variables 
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C). 
*)

(*  type t = (Ast.id * (Ll.ty * Ll.operand)) list  *)
let glb_ctxt_fold (c:Ctxt.t) (d:decl) : Ctxt.t =
  begin match d with
    | Ast.Gvdecl {elt = {name = g_name; init = g_exp_node} } ->
      let g_exp = g_exp_node.elt in
      (match g_exp with
        | CNull rt -> Ctxt.add c g_name (cmp_rty rt, Gid g_name)
        | CBool b -> Ctxt.add c g_name (Ll.Ptr(cmp_ty Ast.TBool), Gid g_name)
        | CInt i -> Ctxt.add c g_name (Ll.Ptr(cmp_ty Ast.TInt), Gid g_name)
        | CStr s -> Ctxt.add c g_name (Ll.Ptr(Ll.I8), Gid g_name)
        | CArr (t,e) -> failwith "glb_ctxt_fold CArr case not implemented"
        | _ -> failwith "g_exp case not implemented")

    | _ -> c
  end

let cmp_global_ctxt (c:Ctxt.t) (p:Ast.prog) : Ctxt.t =
  List.rev (List.fold_left glb_ctxt_fold c p)

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from 
 *)
  


let args_types_fold (c:Ctxt.t) (acc : Ll.ty list) (arg : (Ast.ty * Ast.id)) : Ll.ty list =
  begin match arg with
  | (t, _) -> (cmp_ty t)::acc
  | _ -> failwith "some args_types_fold case unimplemented, should not be the case"
  end
let args_types (c:Ctxt.t) (args : (Ast.ty * Ast.id) list) : (Ll.ty list) =
  List.rev (List.fold_left (args_types_fold c) [] args)

let args_uids_fold (c:Ctxt.t) (acc : Ll.uid list) (arg : (Ast.ty * Ast.id)) : Ll.uid list =
  begin match arg with
  | (_, name) -> (name)::acc
  | _ -> failwith "some args_uids_fold case unimplemented, should not be the case"
  end
  
let args_uids (c:Ctxt.t) (args : (Ast.ty * Ast.id) list) : (Ll.uid list) =
  List.rev (List.fold_left (args_uids_fold c) [] args)

let rec remove_nodes (l:'a node list) : ('a) list =
  begin match l with
  | [] -> []
  | x::xs -> (x.elt)::(remove_nodes xs)
  end
(* and cmp_block (c:Ctxt.t) (rt:Ll.ty) (stmts:Ast.block) : Ctxt.t * stream = *)
(* let cfg_of_stream (code:stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list  = *)
let is_decl (stmt:Ast.stmt) : bool =
  match stmt with
  | Decl(_) -> true
  | _ -> false

let rec decl_to_vdecl  (decl_list : stmt list)  : Ast.vdecl list =
  match decl_list with
  | [] -> []
  | Decl(x)::xs -> x::(decl_to_vdecl xs)


let rec decl_args (c:Ctxt.t) (decl_list : (Ast.id *( Ast.exp node)) list) : Ctxt.t * (stream) =
  match decl_list with
  | [] -> (c,[])
  | x::xs -> let (arg_id, arg_exp_node) = x in
             let arg_ll_ty = exp_type c arg_exp_node in
             let alloca_id = gensym arg_id in
             let alloca_insn = Ll.Alloca(arg_ll_ty) in
             let c1 = Ctxt.add c arg_id (Ll.Ptr(arg_ll_ty), Ll.Id(alloca_id)) in
             let (ret_c, ret_list) = decl_args c1 xs in
             (ret_c, E(alloca_id, alloca_insn)::ret_list)

let local_vars (c:Ctxt.t) (stmt_node_list : stmt node list) : Ctxt.t * stream =
  let stmt_list = remove_nodes stmt_node_list in
  let decl_list = List.filter is_decl stmt_list in
  let vdecl_list = decl_to_vdecl decl_list in
  decl_args c vdecl_list
  

let rec alloca_args (args_list : (Ast.ty * Ast.id) list) : Ctxt.t * stream =
  begin match args_list with 
  | [] -> ([],[])
  | x::xs -> let (arg_ast_ty, arg_id) = x in
             let arg_ll_ty = cmp_ty arg_ast_ty in
             let alloca_id = gensym arg_id in
             let ret_elt = E(alloca_id, Ll.Alloca(arg_ll_ty)) in
             let ret_bnd = (arg_id, (arg_ll_ty, Ll.Id(alloca_id))) in
             let (rec_ctxt, rec_stream) = alloca_args xs in
             (ret_bnd::rec_ctxt, ret_elt::rec_stream)
  end 



let cmp_fdecl (c:Ctxt.t) (f:Ast.fdecl node) : Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let {frtyp=frtyp; fname=fname; args=args; body=body} = f.elt in
  let fty_list = args_types c args in
  let ret_fty = (fty_list, (cmp_ret_ty frtyp)) in
  let ret_f_param = args_uids c args in
  let (args_ctxt, args_stream) = alloca_args args in
  let c1 = args_ctxt@c in
  let (c2, vars_stream) = local_vars c1 body in
  let (cmp_block_ctxt, cmp_block_stream) = cmp_block c2 (cmp_ret_ty frtyp) body in
  let (ret_cfg, ret_gdecls) = cfg_of_stream (args_stream@vars_stream@cmp_block_stream) in
  let ret_fdecl = {f_ty = ret_fty; f_param=ret_f_param; f_cfg=ret_cfg} in
  (ret_fdecl, ret_gdecls)

(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp c (e:Ast.exp node) : Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  let {elt=g_exp; loc=g_exp_loc} = e in
  begin match g_exp with
    | CBool b ->
                let v = (if (b) then 1L else 0L) in
                let g_dec = ((cmp_ty TBool),(GInt v)) in 
                (g_dec, [])
    | CInt i ->
                let g_dec = ( (cmp_ty TInt),(GInt i)) in 
                (g_dec, [])
    | CStr s ->
                let g_dec = (Ll.Ptr(I8),(GString s)) in
                (g_dec, [])
    | _ -> failwith "g_exp case not implemented"            
  end
(* Oat internals function context ------------------------------------------- *)
let internals = [
    "oat_alloc_array",         Ll.Fun ([I64], Ptr I64)
  ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [ "array_of_string",  cmp_rty @@ RFun ([TRef RString], RetVal (TRef(RArray TInt)))
  ; "string_of_array",  cmp_rty @@ RFun ([TRef(RArray TInt)], RetVal (TRef RString))
  ; "length_of_string", cmp_rty @@ RFun ([TRef RString],  RetVal TInt)
  ; "string_of_int",    cmp_rty @@ RFun ([TInt],  RetVal (TRef RString))
  ; "string_cat",       cmp_rty @@ RFun ([TRef RString; TRef RString], RetVal (TRef RString))
  ; "print_string",     cmp_rty @@ RFun ([TRef RString],  RetVoid)
  ; "print_int",        cmp_rty @@ RFun ([TInt],  RetVoid)
  ; "print_bool",       cmp_rty @@ RFun ([TBool], RetVoid)
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p:Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt = 
    List.fold_left (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* compile functions and global variables *)
  let fdecls, gdecls = 
    List.fold_right (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt=gd } -> 
           let ll_gd, gs' = cmp_gexp c gd.init in
           (fs, (gd.name, ll_gd)::gs' @ gs)
        | Ast.Gfdecl fd ->
           let fdecl, gs' = cmp_fdecl c fd in
           (fd.elt.fname,fdecl)::fs, gs' @ gs
      ) p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
