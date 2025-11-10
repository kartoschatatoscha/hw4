%{
open Ast

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token <bool>   BOOL
%token NULL
%token <string> STRING
%token <string> IDENT

%token TINT     /* int */
%token TVOID    /* void */
%token TSTRING  /* string */
%token TBOOL    /* bool */
%token NEW      /* new */
%token IF       /* if */
%token ELSE     /* else */
%token FOR      /* for */
%token WHILE    /* while */
%token RETURN   /* return */
%token VAR      /* var */
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQEQ     /* == */
%token EQ       /* = */
%token NOTEQ    /* != */
%token SHL      /* << */
%token SHR      /* >> */
%token SAR      /* >>> */
%token LT       /* < */
%token LE       /* <= */
%token GT       /* > */
%token GE       /* >= */
%token AND      /* & */
%token OR       /* | */
%token BAND     /* [&] */
%token BOR      /* [|] */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token GLOBAL   /* global */
%token TRUE     /* true */
%token FALSE     /* false */

(* higher precedence appears lower*)
(* same precedence appears on the same line*)
%left BOR
%left BAND
%left OR
%left AND
%left NOTEQ EQEQ
%left LT LE GT GE
%left SHL SHR SAR
%left PLUS DASH     (*  left associative *)
%left STAR
  
%nonassoc BANG TILDE
%nonassoc LBRACKET LPAREN RBRACKET RPAREN LBRACE RBRACE COMMA SEMI VAR RETURN WHILE FOR ELSE IF TSTRING TVOID TINT TBOOL NEW TRUE FALSE

/* ---------------------------------------------------------------------- */

%start prog      (* start rule*) 
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TBOOL  { TBool }
  | TINT   { TInt }
  | r=rtyp { TRef r } 

%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

%inline rtyp: (* Incomplete *)
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | PLUS   { Add }
  | DASH   { Sub }
  | STAR   { Mul }
  | EQEQ   { Eq }
  | SHL    { Shl }
  | SHR    { Shr }
  | SAR    { Sar }
  | LT     { Lt }
  | LE     { Lte }
  | GT     { Gt }
  | GE     { Gte }
  | AND    { And }
  | OR     { Or }
  | NOTEQ  { Neq }
  | BAND   { IAnd }
  | BOR    { IOr}

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | i=INT      { loc $startpos $endpos @@ CInt i }
  | s=STRING   { loc $startpos $endpos @@ CStr s }
  | t=rtyp NULL  { loc $startpos $endpos @@ CNull t }
  | b=BOOL      { loc $startpos $endpos @@ CBool b }
  | NEW typ=ty LBRACKET RBRACKET LBRACE l=separated_list(COMMA,gexp) RBRACE  { loc $startpos $endpos @@ CArr(typ, l) }

lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

exp:
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | s=STRING            { loc $startpos $endpos @@ CStr s }
  | t=rtyp NULL         { loc $startpos $endpos @@ CNull t }
  | b=BOOL              { loc $startpos $endpos @@ CBool b }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (e,es) }
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | LPAREN e=exp RPAREN { e }    (* previous 3 should be in the end*)                    
  | NEW typ=ty LBRACKET e=exp RBRACKET 
                        { loc $startpos $endpos @@ NewArr(typ, e) }  
  | NEW typ=ty LBRACKET RBRACKET LBRACE l=separated_list(COMMA, exp) RBRACE
                        { loc $startpos $endpos @@ CArr (typ, l) }                                                        
  

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

stmt:
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (e, es) }
  | ifs=if_stmt         { ifs }
  | FOR LPAREN vlist=separated_list(COMMA, vdecl) SEMI opt=exp SEMI s_opt=stmt RPAREN b=block
                        { loc $startpos $endpos @@ For (vlist, Some(opt), Some(s_opt), b) }
  | FOR LPAREN vlist=separated_list(COMMA, vdecl) SEMI SEMI s_opt=stmt RPAREN b=block
                        { loc $startpos $endpos @@ For (vlist, None, Some(s_opt), b) }
  | FOR LPAREN vlist=separated_list(COMMA, vdecl) SEMI opt=exp SEMI RPAREN b=block
                        { loc $startpos $endpos @@ For (vlist, Some(opt), None, b) } 
  | FOR LPAREN vlist=separated_list(COMMA, vdecl) SEMI SEMI RPAREN b=block
                        { loc $startpos $endpos @@ For (vlist, None, None, b) }                                                
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) } 

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
