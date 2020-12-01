(** The parser for Stan.
    A CoqMenhir file. *)

%{

Require Import List.
Import ListNotations.
Require Import Nat.

Require Import Stan.

(* Takes a sized_basic_type and a list of sizes and repeatedly applies then
   SArray constructor, taking sizes off the list *)
Definition reducearray (sbt:sizedtype) (l:list expression) : sizedtype :=
  List.fold_right (fun z y => SArray (y, z)) sbt l.

Fixpoint reparray (n:nat) (x:unsizedtype) : unsizedtype :=
  match n with
  | O => x
  | S n' => reparray n' (UArray x)
  end.

Definition omap {A:Type} {B:Type} (f:A->B) (x:option A): option B :=
  match x with
  | None => None
  | Some a => Some (f a)
  end.

%}
  

%token FUNCTIONBLOCK DATABLOCK TRANSFORMEDDATABLOCK PARAMETERSBLOCK
       TRANSFORMEDPARAMETERSBLOCK MODELBLOCK GENERATEDQUANTITIESBLOCK
%token LBRACE RBRACE LPAREN RPAREN LBRACK RBRACK LABRACK RABRACK COMMA SEMICOLON
       BAR
%token RETURN IF_ ELSE WHILE FOR IN BREAK CONTINUE
%token VOID INT REAL VECTOR ROWVECTOR MATRIX ORDERED POSITIVEORDERED SIMPLEX
       UNITVECTOR CHOLESKYFACTORCORR CHOLESKYFACTORCOV CORRMATRIX COVMATRIX
%token LOWER UPPER OFFSET MULTIPLIER
%token <string> INTNUMERAL
%token <string> REALNUMERAL
%token <string> STRINGLITERAL
%token <string> IDENTIFIER
%token TARGET
%token QMARK COLON BANG MINUS PLUS HAT ELTPOW TRANSPOSE TIMES DIVIDE MODULO IDIVIDE
       LDIVIDE ELTTIMES ELTDIVIDE OR AND EQUALS NEQUALS LEQ GEQ TILDE
%token ASSIGN PLUSASSIGN MINUSASSIGN TIMESASSIGN DIVIDEASSIGN
   ELTDIVIDEASSIGN ELTTIMESASSIGN
%token ARROWASSIGN INCREMENTLOGPROB GETLP (* all of these are deprecated *)
%token PRINT REJECT
%token TRUNCATE
%token EOF

(* type declarations for nonterminals *)

%type <expression> lhs expression or_expression and_expression equal_expression comparison_expression additive_expression multiplicative_expression leftdivide_expression prefix_expression exponentiation_expression postfix_expression common_expression basic_expression constr_expression index_expression
%type <list expression> dims
%type <list index> index indexes
%type <list printable> printable printables
%type <string> string_literal, identifier, decl_identifier
%type <assignmentoperator> assignment_op
%type <statement> statement atomic_statement open_statement closed_statement simple_statement top_vardecl_or_statement vardecl_or_statement var_decl top_var_decl
%type <vardecl> top_var_decl_no_assign
%type <list statement> transformed_data_block transformed_parameters_block model_block generated_quantities_block
%type <list vardecl> data_block parameters_block
%type <list fundecl> function_block
%type <truncation> truncation
%type <transformation> range offset_mult range_constraint type_constraint
%type <sizedtype * transformation> top_var_type
%type <sizedtype> sized_basic_type
%type <unsizedtype> basic_type unsized_type
%type <nat> unsized_dims (* questionable *)
%type <autodifftype * unsizedtype * string> arg_decl
%type <returntype> return_type
%type <fundecl> function_def

(* turns out you can apply %type to _fully applied_ parameterized things *) 
%type <option (list vardecl)> option(data_block) option(parameters_block) 
%type <option (list fundecl)> option(function_block)
%type <option (list statement)> option(transformed_data_block) option(transformed_parameters_block) option(model_block) option(generated_quantities_block)

%type <list expression> separated_nonempty_list(COMMA,expression) separated_list(COMMA,expression)
%type <list (autodifftype * unsizedtype * string) > separated_nonempty_list(COMMA,arg_decl) separated_list(COMMA,arg_decl)
%type <unit * expression> pair(COMMA,expression)  pair(ASSIGN,expression)
%type <option expression> option(expression)
%type <option (list expression)> option(dims)
%type <option (unit * expression)> option(pair(COMMA,expression)) option(pair(ASSIGN,expression))
%type <option truncation> option(truncation)
%type <list statement> list(vardecl_or_statement) list(top_vardecl_or_statement) 
%type <list vardecl> list(top_var_decl_no_assign)
%type <list fundecl> list(function_def)
%type <list unit> list(COMMA)
(* Grammar *)

(* Top level rule *)

%start <program> program
%%

(* copied from stdlib *)
option(X):
  | { None }
  | x = X { Some x }

list(X):
  | { [] }
  | x = X; xs = list(X) { x :: xs }

separated_list(separator, X):
 | {[]}
 | xs =separated_nonempty_list(separator, X) { xs }

separated_nonempty_list(separator, X):
  | x = X { [ x ] }
  | x = X; separator; xs = separated_nonempty_list(separator, X) { x :: xs }

 pair(X, Y):
  | x = X; y = Y { pair x y }

(* program *)
program:
  | ofb=option(function_block)
    odb=option(data_block)
    otdb=option(transformed_data_block)
    opb=option(parameters_block)
    otpb=option(transformed_parameters_block)
    omb=option(model_block)
    ogb=option(generated_quantities_block)
    EOF
    {
      {| functionblock := ofb
      ; datablock := odb
      ; transformeddatablock := otdb
      ; parametersblock := opb
      ; transformedparametersblock := otpb
      ; modelblock := omb
      ; generatedquantitiesblock := ogb |}
    }

function_block:
  | FUNCTIONBLOCK LBRACE fd=list(function_def) RBRACE {fd}

data_block:
  | DATABLOCK LBRACE tvd=list(top_var_decl_no_assign) RBRACE { tvd }

transformed_data_block:
  | TRANSFORMEDDATABLOCK LBRACE tvds=list(top_vardecl_or_statement) RBRACE { tvds }

parameters_block:
  | PARAMETERSBLOCK LBRACE tvd=list(top_var_decl_no_assign) RBRACE { tvd }

transformed_parameters_block:
  | TRANSFORMEDPARAMETERSBLOCK LBRACE tvds=list(top_vardecl_or_statement) RBRACE { tvds }

model_block:
  | MODELBLOCK LBRACE vds=list(vardecl_or_statement) RBRACE { vds  }

generated_quantities_block:
  | GENERATEDQUANTITIESBLOCK LBRACE tvds=list(top_vardecl_or_statement) RBRACE { tvds }

identifier:
  | id=IDENTIFIER { id }
  | TRUNCATE { literal_T }

decl_identifier:
  | id=identifier { id }

function_def:
  | rt=return_type name=decl_identifier LPAREN args=separated_list(COMMA, arg_decl) RPAREN b=statement
    { {| funreturntype := rt; funname := name; arguments := args; body := b |} }

return_type:
  | VOID { Void }
  | ut=unsized_type { ReturnType ut }

arg_decl:
  | ut=unsized_type id=decl_identifier { (AutoDiffable, ut, id) }
  | DATABLOCK ut=unsized_type id=decl_identifier { (DataOnly, ut, id) }

unsized_type:
  | bt=basic_type { reparray 0 bt    }
  | bt=basic_type d=unsized_dims { reparray (1+d) bt    }

basic_type:
  | INT { UInt }
  | REAL { UReal }
  | VECTOR { UVector }
  | ROWVECTOR { URowVector }
  | MATRIX { UMatrix }

unsized_dims:
  | LBRACK cs=list(COMMA) RBRACK { length cs }

(* declarations *)
var_decl:
  | sbt=sized_basic_type id=decl_identifier d=option(dims)
    ae=option(pair(ASSIGN, expression)) SEMICOLON
    { 
      let sizes := 
      (match d with None => [] | Some l => l end)
      in
      VarDecl {| decl_type := Sized (reducearray sbt sizes);
              decl_transform := Identity;
              decl_identifier := id;
              initial_value := omap snd ae;
              is_global := false |}
    }

sized_basic_type:
  | INT { SInt }
  | REAL { SReal }
  | VECTOR LBRACK e=expression RBRACK { SVector e }
  | ROWVECTOR LBRACK e=expression RBRACK { SRowVector e  }
  | MATRIX LBRACK e1=expression COMMA e2=expression RBRACK { SMatrix (e1, e2) }

top_var_decl_no_assign:
  | tvt=top_var_type id=decl_identifier d=option(dims) SEMICOLON
    {
      let sizes := 
      (match d with None => [] | Some l => l end)
      in
      {| decl_type := Sized (reducearray (fst tvt) sizes);
                  decl_transform :=  snd tvt;
                  decl_identifier := id;
                  initial_value := None;
                  is_global := true |}
    }

top_var_decl:
  | tvt=top_var_type id=decl_identifier d=option(dims)
    ass=option(pair(ASSIGN, expression)) SEMICOLON
    { 
      let sizes := 
      (match d with None => [] | Some l => l end) 
      in
      VarDecl {| decl_type := Sized (reducearray (fst tvt) sizes);
                    decl_transform := snd tvt;
                    decl_identifier := id;
                    initial_value := omap snd ass;
                    is_global := true |}
    }

top_var_type:
  | INT r=range_constraint { (SInt, r) }
  | REAL c=type_constraint { (SReal, c) }
  | VECTOR c=type_constraint LBRACK e=expression RBRACK { (SVector e, c) }
  | ROWVECTOR c=type_constraint LBRACK e=expression RBRACK { (SRowVector e, c) }
  | MATRIX c=type_constraint LBRACK e1=expression COMMA e2=expression RBRACK { (SMatrix (e1, e2), c) }
  | ORDERED LBRACK e=expression RBRACK { (SVector e, Ordered) }
  | POSITIVEORDERED LBRACK e=expression RBRACK { (SVector e, PositiveOrdered) }
  | SIMPLEX LBRACK e=expression RBRACK { (SVector e, Simplex) }
  | UNITVECTOR LBRACK e=expression RBRACK { (SVector e, UnitVector) }
  | CHOLESKYFACTORCORR LBRACK e=expression RBRACK { (SMatrix (e, e), CholeskyCorr) }
  | CHOLESKYFACTORCOV LBRACK e1=expression oe2=option(pair(COMMA, expression))
    RBRACK
    { 
      match oe2 with 
      | Some (_,e2) => ( SMatrix (e1, e2), CholeskyCov)
      | _           =>  (SMatrix (e1, e1),  CholeskyCov)
      end
    }
  | CORRMATRIX LBRACK e=expression RBRACK { (SMatrix (e, e), Correlation) }
  | COVMATRIX LBRACK e=expression RBRACK { (SMatrix (e, e), Covariance) }

type_constraint:
  | r=range_constraint { r }
  | LABRACK l=offset_mult RABRACK { l }

range_constraint:
  | { Identity }
  | LABRACK r=range RABRACK { r }

range:
  | LOWER ASSIGN e1=constr_expression COMMA UPPER ASSIGN e2=constr_expression
  | UPPER ASSIGN e2=constr_expression COMMA LOWER ASSIGN e1=constr_expression { LowerUpper (e1, e2) }
  | LOWER ASSIGN e=constr_expression { Lower e }
  | UPPER ASSIGN e=constr_expression { Upper e }

offset_mult:
  | OFFSET ASSIGN e1=constr_expression COMMA MULTIPLIER ASSIGN e2=constr_expression
  | MULTIPLIER ASSIGN e2=constr_expression COMMA OFFSET ASSIGN e1=constr_expression { OffsetMultiplier (e1, e2) }
  | OFFSET ASSIGN e=constr_expression { Offset e }
  | MULTIPLIER ASSIGN e=constr_expression { Multiplier e }

dims:
  | LBRACK l=separated_nonempty_list(COMMA, expression) RBRACK { l }

(* expressions *)
expression:
  | e1=or_expression  QMARK e2=expression COLON e3=expression { TernaryIf (e1, e2, e3) }
  | e=or_expression { e }

or_expression:
  | e1 = or_expression OR e2=and_expression { BinOp (e1, Or, e2) }
  | e = and_expression { e }

and_expression:
  | e1=and_expression AND e2=equal_expression { BinOp (e1, And, e2) }
  | e=equal_expression { e }

equal_expression:
  | e1=equal_expression EQUALS e2=comparison_expression { BinOp (e1, Equals, e2) }
  | e1=equal_expression NEQUALS e2=comparison_expression { BinOp (e1, NEquals, e2) }
  | e = comparison_expression { e }

comparison_expression:
  | e1=comparison_expression LABRACK e2=additive_expression { BinOp (e1, Less, e2) }
  | e1=comparison_expression LEQ e2=additive_expression { BinOp (e1, Leq, e2) }  
  | e1=comparison_expression RABRACK e2=additive_expression { BinOp (e1, Greater, e2) }    
  | e1=comparison_expression GEQ e2=additive_expression { BinOp (e1, Geq, e2) }
  | e=additive_expression { e }

additive_expression:
  | e1=additive_expression PLUS e2=multiplicative_expression { BinOp (e1, Plus, e2) }
  | e1=additive_expression MINUS e2=multiplicative_expression { BinOp (e1, Minus, e2) }
  | e=multiplicative_expression { e }

multiplicative_expression:
  | e1=multiplicative_expression TIMES e2=leftdivide_expression { BinOp (e1, Times, e2) }
  | e1=multiplicative_expression DIVIDE e2=leftdivide_expression { BinOp (e1, Divide, e2) }  
  | e1=multiplicative_expression IDIVIDE e2=leftdivide_expression { BinOp (e1, IntDivide, e2) }
  | e1=multiplicative_expression MODULO e2=leftdivide_expression { BinOp (e1, Modulo, e2) }  
  | e1=multiplicative_expression ELTTIMES e2=leftdivide_expression { BinOp (e1, EltTimes, e2) }
  | e1=multiplicative_expression ELTDIVIDE e2=leftdivide_expression { BinOp (e1, EltDivide, e2) }
  | e=leftdivide_expression { e }

leftdivide_expression:
  | e1=leftdivide_expression LDIVIDE e2=prefix_expression { BinOp (e1, LDivide, e2) }
  | e=prefix_expression { e }

prefix_expression:
  | BANG e=exponentiation_expression { PrefixOp (PNot, e) }
  | MINUS e=exponentiation_expression { PrefixOp (PMinus, e) }
  | PLUS e=exponentiation_expression { PrefixOp (PPlus, e) }
  | e=exponentiation_expression { e }

exponentiation_expression:
  | e1=postfix_expression HAT e2=exponentiation_expression { BinOp (e1, Pow, e2) }
  | e1=postfix_expression ELTPOW e2=exponentiation_expression { BinOp (e1, EltPow, e2) }
  | e=postfix_expression { e }

postfix_expression: 
  | e=postfix_expression TRANSPOSE { PostfixOp (e, Transpose) }
  | e = index_expression { e }
  | e=common_expression { e }

index_expression:
  | e=basic_expression LBRACK indices=indexes RBRACK { Indexed (e, indices) }

common_expression:
  | e=basic_expression { e}
  | l=lhs { l}

basic_expression:
  | i=INTNUMERAL { IntNumeral i }
  | r=REALNUMERAL { RealNumeral r }
  | LBRACE xs=separated_nonempty_list(COMMA, expression) RBRACE { ArrayExpr xs }
  | LBRACK xs=separated_list(COMMA, expression) RBRACK { RowVectorExpr xs }
  | id=identifier LPAREN e=expression BAR args=separated_list(COMMA, expression) RPAREN { CondDistApp (id, e :: args) }
  | id=identifier LPAREN args=separated_list(COMMA, expression) RPAREN
    {  
       if andb ( eqb (List.length args) 1  )
               ( is_suffix literal_lpdf id
                || is_suffix literal_lpmf id )
       then 
       CondDistApp (id, args)
       else 
       FunApp (id, args) 
    }
  | TARGET LPAREN RPAREN { GetTarget }
  | GETLP LPAREN RPAREN { GetLP } (* deprecated *)
  | LPAREN e=expression RPAREN { e }

constr_expression:
  | e=additive_expression { e }

indexes:
  | i = index {  i }
  | i1=index COMMA i2=indexes { List.app i1 i2 }

index:
  | { [All] }
  | COLON { [All] }
  | e=expression { [Single e] }
  | e=expression COLON { [Upfrom e] }
  | COLON e=expression { [Downfrom e] }
  | e1=expression COLON e2=expression { [Between (e1, e2)] }


printables:
  | p = printable { p }
  | p1=printable COMMA p2=printables { List.app p1 p2 }

printable:
  | e=expression { [PExpr e] }
  | s=string_literal { [PString s] }

(* L-values *)
lhs:
  | id=identifier { Var id }
  | l=lhs LBRACK indices=indexes RBRACK { Indexed (l, indices) }

(* statements *)
statement:
  | s=closed_statement { s }
  | s=open_statement { s }

atomic_statement:
  | l=lhs op=assignment_op e=expression SEMICOLON
    { Assignment {| assign_lhs := l;
                   assign_op := op;
                   assign_rhs := e |} 
    }
  | id=identifier LPAREN args=separated_list(COMMA, expression) RPAREN SEMICOLON { NRFunApp (id, args)  }
  | INCREMENTLOGPROB LPAREN e=expression RPAREN SEMICOLON { IncrementLogProb e } (* deprecated *)
  | e=expression TILDE id=identifier LPAREN es=separated_list(COMMA, expression)
    RPAREN ot=option(truncation) SEMICOLON
    {  
       let t := 
       (match ot with | Some tt_ => tt_ | None => NoTruncate end)
       in
       Tilde {| tilde_arg := e; tilde_distribution := id; tilde_args := es; tilde_truncation := t |}
    }
  | TARGET PLUSASSIGN e=expression SEMICOLON { TargetPE e }
  | BREAK SEMICOLON { Break }
  | CONTINUE SEMICOLON { Continue }
  | PRINT LPAREN l=printables RPAREN SEMICOLON { PrintStmt l }
  | REJECT LPAREN l=printables RPAREN SEMICOLON { Reject l  }
  | RETURN e=expression SEMICOLON { Return e }
  | RETURN SEMICOLON { ReturnVoid }
  | SEMICOLON { Skip }

assignment_op:
  | ASSIGN { Assign }
  | ARROWASSIGN { ArrowAssign  } (* deprecated *)
  | PLUSASSIGN { OperatorAssign Plus }
  | MINUSASSIGN { OperatorAssign Minus }
  | TIMESASSIGN { OperatorAssign Times }
  | DIVIDEASSIGN { OperatorAssign Divide }
  | ELTTIMESASSIGN { OperatorAssign EltTimes }
  | ELTDIVIDEASSIGN { OperatorAssign EltDivide  }

string_literal:
  | s=STRINGLITERAL { s }

truncation:
  | TRUNCATE LBRACK e1=option(expression) COMMA e2=option(expression)
    RBRACK
    {  
       match e1, e2 with
       | Some tt1, Some tt2 => TruncateBetween (tt1, tt2)
       | Some tt1, None => TruncateUpFrom tt1
       | None, Some tt2 => TruncateDownFrom tt2
       | None, None => NoTruncate  
       end
    }

open_statement:
  | IF_ LPAREN e=expression RPAREN s=simple_statement { IfThenElse(e, s, None)}
  | IF_ LPAREN e=expression RPAREN s=open_statement { IfThenElse (e, s, None) }
  | IF_ LPAREN e=expression RPAREN s1=closed_statement ELSE s2=open_statement { IfThenElse (e, s1, Some s2) }
  | WHILE LPAREN e=expression RPAREN s=open_statement { While (e, s) }
  | FOR LPAREN id=identifier IN e1=expression COLON e2=expression RPAREN
    s=open_statement
    {
      For {| loop_variable := id;
             lower_bound := e1;
             upper_bound := e2 |} 
          s
    }
  | FOR LPAREN id=identifier IN e=expression RPAREN s=open_statement { ForEach (id, e, s) }

closed_statement:
  | IF_ LPAREN e=expression RPAREN s1=closed_statement ELSE s2=closed_statement { IfThenElse (e, s1, Some s2) }
  | WHILE LPAREN e=expression RPAREN s=closed_statement { While (e, s) }
  | s=simple_statement { s }
  | FOR LPAREN id=identifier IN e1=expression COLON e2=expression RPAREN
    s=closed_statement
    {
      For {| loop_variable := id;
             lower_bound := e1;
             upper_bound := e2; |}
          s
    }
  | FOR LPAREN id=identifier IN e=expression RPAREN s=closed_statement { ForEach (id, e, s) }


simple_statement:
  | LBRACE l=list(vardecl_or_statement)  RBRACE { Block l } 
  | s=atomic_statement { s }

(* statement or var decls *)
vardecl_or_statement:
  | s=statement { s }
  | v=var_decl { v }

top_vardecl_or_statement:
  | s=statement { s }
  | v=top_var_decl { v }
