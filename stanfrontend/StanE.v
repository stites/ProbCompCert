Require Import Globalenvs.
Require Import Events.
Require Import Integers.
Require Import Coqlib.
Require Import Floats.
Require Import AST.
Require Stan.
Require CStan.

Require Import Sops.
Require Import Cop.
Require Import Stypes.
  
Inductive expr :=
  (* Classical expressions that exist in C *)
  | Econst_int: int -> type -> expr
  | Econst_float: float -> type -> expr
  | Evar: ident -> type -> expr
  (* FIXME: add types to all proceeding as well? *)
  | Eunop: operator -> expr -> expr
  | Ebinop: expr -> operator -> expr -> expr
  | Ecall: ident -> list expr -> expr
  | Econdition: expr -> expr -> expr -> expr
  (* Classical expresions that differ from C *)
  | Earray: list expr -> expr
  | Erow: list expr -> expr
  | Eindexed: expr -> list index -> expr
  (* Probabilistic expressions *)
  | Edist: ident -> list expr -> expr
  | Etarget

with index :=
  | Iall
  | Isingle: expr -> index
  | Iupfrom: expr -> index
  | Idownfrom: expr -> index
  | Ibetween: expr -> expr -> index. 

Inductive basic :=
  | Bint
  | Breal
  | Bvector: expr -> basic
  | Brow: expr -> basic
  | Bmatrix: expr -> expr -> basic
  | Bstruct: ident -> basic.

Inductive printable := 
  | Pstring: ident -> printable 
  | Pexpr: expr -> printable.

Record variable := mkvariable {
  vd_type: basic;
  vd_constraint: Stan.constraint;
  vd_dims: list(expr);
  vd_init: option expr;
  vd_global: bool;
}.

Inductive statement :=
  (* Classical statements that exist in C *)
  | Sskip : statement
  | Sassign : expr -> option operator -> expr -> statement
  | Ssequence: statement -> statement -> statement
  | Sifthenelse: expr -> statement -> statement -> statement
  | Swhile: expr -> statement -> statement
  | Sfor: ident -> expr -> expr -> statement -> statement
  | Sbreak: statement
  | Scontinue: statement
  | Sreturn: option expr -> statement
  | Svar: variable -> statement
  | Scall: ident -> list expr -> statement
  | Sruntime: ident -> list printable -> statement
  (* Classical statements that differ C *)
  | Sforeach: ident -> expr -> statement -> statement
  (* Probabilistic statements *)
  | Starget: expr -> statement
  | Stilde: expr -> expr -> list expr -> (option expr * option expr) -> statement.


Record function := mkfunction {
  fn_return: option(type); 
  fn_params: list (autodifftype * type * ident);
  fn_body: statement;
  fn_blocktype: CStan.blocktype;
  fn_callconv: AST.calling_convention;
  fn_temps: list (ident * type);
  fn_vars: list (ident * type); 
}.

Definition fundef := Ctypes.fundef function.
  
Record program := mkprogram {
  pr_defs: list (ident * globdef fundef variable);
  pr_public: list ident;
  pr_model: ident;
  pr_parameters: ident;
  pr_parameters_vars: list ident;
  pr_parameters_struct: ident*ident;
  pr_transformed_parameters: ident;
  pr_data: ident;
  pr_data_vars: list ident;
  pr_data_struct: ident*ident;
  pr_transformed_data: ident;
  pr_generated: ident
}.

Definition program_of_program (p: program) : AST.program fundef variable :=
  {| AST.prog_defs := p.(pr_defs);
     AST.prog_public := p.(pr_public);
     AST.prog_main := xH |}.

Coercion program_of_program: program >-> AST.program.
