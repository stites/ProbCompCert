Require Import Globalenvs.
Require Import Events.
Require Import Integers.
Require Import Coqlib.
Require Import Floats.

Require Import Sops.
Require Import Stypes.

Definition ident := positive.
  
Inductive expr :=
  (* Classical expressions that exist in C *)
  | Econst_int: int -> expr
  | Econst_float: float -> expr
  | Evar: ident -> expr
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
  | Bmatrix: expr -> expr -> basic.

Inductive constraint :=
  | Cidentity
  | Clower: expr -> constraint
  | Cupper: expr -> constraint
  | Clower_upper: expr -> expr -> constraint
  | Coffset: expr -> constraint
  | Cmultiplier: expr -> constraint
  | Coffset_multiplier: expr -> expr -> constraint
  | Cordered
  | Cpositive_ordered
  | Csimplex
  | Cunit_vector
  | Ccholesky_corr
  | Ccholesky_cov
  | Ccorrelation
  | Ccovariance. 		       
		      			 
Record variable := mkvariable {
  vd_id: ident;
  vd_type: basic;
  vd_constraint: constraint;
  vd_dims: list(expr);
  vd_init: option expr;
  vd_global: bool
}.

Inductive printable := 
  | Pstring: ident -> printable 
  | Pexpr: expr -> printable.
  
Inductive statement :=
  (* Classical statements that exist in C *)
  | Sskip : statement
  | Sassign : expr -> option operator -> expr -> statement
  | Sblock: list statement -> statement
  | Sifthenelse: expr -> statement -> statement -> statement
  | Swhile: expr -> statement -> statement
  | Sfor: ident -> expr -> expr -> statement -> statement
  | Sbreak: statement
  | Scontinue: statement
  | Sreturn: option expr -> statement
  | Svar: variable -> statement
  | Scall: ident -> list expr -> statement
  | Sruntime: String.string -> list printable -> statement
  (* Classical statements that differ C *)
  | Sforeach: ident -> expr -> statement -> statement
  (* Probabilistic statements *)
  | Starget: expr -> statement
  | Stilde: expr -> ident -> list expr -> (option expr * option expr) -> statement.
		      
Record function := mkfunction { 
  fn_return: option(type); 
  fn_name: ident; 
  fn_params: list (autodifftype * type * ident);
  fn_body: statement 
}.

Record program := mkprogram {
  pr_functions: option (list function);
  pr_data: option (list variable);
  pr_transformed_data: option (list statement);
  pr_parameters: option (list variable);
  pr_transformed_parameters: option (list statement);
  pr_model: option (list statement);
  pr_generated: option (list statement)
}.
