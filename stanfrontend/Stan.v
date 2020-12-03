Require Import Globalenvs.
Require Import Events.
Require Import Integers.

Require Import Sops.
Require Import Stypes.

Parameter string : Type.

Parameter literal_T : string.
Parameter literal_lpdf : string (* "_lpdf" *).
Parameter literal_lpmf : string (* "_lpmf" *).

Parameter is_suffix: string -> string -> bool.

Definition identifier := string.

Inductive expr :=
  (* Classical expressions that exist in C *)
  | Econst_int: string -> expr
  | Econst_float: string -> expr
  | Evar: identifier -> expr
  | Eunop: operator -> expr -> expr
  | Ebinop: expr -> operator -> expr -> expr
  | Ecall: identifier -> list expr -> expr
  | Econdition: expr -> expr -> expr -> expr
  (* Classical expresions that differ from C *)
  | Earray: list expr -> expr
  | Erow: list expr -> expr
  | Eindexed: expr -> list index -> expr
  (* Probabilistic expressions *)
  | Edist: identifier -> list expr -> expr
  | Etarget

with index :=
  | Iall
  | Isingle: expr -> index
  | Iupfrom: expr -> index
  | Idownfrom: expr -> index
  | Ibetween: expr -> expr -> index. 


(* experiment with types *)
	
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

Record type := mktype {
  type_basic: basic;
  type_constraint: constraint;
   type_dims: list(int);
}.		       
			 
(* end of experiments with types *)
		 
Inductive transformation :=
  | Tidentity
  | Tlower: expr -> transformation
  | Tupper: expr -> transformation
  | Tlower_upper: expr -> expr -> transformation
  | Toffset: expr -> transformation
  | Tmultiplier: expr -> transformation
  | Toffset_multiplier: expr -> expr -> transformation
  | Tordered
  | Tpositive_ordered
  | Tsimplex
  | Tunit_vector
  | Tcholesky_corr
  | Tcholesky_cov
  | Tcorrelation
  | Tcovariance.

Inductive sizedtype :=
  | Sint
  | Sreal
  | Svector: expr -> sizedtype
  | Srow_vector: expr -> sizedtype
  | Smatrix: expr -> expr -> sizedtype
  | Sarray: sizedtype -> expr -> sizedtype.
			 
Inductive printable := 
  | Pstring: string -> printable 
  | Pexpr: expr -> printable.

Record variable := mkvariable {
  vd_transform: transformation;
  vd_type: sizedtype;
  vd_id: identifier;
  vd_init: option expr;
  vd_global: bool
}.

Inductive statement :=
  (* Classical statements that exist in C *)
  | Sskip : statement
  | Sassign : expr -> option operator -> expr -> statement
  | Sblock: list statement -> statement
  | Sifthenelse: expr -> statement -> statement -> statement
  | Swhile: expr -> statement -> statement
  | Sfor: identifier -> expr -> expr -> statement -> statement
  | Sbreak: statement
  | Scontinue: statement
  | Sreturn: option expr -> statement
  | Svar: variable -> statement
  | Scall: identifier -> list expr -> statement
  (* Classical statements that differ C *)
  | Sprint: list printable -> statement
  | Sreject: list printable -> statement
  | Sforeach: identifier -> expr -> statement -> statement
  (* Probabilistic statements *)
  | Starget: expr -> statement
  | Stilde: expr -> identifier -> list expr -> (option expr * option expr) -> statement.
		      
Record function := mkfunction { 
  fn_return: option(unsizedtype); 
  fn_name: identifier; 
  fn_params: list (autodifftype * unsizedtype * identifier);
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
