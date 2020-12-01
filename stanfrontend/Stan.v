Require Import Globalenvs.
Require Import Events.
Require Import Integers.

Parameter string : Type.

Parameter literal_T : string.
Parameter literal_lpdf : string (* "_lpdf" *).
Parameter literal_lpmf : string (* "_lpmf" *).

Parameter is_suffix: string -> string -> bool.

Definition identifier := string.

Inductive operator :=
  | Plus
  | Vector_Plus
  | PPlus
  | Minus
  | PMinus
  | Times
  | Divide
  | IntDivide
  | Modulo
  | LDivide
  | EltTimes
  | EltDivide
  | Pow
  | EltPow
  | Or
  | And
  | Equals
  | NEquals
  | Less
  | Leq
  | Greater
  | Geq
  | PNot
  | Transpose.

Inductive expr :=
  (* Classical expressions that exist in C *)
  | Econst_int: string -> expr
  | Econst_float: string -> expr
  | Evar: identifier -> expr
  | Eunop_prefix: operator -> expr -> expr
  | Eunop_postfix: expr -> operator -> expr
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
  | Ibetween: expr * expr -> index. 

Inductive transformation :=
  | Tidentity
  | Tlower: expr -> transformation
  | Tppper: expr -> transformation
  | Tlower_upper: expr * expr -> transformation
  | Toffset: expr -> transformation
  | Tmultiplier: expr -> transformation
  | Toffset_multiplier: expr * expr -> transformation
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

Inductive unsizedtype :=
  | Uint
  | Ureal
  | Uvector
  | Urow_vector
  | Umatrix
  | Uarray: unsizedtype -> unsizedtype
  | Ufun: (list (autodifftype * unsizedtype)) -> returntype -> unsizedtype
  | Umath_library_function

with autodifftype := 
  | Adata_only 
  | Aauto_diffable

with returntype := 
  | Rvoid 
  | Rtype: unsizedtype -> returntype.

Inductive type := 
  | Tsized: sizedtype -> type 
  | Tunsized: unsizedtype -> type.

Inductive assignmentoperator :=
  | Asimple
  | Aoperator: operator -> assignmentoperator.

Inductive truncation :=
  | Tnone
  | Tup_from: expr -> truncation
  | Tdown_fom: expr -> truncation
  | Tbetween: expr -> expr -> truncation.

Inductive printable := 
  | Pstring: string -> printable 
  | Pexpr: expr -> printable.

Record variable := mkvariable {
  vd_transform: transformation;
  vd_type: type;
  vd_id: identifier;
  vd_init: option expr;
  vd_global: bool
}.

Inductive statement :=
  (* Classical statements that exist in C *)
  | Sskip : statement
  | Sassign : expr -> assignmentoperator -> expr -> statement
  | Sblock: list statement -> statement
  | Sifthenelse: expr -> statement -> option statement -> statement
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
  | Stilde: expr -> identifier -> list expr -> truncation -> statement.

Record function := mkfunction { 
  fn_return: returntype; 
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

Require Import Smallstep.

Parameter semantics: program -> semantics.
