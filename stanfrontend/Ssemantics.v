Require Import StanE.
Require Import Smallstep.
Require Import Globalenvs.
Require Import Events.
Require Import Integers.
Require Import Maps.
Require Import Floats.
Require Import Values. 

  (*
Record env := mkenv {
  e_functions: PTree.t function;
  e_data: PTree.t variable;
  e_parameters: PTree.t variable;		     
}.
  
Definition temp := PTree.t val.
  
Inductive state: Type :=
  | State
      (s: list statement)
      (le: temp): state
  | Returnstate
      (res: val): state.
  
Definition globalenv (p: program): env :=
  mkenv (PTree.empty function) (PTree.empty variable) (PTree.empty variable).

Section Expr.

Variable e: env. 
Variable t: temp.
Variable target: float. 

Inductive eval_expr: expr -> val -> Prop :=
  | eval_binop: 
    forall e1 e2 op v1 v2,
    eval_expr e1 v1 -> eval_expr e2 v2 -> eval_expr (Ebinop e1 op e2) v1.



Parameter eval_lvalue: env -> temp_env -> expr -> ident -> list int -> Prop

Inductive stepp: env -> list statement -> temp -> list statement -> temp -> Prop :=

  | step_assign: forall f a1 a2 k e le m loc ofs v2 v m',
      eval_lvalue e le m a1 i idx ->
      eval_expr e le a2 v2 ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      code = (Sassign lhs op rhs) :: cont ->
      step e code le cont le'.
  
Parameter step: env -> state -> trace -> state -> Prop.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall model_code tr_params_code tr_data_code t,
      let ge := globalenv p in
      let le := PTree.empty val in
      p.(pr_transformed_data) = Some tr_data_code ->
      p.(pr_transformed_parameters) = Some tr_params_code ->
      p.(pr_model) = Some model_code ->	
      star step ge (State tr_data_code ge le) t (State nil ge le) ->	      
      initial_state p (State (tr_params_code ++ model_code) ge le).
						      
Parameter final_state: state -> int -> Prop.

Parameter st: Senv.t.
  
Definition semantics (p: program) :=
  let ge := globalenv p in
  Semantics_gen step (initial_state p) final_state ge st.
*)

Parameter semantics: program -> semantics.
