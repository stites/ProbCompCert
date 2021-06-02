Require Import List.
Require Import Ctypes.
Require Import CStan.
Require Import Errors.
Require Import String.
Open Scope string_scope.
Require Import Coqlib.
Require Import Sops.
Require Import Cop.
Require Denumpyification.
Require Import Globalenvs.
Require AST.

(* FIXME how do I share this notation? *)
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.


(* To avoid having to deal with constraints every parameter in a Stan model is
transformed to an unconstrained variable.

Constraint types:
+ Scalars, scalars in vectors, row vectors, matrices: lower and/or upper bounds.
+ Vectors, additionally: ordered, positive ordered, or simplexes.
+ Matrices, additionally: constrained as correlation or covariance matrices.

<quote>
Stan converts models to C++ classes which define probability functions with
support on all of R^K, where K is the number of unconstrained parameters needed
to define the constrained parameters defined in the program. The C++ classes
also include code to transform the parameters from unconstrained to constrained
and apply the appropriate Jacobians.
</quote> *)

Inductive Constraint :=
  | ChangeOfVariables : CStan.expr (* new support? *) -> Constraint
  | LowerBound : CStan.expr (* double *) -> Constraint
  | UpperBound : CStan.expr (* double *) -> Constraint
  | LowerAndUpperBound : CStan.expr (* lower double *) -> CStan.expr (* upper double *) -> Constraint
  | AffineTransformScalar : option CStan.expr (* mu ? 0 *) -> option CStan.expr (* sigma ? 1 *) -> Constraint
  | OrderedVector : Constraint
  | UnitSimplex : Constraint
  | UnitVector : Constraint
  | CorrelationMatrix : Constraint
  | CovarianceMatrix : Constraint
  | CholeskyFactorsOfCovariance : Constraint
  | CholeskyFactorsOfCorrelation : Constraint
  .

Fixpoint transf_expr (e: CStan.expr) {struct e}: res CStan.expr :=
  match e with
  | CStan.Econst_int i t => OK (CStan.Econst_int i t)
  | CStan.Econst_float f t => OK (CStan.Econst_float f t)
  | CStan.Econst_single f t => OK (CStan.Econst_single f t)
  | CStan.Econst_long i t => OK (CStan.Econst_long i t)
  | CStan.Evar i t => OK (CStan.Evar i t)
  | CStan.Etempvar i t => OK (CStan.Etempvar i t)
  | CStan.Ederef e t => OK (CStan.Ederef e t)
  | CStan.Eunop uop e t => OK (CStan.Eunop uop e t)
  | CStan.Ebinop bop e0 e1 t => OK (CStan.Ebinop bop e0 e1 t)
  | CStan.Esizeof t0 t1 => OK (CStan.Esizeof t0 t1)
  | CStan.Ealignof t0 t1 => OK (CStan.Ealignof t0 t1)
  | CStan.Etarget t => OK (CStan.Etarget t)
end.

Fixpoint transf_statement (s: CStan.statement) {struct s}: res CStan.statement :=
match s with
  | Sskip => OK Sskip
  | Sassign e0 e1 => OK (Sassign e0 e1)
  | Sset i e =>  OK (Sset i e)
  | Scall oi e le =>  OK (Scall oi e le)
  | Sbuiltin oi ef lt le =>  OK (Sbuiltin oi ef lt le)
  | Ssequence s0 s1 =>  OK (Ssequence s0 s1)
  | Sifthenelse e s0 s1 =>  OK (Sifthenelse e s0 s1)
  | Sloop s0 s1 =>  OK (Sloop s0 s1)
  | Sbreak =>  OK (Sbreak)
  | Scontinue =>  OK (Scontinue)
  | Sreturn oe =>   OK (Sreturn oe)
  | Starget e =>  OK (Starget e)
  | Stilde e i le (oe0, oe1) => OK (Stilde e i le (oe0, oe1))
end.

Notation localvar := (prod AST.ident Ctypes.type).

Definition transf_params (ps: list localvar) (body : statement): res (list localvar) :=
  OK ps.

Definition transf_temps (ts: list localvar) (params: list localvar) (body : statement): res (list localvar) :=
  OK ts.
Definition transf_vars (vs: list localvar) (temps: list localvar) (params: list localvar) (body : statement): res (list localvar) :=
  OK vs.

Definition transf_function (f: function): res function :=
  do body <- transf_statement f.(fn_body);
  do params <- transf_params f.(fn_params) body;
  do temps <- transf_temps f.(fn_temps) params body;
  do vars <- transf_vars f.(fn_vars) temps params body;
  OK {|
      fn_params := params;
      fn_body := body;
      fn_temps := temps;
      fn_vars := vars;

      (*should not change*)
      fn_return := Tvoid;
      fn_callconv := f.(fn_callconv);
     |}.

Definition transf_external (ef: AST.external_function) : res AST.external_function :=
  match ef with
  | AST.EF_external n sig => OK (AST.EF_external n sig) (*link to blas ops?*)
  | AST.EF_runtime n sig => OK (AST.EF_runtime n sig) (*link runtime?*)
  | _ => OK ef
  end.

Definition transf_fundef (id: AST.ident) (fd: CStan.fundef) : res CStan.fundef :=
  match fd with
  | Internal f =>
      do tf <- transf_function f; OK (Internal tf)
  | External ef targs tres cc =>
      do ef <- transf_external ef;
      OK (External ef targs tres cc)
  end.


Definition transf_variable (id: AST.ident) (v: CStan.type): res CStan.type :=
  OK v.

Definition transf_prog_data (p0: AST.program fundef type) (p1: CStan.program) (d: AST.ident): res AST.ident :=
  OK d.

Definition transf_prog_transformed_data (p0: AST.program fundef type) (p1: CStan.program) (d: AST.ident) (td: AST.ident): res AST.ident :=
  OK td.

Definition transf_prog_parameters (p0: AST.program fundef type) (p1: CStan.program) (p: AST.ident): res AST.ident :=
  OK p.

Definition transf_prog_transformed_parameters (p0: AST.program fundef type) (p1: CStan.program) (p: AST.ident) (tp: AST.ident): res AST.ident :=
  OK tp.

Definition transf_prog_generated_quantities (p0: AST.program fundef type) (p1: CStan.program) (tp: AST.ident) (gq: AST.ident): res AST.ident :=
  OK gq.

Definition transf_prog_model (p0: AST.program fundef type) (p1: CStan.program) (tp: AST.ident) (m: AST.ident): res AST.ident :=
  OK m.

Definition transf_program(p: CStan.program): res CStan.program :=
  (* do several layers of transformations? TODO: review NSF grant. *)
  do p3 <- AST.transform_partial_program2 transf_fundef transf_variable p;

  (* FIXME: I think I need to traverse the ptree (composite_env) and pass a list of refs to all of these. *)
  do data                   <- transf_prog_data p3 p p.(prog_data);
  do transformed_data       <- transf_prog_transformed_data p3 p data p.(prog_transformed_data);
  (* validate each transformation: can happen in ^^^ *)

  do parameters             <- transf_prog_parameters p3 p p.(prog_parameters);
  do transformed_parameters <- transf_prog_transformed_parameters p3 p parameters p.(prog_transformed_parameters);

  do generated_quantities   <- transf_prog_generated_quantities p3 p transformed_parameters p.(prog_generated_quantities);
  do model                  <- transf_prog_model p3 p transformed_parameters p.(prog_model);

  OK {|
      prog_defs := AST.prog_defs p3;
      prog_public := AST.prog_public p3;

      prog_data:=data;
      prog_transformed_data:=transformed_data;

      prog_parameters:= parameters;
      prog_transformed_parameters:=transformed_parameters;

      prog_generated_quantities:=p.(prog_generated_quantities);
      prog_model:=model;

      prog_comp_env:=p.(prog_comp_env);
    |}.
