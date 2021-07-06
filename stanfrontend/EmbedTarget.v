(** Embed the target ident into a function. *)
Require Import List.
Require Import Cop.
Require Import Ctypes.
Require Import CStan.
Require Import Errors.
Require Import String.
Require Import Floats.
Open Scope string_scope.
Require Import Coqlib.
Require Import Sops.
Require Import Cop.
Require Denumpyification.
Require Import Globalenvs.
Require Import Integers.
Require AST.
Require SimplExpr.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition tdouble := Tfloat F64 noattr.

Notation mon := SimplExpr.mon.
Notation ret := SimplExpr.ret.
Notation error := SimplExpr.error.
Notation localvar := (prod AST.ident Ctypes.type).

(* assuming that target is always symbol 0 to a model lets us remove this hack *)
Definition get_target_ident (vars: list localvar) : res AST.ident :=
  match vars with
  | nil => Error (msg "impossible: 0")
  | (t, ty)::nil => OK t (* model takes target, params struct as arguments *)
  (* | (t, ty)::(p, pty)::nil => OK t (* model takes target, params struct as arguments *) *)
  | _ => Error (msg "impossible: >2")
  end.

Fixpoint transf_target_expr (tgt: AST.ident) (e: CStan.expr) {struct e}: res CStan.expr :=
  match e with
  | CStan.Econst_int i t => OK (CStan.Econst_int i t)
  | CStan.Econst_float f t => OK (CStan.Econst_float f t)
  | CStan.Econst_single f t => OK (CStan.Econst_single f t)
  | CStan.Econst_long i t => OK (CStan.Econst_long i t)
  | CStan.Evar i t => OK (CStan.Evar i t)
  | CStan.Etempvar i t => OK (CStan.Etempvar i t)
  | CStan.Ederef e t =>
    do e <- transf_target_expr tgt e;
    OK (CStan.Ederef e t)
  | CStan.Eunop uop e t =>
    do e <- transf_target_expr tgt e;
    OK (CStan.Eunop uop e t)
  | CStan.Ebinop bop e0 e1 t =>
    do e0 <- transf_target_expr tgt e0;
    do e1 <- transf_target_expr tgt e1;
    OK (CStan.Ebinop bop e0 e1 t)
  | CStan.Esizeof t0 t1 => OK (CStan.Esizeof t0 t1)
  | CStan.Ealignof t0 t1 => OK (CStan.Ealignof t0 t1)
  | CStan.Etarget ty => OK (CStan.Evar tgt ty)
end.

Definition option_mmap {X Y:Type} (f: X -> res Y) (ox: option X) : res (option Y) :=
  match ox with
  | None => OK None
  | Some x => do x <- f x; OK (Some x)
  end.


Fixpoint transf_target_statement (tgt: AST.ident) (s: CStan.statement) {struct s}: res CStan.statement :=
match s with
  | Sassign e0 e1 =>
    do e0 <- transf_target_expr tgt e0;
    do e1 <- transf_target_expr tgt e1;
    OK (Sassign e0 e1)
  | Sset i e => do e <- transf_target_expr tgt e; OK (Sset i e)
  | Scall oi e le =>
    do e <- transf_target_expr tgt e;
    do le <- Errors.mmap (transf_target_expr tgt) le;
    OK (Scall oi e le)
  | Sbuiltin oi ef lt le => Error (msg "OK (Sbuiltin oi ef lt le)")
  | Ssequence s0 s1 =>
    do s0 <- transf_target_statement tgt s0;
    do s1 <- transf_target_statement tgt s1;
    OK (Ssequence s0 s1)
  | Sifthenelse e s0 s1 =>
    do e <- transf_target_expr tgt e;
    do s0 <- transf_target_statement tgt s0;
    do s1 <- transf_target_statement tgt s1;
    OK (Sifthenelse e s0 s1)
  | Sloop s0 s1 =>
    do s0 <- transf_target_statement tgt s0;
    do s1 <- transf_target_statement tgt s1;
    OK (Sloop s0 s1)
  | Sreturn oe =>
    do oe <- option_mmap (transf_target_expr tgt) oe;
    OK (Sreturn oe)
  | Starget e =>
    Error (msg "Starget DNE in this stage of pipeline")
  | Stilde e i le (oe0, oe1) =>
    Error (msg "Stilde DNE in this stage of pipeline")
  | Sbreak => OK Sbreak
  | Sskip => OK Sskip
  | Scontinue => OK Scontinue
end.


Definition transf_function (f: function): res function :=
  match f.(fn_blocktype) with
  | BTOther => OK f
  | BTModel =>
    do tgt <- get_target_ident f.(fn_params);
    let body := (Ssequence f.(fn_body)
          (Sreturn (Some (CStan.Etarget tdouble)))) in
    do body <- transf_target_statement tgt body;
    OK {|
      fn_params := f.(fn_params);
      fn_body := body;

      (*should not change*)
      fn_return := f.(fn_return);
      fn_temps := f.(fn_temps);
      fn_vars := f.(fn_vars);
      fn_callconv := f.(fn_callconv);
      fn_blocktype := f.(fn_blocktype);
    |}

  end.


(* ================================================================== *)
(*                    Switch to Error Monad                           *)
(* ================================================================== *)

Definition transf_external (ef: AST.external_function) : res AST.external_function :=
  match ef with
  | AST.EF_external n sig => OK (AST.EF_external n sig) (*link to blas ops?*)
  | AST.EF_runtime n sig => OK (AST.EF_runtime n sig) (*link runtime?*)
  | _ => OK ef
  end.

Definition transf_fundef (id: AST.ident) (fd: CStan.fundef) : res CStan.fundef :=
  match fd with
  | Internal f =>
      do tf <- transf_function f;
      OK (Internal tf)
  | External ef targs tres cc =>
      do ef <- transf_external ef;
      OK (External ef targs tres cc)
  end.

Definition transf_variable (id: AST.ident) (v: CStan.type): res CStan.type :=
  OK v.

Definition transf_program(p: CStan.program): res CStan.program :=
  do p1 <- AST.transform_partial_program2 transf_fundef transf_variable p;
  OK {|
      prog_defs := AST.prog_defs p1;
      prog_public := AST.prog_public p1;

      prog_data:=p.(prog_data);
      prog_data_vars:=p.(prog_data_vars);
      prog_transformed_data:=p.(prog_transformed_data);

      prog_parameters:= p.(prog_parameters);
      prog_parameters_vars:= p.(prog_parameters_vars);
      prog_transformed_parameters:=p.(prog_transformed_parameters);

      prog_generated_quantities:=p.(prog_generated_quantities);
      prog_model:=p.(prog_model);

      prog_comp_env:=p.(prog_comp_env);
    |}.
