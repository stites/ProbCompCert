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

(* FIXME how do I share this notation? *)
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Notation "'do' X <~ A ; B" := (SimplExpr.bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition tdouble := Tfloat F64 noattr.
Definition float_one := Floats.Float.of_int Int.one.

Notation mon := SimplExpr.mon.
Notation ret := SimplExpr.ret.
Notation error := SimplExpr.error.
Notation gensym := SimplExpr.gensym.

Fixpoint transf_expr (e: CStan.expr) {struct e}: mon CStan.expr :=
  match e with
  | CStan.Econst_int i t => ret (CStan.Econst_int i t)
  | CStan.Econst_float f t => ret (CStan.Econst_float f t)
  | CStan.Econst_single f t => ret (CStan.Econst_single f t)
  | CStan.Econst_long i t => ret (CStan.Econst_long i t)
  | CStan.Evar i t => ret (CStan.Evar i t)
  | CStan.Etempvar i t => ret (CStan.Etempvar i t)
  | CStan.Ederef e t => ret (CStan.Ederef e t)
  | CStan.Eunop uop e t => ret (CStan.Eunop uop e t)
  | CStan.Ebinop bop e0 e1 t => ret (CStan.Ebinop bop e0 e1 t)
  | CStan.Esizeof t0 t1 => ret (CStan.Esizeof t0 t1)
  | CStan.Ealignof t0 t1 => ret (CStan.Ealignof t0 t1)
  | CStan.Etarget t => ret (CStan.Etarget t)
end.
Notation error_mmap := Errors.mmap.

Fixpoint mon_mmap {A B : Type} (f: A -> mon B) (l: list A) {struct l} : mon (list B) :=
  match l with
  | nil => ret nil
  | hd :: tl =>
    do hd' <~ f hd;
    do tl' <~ mon_mmap f tl;
    ret (hd' :: tl')
  end.

Definition option_mon_mmap {X Y:Type} (f: X -> mon Y) (ox: option X) : mon (option Y) :=
  match ox with
  | None => ret None
  | Some x => do x <~ f x; ret (Some x)
  end.

Fixpoint maybe_ident (e: expr): option AST.ident :=
match e with
  | CStan.Evar i t => Some i
  | CStan.Etempvar i t => Some i
  | _ => None
end.

Fixpoint transf_statement (s: CStan.statement) {struct s}: mon CStan.statement :=
match s with
  | Sskip => ret Sskip
  | Sassign e0 e1 =>
    do e0 <~ transf_expr e0;
    do e1 <~ transf_expr e1;
    match maybe_ident e0 with
      | Some i => ret (Sset i e1)
      | None => ret (Sassign e0 e1)
    end
  | Sset i e =>
    do e <~ transf_expr e;
    ret (Sset i e)

  | Scall oi e le =>
    do e <~ transf_expr e;
    do le <~ mon_mmap transf_expr le;
    ret (Scall oi e le)

  | Sbuiltin oi ef lt le => error (msg "ret (Sbuiltin oi ef lt le)")

  | Ssequence s0 s1 =>
    do s0 <~ transf_statement s0;
    do s1 <~ transf_statement s1;
    ret (Ssequence s0 s1)

  | Sifthenelse e s0 s1 =>
    do s0 <~ transf_statement s0;
    do s1 <~ transf_statement s1;
    ret (Sifthenelse e s0 s1)

  | Sloop s0 s1 =>
    do s0 <~ transf_statement s0;
    do s1 <~ transf_statement s1;
    ret (Sloop s0 s1)

  | Sbreak => ret Sbreak

  | Scontinue => ret Scontinue

  | Sreturn oe =>
    do oe <~ option_mon_mmap (transf_expr) oe;
    ret (Sreturn oe)

  | Starget e =>
    do e <~ transf_expr e;
    ret (Sassign (Etarget tdouble)
              (Ebinop Cop.Oadd
                      (Etarget tdouble) e tdouble))

  | Stilde e i le (oe0, oe1) =>
    (* do tmp <~ gensym tdouble; *)
    (* simulate function call: *)
    (**)
    (* let etmp := (Etempvar tmp tdouble) in *)
    (* ret (Ssequence *)
    (*       (Scall (Some tmp) (Evar i tfunction :: fundef -> Ctypes.type) el) *)
    (*       (Starget etmp)) *)

    (* (* instead we just assign it 1 *) *)
    (* ret (Ssequence *)
    (*   (Sassign (Evar tmp tdouble) (Econst_float float_one tdouble)) *)
    (*   (Starget (Etempvar tmp tdouble))) *)

    ret (Starget (Econst_float float_one tdouble))
end.

Notation localvar := (prod AST.ident Ctypes.type).

Definition get_target_ident (vars: list localvar) : mon AST.ident :=
  match vars with
  | nil => error (msg "impossible: 0")
  | (t, ty)::nil => ret t
  | _ => error (msg "impossible: >1")
  end.

Fixpoint transf_target_expr (tgt: AST.ident) (e: CStan.expr) {struct e}: mon CStan.expr :=
  match e with
  | CStan.Econst_int i t => ret (CStan.Econst_int i t)
  | CStan.Econst_float f t => ret (CStan.Econst_float f t)
  | CStan.Econst_single f t => ret (CStan.Econst_single f t)
  | CStan.Econst_long i t => ret (CStan.Econst_long i t)
  | CStan.Evar i t => ret (CStan.Evar i t)
  | CStan.Etempvar i t => ret (CStan.Etempvar i t)
  | CStan.Ederef e t =>
    do e <~ transf_target_expr tgt e;
    ret (CStan.Ederef e t)
  | CStan.Eunop uop e t =>
    do e <~ transf_target_expr tgt e;
    ret (CStan.Eunop uop e t)
  | CStan.Ebinop bop e0 e1 t =>
    do e0 <~ transf_target_expr tgt e0;
    do e1 <~ transf_target_expr tgt e1;
    ret (CStan.Ebinop bop e0 e1 t)
  | CStan.Esizeof t0 t1 => ret (CStan.Esizeof t0 t1)
  | CStan.Ealignof t0 t1 => ret (CStan.Ealignof t0 t1)
  | CStan.Etarget ty => ret (CStan.Evar tgt ty)
end.

Fixpoint transf_target_statement (tgt: AST.ident) (s: CStan.statement) {struct s}: mon CStan.statement :=
match s with
  | Sassign e0 e1 =>
    do e0 <~ transf_target_expr tgt e0;
    do e1 <~ transf_target_expr tgt e1;
    ret (Sassign e0 e1)
  | Sset i e => do e <~ transf_target_expr tgt e; ret (Sset i e)
  | Scall oi e le =>
    do e <~ transf_target_expr tgt e;
    do le <~ mon_mmap (transf_target_expr tgt) le;
    ret (Scall oi e le)
  | Sbuiltin oi ef lt le => error (msg "ret (Sbuiltin oi ef lt le)")
  | Ssequence s0 s1 =>
    do s0 <~ transf_target_statement tgt s0;
    do s1 <~ transf_target_statement tgt s1;
    ret (Ssequence s0 s1)
  | Sifthenelse e s0 s1 =>
    do e <~ transf_target_expr tgt e;
    do s0 <~ transf_target_statement tgt s0;
    do s1 <~ transf_target_statement tgt s1;
    ret (Sifthenelse e s0 s1)
  | Sloop s0 s1 =>
    do s0 <~ transf_target_statement tgt s0;
    do s1 <~ transf_target_statement tgt s1;
    ret (Sloop s0 s1)
  | Sreturn oe =>
    do oe <~ option_mon_mmap (transf_target_expr tgt) oe;
    ret (Sreturn oe)
  | Starget e =>
    error (msg "Starget DNE in this stage of pipeline")
  | Stilde e i le (oe0, oe1) =>
    error (msg "Stilde DNE in this stage of pipeline")

  | Sbreak => ret Sbreak
  | Sskip => ret Sskip
  | Scontinue => ret Scontinue
end.

Definition transf_model (f: function) (body : statement): mon statement :=
  match f.(fn_blocktype) with
  | BTOther => ret body
  | BTModel =>
    do tgt <~ get_target_ident f.(fn_vars);
    let body :=
      (Ssequence (Sassign (CStan.Etarget tdouble) (Econst_float (Float.of_bits (Integers.Int64.repr 0)) tdouble))
        (Ssequence body
          (Sreturn (Some (CStan.Etarget tdouble))))) in
    transf_target_statement tgt body
  end.

Definition transf_statement_pipeline (f: function) : mon CStan.statement :=
  do body <~ transf_statement f.(fn_body); (* Stilde -> Starget; Error "Backend: tilde" *)
  do body <~ transf_statement body;        (* apply Starget transform *)
  do body <~ transf_model f body;
  ret body.

Definition transf_function (f: function): res function :=
  match transf_statement_pipeline f (SimplExpr.initial_generator tt) with
  | SimplExpr.Err msg => Error msg
  | SimplExpr.Res tbody g i =>
    OK {|
      fn_params := f.(fn_params);
      fn_body := tbody;

      fn_temps := f.(fn_temps);
      fn_vars := g.(SimplExpr.gen_trail) ++ f.(fn_vars);

      (*should not change*)
      fn_return := f.(fn_return);
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
