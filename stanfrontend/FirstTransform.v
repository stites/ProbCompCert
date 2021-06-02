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
Require AST.
From ReductionEffect Require Import PrintingEffect.

(* FIXME how do I share this notation? *)
Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition flt64 := Tfloat F64 noattr.
Definition target_ident : AST.ident := xH. (* FIXME setting ident to 1 (xH) seems like a bad idea*)
Definition target_type : type := {|
  vd_type := flt64;
  vd_constraint:= Stan.Cidentity;
  vd_init := Some (Econst_float (Floats.Float.of_int Integers.Int.zero) flt64);
  vd_block := Bparam;
  vd_global := true;
|}.
Definition vtarget := CStan.Evar target_ident target_type.(vd_type).

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
  | CStan.Etarget (Tfloat sz attr) =>
    OK (CStan.Evar xH (Tfloat sz attr))
  | CStan.Etarget _ => Error (msg "target can only be of type float")
end.

Fixpoint mmap {A:Type} {B:Type} (f: A -> res B) (l: list A) : res (list B) :=
  match l with
    | nil => OK nil
    | a :: a's =>
      do b <- f a;
      do b's <- mmap f a's;
      OK (b :: b's)
  end.

Fixpoint transf_statement (s: CStan.statement) {struct s}: res CStan.statement :=
match s with
  | Sskip => OK Sskip
  | Sassign e0 e1 =>
    Error (msg "Sassign")
    (* do e0 <- transf_expr e0; *)
    (* do e1 <- transf_expr e1; *)
    (* OK (Sassign e0 e1) *)
  | Sset i e =>
    Error (msg "Sset")
    (* do e <- transf_expr e; *)
    (* OK (Sset i e) *)
  | Scall oi e le =>
    Error (msg "Scall")
    (* do e <- transf_expr e; *)
    (* do le <- mmap transf_expr le; *)
    (* OK (Scall oi e le) *)
  | Sbuiltin oi ef lt le => Error (msg "OK (Sbuiltin oi ef lt le)")
  | Ssequence s0 s1 =>
    do s0 <- transf_statement s0;
    do s1 <- transf_statement s1;
    OK (Ssequence s0 s1)
  | Sifthenelse e s0 s1 =>
    do s0 <- transf_statement s0;
    do s1 <- transf_statement s1;
    OK (Sifthenelse e s0 s1)
  | Sloop s0 s1 =>
    do s0 <- transf_statement s0;
    do s1 <- transf_statement s1;
    OK (Sloop s0 s1)
  | Sbreak => OK Sbreak
  | Scontinue => OK Scontinue
  | Sreturn oe =>
    do oe <- Denumpyification.option_mmap transf_expr oe;
    OK (Sreturn oe)
  | Starget e =>
    Error (msg "Starget e")
    (* do e <- transf_expr e; *)
    (* (* Scall (): option ident -> expr -> list expr -> statement (**r function call *) *) *)

    (* OK (Starget vtarget) *)
  | Stilde e i le (oe0, oe1) =>
    OK (Ssequence (*instead of calling the dist function, just add: *)
          (Sassign e (Econst_float (Floats.Float.of_int Integers.Int.one) flt64))
      (*(Scall (Some i) e le) (* 'fn' 'ret' 'args'? *)*)
          (Sassign vtarget (Ebinop Cop.Oadd vtarget e flt64)))
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

(* Definition transf_model_def (id: AST.program CStan.fundef CStan.type) (m: AST.ident) (p : CStan.program): res CStan.program := *)
(*   OK p. *)

Notation global_refs := (prod AST.ident (AST.globdef fundef type)).

Definition inject_target (defs: list global_refs): res (list global_refs) :=
  let target_gvar := AST.Gvar ({|
         AST.gvar_info:= target_type;
         AST.gvar_init:= (AST.Init_float64 (Floats.Float.of_int Integers.Int.zero))::nil;
         AST.gvar_readonly := false;
         AST.gvar_volatile := false;
        |})
  in OK ((target_ident, target_gvar) :: defs).


Definition transf_program(p: CStan.program): res CStan.program :=
  do p1 <- AST.transform_partial_program2 transf_fundef transf_variable p;
  do defs <- inject_target (AST.prog_defs p1);
  OK {|
      prog_defs := defs;
      prog_public := AST.prog_public p1;

      prog_data:=p.(prog_data);
      prog_transformed_data:=p.(prog_transformed_data);

      prog_parameters:= p.(prog_parameters);
      prog_transformed_parameters:=p.(prog_transformed_parameters);

      prog_generated_quantities:=p.(prog_generated_quantities);
      prog_model:=p.(prog_model);

      prog_comp_env:=p.(prog_comp_env);
    |}.
