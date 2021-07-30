Require Import Coqlib.
Require Import Smallstep.
Require Import Sbackend.
Require Import CStan.
Require Import Clight.
Require Import Ssemantics.
Require Import Errors.
Require Import Globalenvs.
Require Import Memory.
Require Import Linking Ctypes Stypes.
Import Integers.

Section PRESERVATION.

Variable prog: CStan.program.
Variable tprog: Clight.program.
Hypothesis TRANSF: Sbackend.backend prog = OK tprog.
Let ge := CStan.globalenv prog.
Let tge := globalenv tprog.

Variable match_cont: CStan.cont -> Clight.cont -> Prop.

Inductive match_states: CStan.state -> Clight.state -> Prop :=
  | match_regular_states:
      forall f s k e le m t tf ts tk
      (TRF: transf_function f = OK tf)
      (TRS: transf_statement s = OK ts)
      (MCONT: match_cont k tk),
      match_states (CStan.State f s k e le m t)
                   (Clight.State tf ts tk e le m)
  | match_call_state:
      forall fd vargs k m t tfd tk
      (TRFD: transf_fundef fd = OK tfd)
      (MCONT: match_cont k tk),
      match_states (CStan.Callstate fd vargs k m t)
                   (Clight.Callstate tfd vargs tk m)
  | match_return_state:
      forall v k m t tk
      (MCONT: match_cont k tk),
      match_states (CStan.Returnstate v k m t)
                   (Clight.Returnstate v tk m).


(* --_-_-_-_---                            --_-_-_-_--- *)
(*     -_-_-     d$$$$"   d$$$$"  d$$$$"       -_-_-    *)
(*      -__-    **$$$"   **$$$"  **$$$"         -__-    *)
(*     _-_      .$$$$$"  .$$$$$" .$$$$$"       _-_      *)
(*    _-           z$"      z$"     z$"       _-        *)
(*    -_          zP       zP      zP         -_        *)
(*     _-        ,"       ,"      ,"           _-       *)
(*                                                      *)
(*      ░█▀▄░█▀█░█▀█░█▀▀░█▀▀░█▀▄░░░▀▀█░█▀█░█▀█░█▀▀      *)
(*      ░█░█░█▀█░█░█░█░█░█▀▀░█▀▄░░░▄▀░░█░█░█░█░█▀▀      *)
(*      ░▀▀░░▀░▀░▀░▀░▀▀▀░▀▀▀░▀░▀░░░▀▀▀░▀▀▀░▀░▀░▀▀▀      *)
(*                      ,---------,         ,---------, *)
(*              ,______;       ,____________;           *)
(*  ,__-----__,-    __'      _;         ,_______,       *)
(* ;__________;________________________________________ *)
(* //////////////////////////////////////////////////// *)

Program Instance Linker_types : Linker CStan.type := {
  link := fun (t1 t2: CStan.type) => None; (* FIXME *)
  linkorder := fun t1 t2 => t1 = t2; (* FIXME: not a valid preorder *)
}.

Definition match_prog (p: CStan.program) (tp: Clight.program) :=
  match_program (fun ctx f tf => Sbackend.transf_fundef f = OK tf) (fun cs cl => eq cl (CStan.vd_type cs)) p tp
  (* /\ prog_types tp = prog_types p. *) (* FIXME: I don't think this is necessary until we get structs. *)
  .

Lemma match_transf_program:
  forall p tp, Sbackend.backend p = OK tp -> match_prog p tp.
Proof.
  unfold Sbackend.backend. intros. monadInv H.
  eapply match_transform_partial_program2.
  rewrite EQ. destruct x.
  Admitted.

Lemma comp_env_preserved:
  genv_cenv tge = CStan.genv_cenv ge.
Proof.
  unfold tge, ge.
  Admitted.
(*   destruct tprog. *)
(*   destruct prog. tprog; simpl. destruct TRANSL as [_ EQ]. simpl in EQ. congruence. *)

(* Qed. *)
Lemma find_symbol_eq:
  (* Senv.find_symbol ge = Senv.find_symbol tge -> *)
  forall i,
  Genv.find_symbol ge i = Genv.find_symbol tge i.
Proof.
  intro.
  unfold Genv.find_symbol in *.
  unfold Genv.genv_symb in *.
  unfold CStan.genv_genv in *.
  unfold genv_genv in *.
  simpl in *.
  Admitted.



(*      .                       *)
(*    \ | /      All clear!     *)
(*  '-.;;;.-'                   *)
(* -==;;;;;==-                  *)
(* ---------------------------- *)

Hypothesis TRANSL: match_prog prog tprog.

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma symbols_preserved:
  forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSL).

Lemma sizeof_equiv :
  forall t,
  sizeof ge t = sizeof tge t.
Proof.
  intros.
  rewrite comp_env_preserved.
  auto.
Qed.

Lemma alignof_equiv :
  forall t,
  alignof ge t = alignof tge t.
Proof.
  rewrite comp_env_preserved.
  auto.
Qed.

Lemma transf_types_eq :
  forall e te,
  transf_expression e = OK te -> CStan.typeof e = Clight.typeof te.
Proof.
  intro e.
  induction e; intros; inv H;
    (* base cases *)
    try (simpl in *; reflexivity);

    (* cases with inductive hypothesis: Ederef, Eunop, Ebinop *)
    try (monadInv H1;  (* invert our inductive transf_expression *)
         constructor). (* the rest of the proof follows precisely by constructor *)
Qed.

Lemma eval_expr_correct:
  forall e le m a v target ta
  (TRE: transf_expression a = OK ta),
  CStan.eval_expr ge e le m target a v -> Clight.eval_expr tge e le m ta v.
Proof.
  intros e le m a.
  induction a; intros; simpl in TRE; monadInv TRE; simpl.

  (* Econst expressions: *)
  - (* inversion identifies the eval_Econst_* and eval_lvalue as possibilities *)
    inv H. (* apply inversion on our CStan.eval_expr *)
    constructor. (* for eval_Econst_*, apply the corresponding constructor *)
    inv H0.      (* for eval_lvalue, inversion on the new hypothesis shows that the pattern is invalid *)
  - inv H. constructor. inv H0.
  - inv H. constructor. inv H0.
  - inv H; try constructor; inv H0.

  - (* Evar expressions *)
    inv H. (* apply inversion on our CStan.eval_expr, this matches eval_lvalue. *)
    eapply eval_Elvalue.
    (* redo *)

    Focus 2. (* examine the new deref clauses first *)
    inv H1; simpl in *.
    eapply Clight.deref_loc_value; eauto.
    eapply Clight.deref_loc_reference; eauto.
    eapply Clight.deref_loc_copy; eauto.

    inv H0.
    eapply eval_Evar_local. eauto.
    eapply eval_Evar_global; eauto.
    rewrite symbols_preserved. eauto.

  - (* Etempvar expressions *)
    inv H.
    constructor. exact H3. inv H0.

  (* Inductive-hypotheses *)

  - (* Ederef expressions *)
    inv H. (* invert with CStan.eval_lvalue... *)
    inv H0. (* but look! we can only load variables. *)

  - (* Eunop expressions *)
    inv H.                               (* invert with CStan.eval_Eunop -- we must additionally show CStan.eval_lvalue is invalid. *)
    econstructor.                        (* apply Clight.eval_Eunop -- we must additionally show Cop.sem_unary_operation *)
    apply (IHa v1 target x EQ H4).       (* Eunop is then shown to be valid by inductive case of it's argument *)
    rewrite (transf_types_eq a x) in H5.
    exact H5. exact EQ.                  (* Cop.sem_unary_operation is true by transf_types_eq, so long as EQ *)
    inv H0.                              (* CStan.eval_lvalue is invalid. *)

  - (* Ebinop expressions *)
    inv H.                                 (* invert with CStan.eval_Ebinop *)
    Focus 2. inv H0.                       (* this also pattern-matches on the invalid CStan.eval_lvalue -- just deal with that now. *)
    econstructor.                          (* apply Clight.eval_Ebinop *)
    apply (IHa1 v1 target x EQ H5).        (* The first argument is then proven true by the first inductive case*)
    apply (IHa2 v2 target x0 EQ1 H6).      (* The second argument is then proven true by the second inductive case*)

    rewrite (transf_types_eq a1 x ) in H7. (* we additionally need to show that Cop.sem_binary_operation is true. *)
    rewrite (transf_types_eq a2 x0) in H7.
    rewrite comp_env_preserved.
    eauto.
    eauto.
    eauto.

  (* Two more base cases *)

  - (* Esizeof expressions *)
    inv H.
    rewrite sizeof_equiv.
    apply Clight.eval_Esizeof.
    inv H0.

  - (* Ealignof expressions *)
    inv H.
    rewrite alignof_equiv.
    apply Clight.eval_Ealignof.
    inv H0.
Qed.

Lemma eval_lvalue_correct:
  forall e le m a b ofs target ta
  (TRE: transf_expression a = OK ta),
  CStan.eval_lvalue ge e le m target a b ofs -> Clight.eval_lvalue tge e le m ta b ofs.
Proof.
  intros e le m a.
  induction a; intros; monadInv TRE; try (inv H).
  - econstructor. eauto.
  - eapply eval_Evar_global; eauto.
    rewrite symbols_preserved. auto.
Qed.

Lemma types_correct:
  forall e x, transf_expression e = OK x -> CStan.typeof e = Clight.typeof x.
Proof.
  intro e.
  induction e; intros; simpl in *; monadInv H; simpl; trivial.
Qed.

Lemma step_simulation:
  forall S1 t S2, CStan.stepf ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus Clight.step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1. simpl; intros; inv MS; simpl in *; try (monadInv TRS).

  (* assign *)
  exists (Clight.State tf Clight.Sskip tk e le m').
  split.
  eapply plus_one.
  generalize (types_correct _ _ EQ); intro.
  generalize (types_correct _ _ EQ1); intro.  
  rewrite H3 in *.
  rewrite H4 in *.
  unfold step1. 
  eapply step_assign.
  eapply eval_lvalue_correct; eauto.
  eapply eval_expr_correct; eauto.
  eapply H1.
  admit.
  econstructor; eauto.
  Focus 1.
  intros.

Admitted.

Lemma initial_states_simulation:
  forall S, CStan.initial_state prog S ->
  exists R, Clight.initial_state tprog R /\ match_states S R.
Proof.
Admitted.

Lemma final_states_simulation:
  forall S R r,
  match_states S R -> CStan.final_state S r -> Clight.final_state R r.
Proof.
Admitted.


Theorem transf_program_correct:
  forward_simulation (CStan.semantics prog) (Clight.semantics1 tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact initial_states_simulation.
  eexact final_states_simulation.
  eexact step_simulation.
Admitted.

End PRESERVATION.

