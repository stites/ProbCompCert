Require Import Coqlib.
Require Import Smallstep.
Require Import Sbackend.
Require Import CStan.
Require Import Clight.
Require Import Ssemantics.
Require Import Errors.
Require Import Globalenvs.
Require Import Memory.


Section PRESERVATION.

Variable prog: CStan.program.
Variable tprog: Clight.program.
Variable m0: mem.
Hypothesis TRANSF: Sbackend.backend prog = OK tprog.
Hypothesis INITMEM: Genv.init_mem prog = Some m0.
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
      forall fd vargs k m t tfd tk i
      (TRFD: transf_fundef i fd = OK tfd)
      (MCONT: match_cont k tk),
      match_states (CStan.Callstate fd vargs k m t)
                   (Clight.Callstate tfd vargs tk m)
  | match_return_state:
      forall v k m t tk
      (MCONT: match_cont k tk),
      match_states (CStan.Returnstate v k m t)
                   (Clight.Returnstate v tk m).

Lemma senv_preserved: Senv.equiv ge tge.
Proof.
Admitted.

Lemma eval_expr_correct:
  forall e le m a v target ta
  (TRE: transf_expression a = OK ta),
  CStan.eval_expr ge e le m target a v -> Clight.eval_expr tge e le m ta v.
Proof.
Admitted.

Lemma eval_lvalue_correct:
  forall e le m a b ofs target ta
  (TRE: transf_expression a = OK ta),
  CStan.eval_lvalue ge e le m target a b ofs -> Clight.eval_lvalue tge e le m ta b ofs.
Proof.
Admitted.

Lemma types_correct:
  forall e x, transf_expression e = OK x -> CStan.typeof e = Clight.typeof x.
Proof.
Admitted.

Lemma step_simulation:
  forall S1 t S2, CStan.stepf ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus Clight.step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; simpl; intros; inv MS; simpl in *; try (monadInv TRS).

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


Admitted.

Lemma initial_states_simulation:
  forall S, CStan.initial_state prog m0 S ->
  exists R, Clight.initial_state tprog R /\ match_states S R.
Proof.
Admitted.

Lemma final_states_simulation:
  forall S R r,
  match_states S R -> CStan.final_state S r -> Clight.final_state R r.
Proof.
Admitted.


Theorem transf_program_correct:
  forward_simulation (CStan.semantics prog m0) (Clight.semantics1 tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact initial_states_simulation.
  eexact final_states_simulation.
  eexact step_simulation.
Admitted.

End PRESERVATION.

