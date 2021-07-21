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

Variable match_states: CStan.state -> Clight.state -> Prop. 

Lemma senv_preserved: Senv.equiv ge tge.
Proof.
Admitted.

Lemma step_simulation:
  forall S1 t S2, CStan.stepf ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus Clight.step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
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

