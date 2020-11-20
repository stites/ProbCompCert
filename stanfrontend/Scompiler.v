Require Import Stan.
Require Import Clight.
Require Import Errors.
Require Import Smallstep.

Parameter transf_stan_program: Stan.program -> res Clight.program.

Theorem transf_stan_program_correct:
  forall p tp,
  transf_stan_program p = OK tp ->
  backward_simulation (Stan.semantics p) (Clight.semantics2 tp).
Proof.
Admitted.
