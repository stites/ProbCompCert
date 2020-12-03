Require Import Stan.
Require Import Ssemantics.
Require Import Clight.
Require Import Errors.
Require Import Smallstep.
Require Import Asm. 

Parameter transf_stan_program: Stan.program -> res Clight.program.

Theorem transf_stan_program_correct:
  forall p tp,
  transf_stan_program p = OK tp ->
  backward_simulation (Ssemantics.semantics p) (Clight.semantics2 tp).
Proof.
Admitted.

Parameter transf_stan_program_complete: Stan.program -> res Asm.program.

Theorem transf_stan_program_correct_complete:
  forall p tp,
  transf_stan_program_complete p = OK tp ->
  backward_simulation (Ssemantics.semantics p) (Asm.semantics tp).
Proof.
Admitted.
