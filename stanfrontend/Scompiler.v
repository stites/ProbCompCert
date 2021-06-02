Require Import StanE.
Require Import Ssemantics.
Require Import Clight.
Require Import Errors.
Require Import Smallstep.
Require Import Asm. 
Require Import Stemplate.
Require Import Compiler.
Require Import Denumpyification.
Require Import FirstTransform.
Require Import String.
Require Import Sbackend.
Open Scope string_scope.						     

Definition transf_stan_program(p: StanE.program): res Clight.program :=
  OK p
  @@@ time "Denumpyification" Denumpyification.transf_program
  @@@ time "FirstTransform" FirstTransform.transf_program
  @@@ time "Backend" backend.
  
Theorem transf_stan_program_correct:
  forall p tp,
  transf_stan_program p = OK tp ->
  backward_simulation (Ssemantics.semantics p) (Clight.semantics2 tp).
Proof.
Admitted.

Definition transf_stan_program_complete(p: StanE.program): res Asm.program :=						 
  let p := transf_stan_program p in
  match p with				
  | OK p => transf_clight_program p
  | Error s => Error s
  end.															 
  
Theorem transf_stan_program_correct_complete:
  forall p tp,
  transf_stan_program_complete p = OK tp ->
  backward_simulation (Ssemantics.semantics p) (Asm.semantics tp).
Proof.
Admitted.
