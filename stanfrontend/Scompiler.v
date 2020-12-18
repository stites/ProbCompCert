Require Import Stan.
Require Import Ssemantics.
Require Import Clight.
Require Import Errors.
Require Import Smallstep.
Require Import Asm. 
Require Import Stemplate.
Require Import Compiler.
Require Import Denumpyification.
Require Import String.

Definition backend (p: CStan.program): res Clight.program :=
  OK (Stemplate.prog).							     
  
Definition transf_stan_program(p: Stan.program): res Clight.program :=
  OK p
  @@@ time EmptyString Denumpyification.transf_program								  
  @@@ time EmptyString backend.
  
Theorem transf_stan_program_correct:
  forall p tp,
  transf_stan_program p = OK tp ->
  backward_simulation (Ssemantics.semantics p) (Clight.semantics2 tp).
Proof.
Admitted.

Definition transf_stan_program_complete(p: Stan.program): res Asm.program :=						 
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
