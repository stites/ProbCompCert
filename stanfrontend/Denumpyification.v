Require Import Stan.
Require Import CStan.
Require Import Errors.
Require Import String.

Definition transf_program(p: Stan.program): res CStan.program :=
  Error (msg EmptyString).
