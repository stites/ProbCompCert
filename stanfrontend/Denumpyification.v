Require Import Stan.
Require Import CStan.
Require Import Errors.
Require Import String.
Open Scope string_scope.

Definition transf_program(p: Stan.program): res CStan.program :=
  Error (msg "Denumpyification.transf_program: NIY").
