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

Check Clight.semantics1.
Check CStan.semantics.

Theorem transf_program_correct:
  forward_simulation (CStan.semantics prog m0) (Clight.semantics1 tprog).
Admitted.

End PRESERVATION.

