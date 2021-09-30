Require Import AST.
Require Import CStan.

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont
  | Kseq: statement -> cont -> cont       (**r [Kseq s2 k] = after [s1] in [s1;s2] *)
  | Kloop1: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s1] in [Sloop s1 s2] *)
  | Kloop2: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s2] in [Sloop s1 s2] *)
  | Kswitch: cont -> cont       (**r catches [break] statements arising out of [switch] *)
  | Kcall: option ident ->                  (**r where to store result *)
           function ->                      (**r calling function *)
           env ->                           (**r local env of calling function *)
           temp_env ->                      (**r temporary env of calling function *)
           cont -> cont.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kloop1 s1 s2 k => call_cont k
  | Kloop2 s1 s2 k => call_cont k
  | Kswitch k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

