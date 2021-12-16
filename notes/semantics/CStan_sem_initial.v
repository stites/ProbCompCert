(* Initial semantics of CStan programs *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Stan.
Require Import CStan.

Inductive model_state: Type :=
  | MState                             (**r execution of statements where target is in scope *)
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (le: temp_env)
      (m: mem)
      (ta: float) : model_state (* ta is the running target *)
  | MCallstate                           (**r calling a function *)
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem)
      (ta: float) : model_state (* ta is the running target *)
  | MReturnstate                         (**r returning from a function *)
      (res: val)
      (k: cont)
      (m: mem)
      (ta: float) : model_state (* ta is the running target *).

Variable ge: genv.
Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.


Check eval_lvalue.

Inductive model_step: model_state -> trace -> model_state -> Prop :=
  | step_assign:   forall f a1 a2 k e le m ta loc ofs v2 v m',
      eval_lvalue ge e le m ta a1 loc ofs ->
      eval_expr ge e le m ta a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      model_step (MState f (Sassign a1 a2) k e le m ta)
                 E0 (MState f Sskip k e le m' ta)
  | step_set:   forall f id a k e le m ta v,
      eval_expr ge e le m ta a v ->
      model_step (MState f (Sset id a) k e le m ta)
        E0 (MState f Sskip k e (PTree.set id v le) m ta)
  | model_step_call:   forall f optid a al k e le m ta tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr ge e le m ta a vf ->
      eval_exprlist ge e le m ta al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      model_step (MState f (Scall optid a al) k e le m ta)
        E0 (MCallstate fd vargs (Kcall optid f e le k) m ta)
  | model_step_builtin:   forall f optid ef tyargs al k e le m ta vargs t vres m',
      eval_exprlist ge e le m ta al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      model_step (MState f (Sbuiltin optid ef tyargs al) k e le m ta)
         t (MState f Sskip k e (set_opttemp optid vres le) m' ta)
  | model_step_seq:  forall f s1 s2 k e le m ta,
      model_step (MState f (Ssequence s1 s2) k e le m ta)
        E0 (MState f s1 (Kseq s2 k) e le m ta)
  | model_step_skip_seq: forall f s k e le m ta,
      model_step (MState f Sskip (Kseq s k) e le m ta)
        E0 (MState f s k e le m ta)
  | model_step_continue_seq: forall f s k e le m ta,
      model_step (MState f Scontinue (Kseq s k) e le m ta)
        E0 (MState f Scontinue k e le m ta)
  | model_step_break_seq: forall f s k e le m ta,
      model_step (MState f Sbreak (Kseq s k) e le m ta)
        E0 (MState f Sbreak k e le m ta)
  | model_step_ifthenelse:  forall f a s1 s2 k e le m ta v1 b,
      eval_expr ge e le m ta a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      model_step (MState f (Sifthenelse a s1 s2) k e le m ta)
        E0 (MState f (if b then s1 else s2) k e le m ta)
  | model_step_loop: forall f s1 s2 k e le m ta,
      model_step (MState f (Sloop s1 s2) k e le m ta)
        E0 (MState f s1 (Kloop1 s1 s2 k) e le m ta)
  | model_step_skip_or_continue_loop1:  forall f s1 s2 k e le m x ta,
      x = Sskip \/ x = Scontinue ->
      model_step (MState f x (Kloop1 s1 s2 k) e le m ta)
        E0 (MState f s2 (Kloop2 s1 s2 k) e le m ta)
  | model_step_break_loop1:  forall f s1 s2 k e le m ta,
      model_step (MState f Sbreak (Kloop1 s1 s2 k) e le m ta)
        E0 (MState f Sskip k e le m ta)
  | model_step_skip_loop2: forall f s1 s2 k e le m ta,
      model_step (MState f Sskip (Kloop2 s1 s2 k) e le m ta)
        E0 (MState f (Sloop s1 s2) k e le m ta)
  | model_step_break_loop2: forall f s1 s2 k e le m ta,
      model_step (MState f Sbreak (Kloop2 s1 s2 k) e le m ta)
        E0 (MState f Sskip k e le m ta)
  | model_step_return_0: forall f k e le m m' ta,
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      model_step (MState f (Sreturn None) k e le m ta)
        E0 (MReturnstate Vundef (call_cont k) m' ta)
  | model_step_return_1: forall f a k e le m ta v v' m',
      eval_expr ge e le m ta a v ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      model_step (MState f (Sreturn (Some a)) k e le m ta)
        E0 (MReturnstate v' (call_cont k) m' ta)
  | model_step_skip_call: forall f k e le m m' ta,
      is_call_cont k ->
      Mem.free_list m (blocks_of_env ge e) = Some m' ->
      model_step (MState f Sskip k e le m ta)
        E0 (MReturnstate Vundef k m' ta)
  | model_step_skip_break_switch: forall f x k e le m ta,
      x = Sskip \/ x = Sbreak ->
      model_step (MState f x (Kswitch k) e le m ta)
        E0 (MState f Sskip k e le m ta)
  | model_step_continue_switch: forall f k e le m ta,
      model_step (MState f Scontinue (Kswitch k) e le m ta)
        E0 (MState f Scontinue k e le m ta)
  | model_step_internal_function: forall f vargs k m e le m1 ta,
      function_entry f vargs m e le m1 ->
      model_step (MCallstate (Internal f) vargs k m ta)
        E0 (MState f f.(fn_body) k e le m1 ta)
  | model_step_external_function: forall ef targs tres cconv vargs k m vres t m' ta,
      external_call ef ge vargs m t vres m' ->
      model_step (MCallstate (External ef targs tres cconv) vargs k m ta)
         t (MReturnstate vres k m' ta)
  | model_step_returnstate: forall v optid f e le k m ta,
      model_step (MReturnstate v (Kcall optid f e le k) m ta)
        E0 (MState f Sskip k e (set_opttemp optid v le) m ta)
  | model_step_target: forall f a k e le m ta v ta',
      eval_expr ge e le m ta a v ->
      v = Vfloat ta' ->
      model_step (MState f (Starget a) k e le m ta)
        E0 (MState f Sskip k e le m (Float.add ta ta'))
  .
End SEMANTICS.
