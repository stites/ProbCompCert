Require Import Coqlib.
Require Import Smallstep.
Require Import Target.
Require Import Ssemantics.
Require Import Errors.
Require Import Globalenvs.
Require Import Memory.
Require Import Maps.
Require Import Values.
Require Import Csem.
Require Import Linking Ctypes Stypes.
Import Integers.
Require Import CStan.
Require Import CStanCont.
Require CStanSemanticsTarget.
Require Import CStanSemanticsBackend.
Require Sbackendproof.

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: Target.transf_program prog = OK tprog.
(* Variable ge: genv. *)

Let ge := globalenv prog.
Let tge := globalenv tprog.

(** Matching continuations *)
Inductive match_cont : AST.ident -> cont -> cont -> Prop :=
  | match_Kstop: forall ti,
      match_cont ti Kstop Kstop
  | match_Kseq: forall s k ts ti tk ,
      transf_statement ti s = OK ts ->
      match_cont ti k tk ->
      match_cont ti (Kseq s k) (Kseq ts tk)
  | match_Kloop1: forall s1 s2 k ts1 ts2 ti tk ,
      transf_statement ti s1 = OK ts1 ->
      transf_statement ti s2 = OK ts2 ->
      match_cont ti k tk ->
      match_cont ti (Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk)
  | match_Kloop2: forall s1 s2 k ts1 ts2 ti tk ,
      transf_statement ti s1 = OK ts1 ->
      transf_statement ti s2 = OK ts2 ->
      match_cont ti k tk ->
      match_cont ti (Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk)
  | match_Kswitch: forall k ti tk ,
      match_cont ti k tk ->
      match_cont ti (Kswitch k) (Kswitch tk)
  | match_Kcall: forall optid fn e le k tfn ti tk ,
      transf_function ti fn = OK tfn ->
      fn.(fn_blocktype) <> BTModel ->
      match_cont ti k tk ->
      match_cont ti (Kcall optid fn e le k)
                        (Kcall optid tfn e le tk)
  | match_Kcall_model: forall optid fn e le k tfn ti tk,
      transf_function ti fn = OK tfn ->
      fn.(fn_blocktype) = BTModel ->
      match_cont ti k tk ->
      match_cont ti (Kcall optid fn e le k)
                        (Kseq (Sreturn (Some (Evar ti tdouble))) (Kcall optid tfn e le tk))
. (* NOTE: target register is updated local environment -- assuming e and le are identical is probably wrong.*)


Inductive match_states: AST.ident -> CStanSemanticsTarget.state -> CStanSemanticsBackend.state -> Prop :=
  | match_regular_states:
      forall f s k e le m tf ts tk bs i
      (TRF: transf_function i f = OK tf)
      (TRS: transf_statement i s = OK ts)
      (BS_OTHER: bs = CStanSemanticsTarget.Other)
      (MCONT: match_cont i k tk),
      match_states i (CStanSemanticsTarget.State f s k e le m bs)
                   (CStanSemanticsBackend.State tf ts tk e le m)
  | match_call_state:
      forall fd vargs k m tfd tk bs i
      (TRFD: transf_fundef i fd = OK tfd)
      (GET_FN: (exists e tl r cc, fd = External e tl r cc) \/ (exists fn, fd = Internal fn /\ fn.(fn_blocktype) <> BTModel))
      (MCONT: match_cont i k tk),
      match_states i (CStanSemanticsTarget.Callstate fd vargs k m bs)
                   (CStanSemanticsBackend.Callstate tfd vargs tk m)
  | match_return_state:
      forall v k m tk bs i
      (BS_OTHER: bs = CStanSemanticsTarget.Other)
      (MCONT: match_cont i k tk),
      match_states i (CStanSemanticsTarget.Returnstate v k m bs)
                   (CStanSemanticsBackend.Returnstate v tk m)

  | match_regular_states_model:
      forall f s k e le m tf ts tk bs i ta
      (TRF: transf_function i f = OK tf)
      (TRS: transf_statement i s = OK ts)
      (BS_MODEL: bs = CStanSemanticsTarget.Model ta)
      (TAR_MATCH: le!i = Some (Vfloat ta))
      (MCONT: match_cont i k tk),
      match_states i (CStanSemanticsTarget.State f s k e le m bs)
                   (CStanSemanticsBackend.State tf ts tk e le m)
  | match_call_state_model:
      forall fd vargs k m tfd tk bs fn tgt
      (GET_FN: fd = Internal fn)
      (BS_OTHER: bs = CStanSemanticsTarget.Other)
      (BMODEL: fn.(fn_blocktype) = BTModel)
      (TRFD: transf_fundef tgt fd = OK tfd)
      (MCONT: match_cont tgt k (Kseq (Sreturn (Some (Evar tgt tdouble))) tk)),
      match_states tgt (CStanSemanticsTarget.Callstate fd vargs k m bs)
                   (CStanSemanticsBackend.Callstate tfd vargs tk m)
  | match_return_state_model:
      forall v k m tk bs ta tgt
      (BS_MODEL: bs = CStanSemanticsTarget.Model ta)
      (MCONT: match_cont tgt k tk),
      match_states tgt (CStanSemanticsTarget.Returnstate v k m bs)
                   (CStanSemanticsBackend.Returnstate v tk m)
.

(** * Relational specification of the transformation *)

Definition match_prog (p: CStan.program) (tp: CStan.program) :=
    match_program (fun ctx f tf => Target.transf_fundef p.(prog_target) f = OK tf) eq p tp
 /\ prog_types tp = prog_types p.

Variable TRANSL: match_prog prog tprog.

Lemma comp_env_preserved:
  genv_cenv tge = genv_cenv ge.
Proof.
  unfold tge, ge. destruct TRANSL as [_ EQ].
  generalize (prog_comp_env_eq tprog).
  generalize (CStan.prog_comp_env_eq prog).
  destruct tprog, prog; simpl in *.
  congruence.
Qed.

(* Inductive tr_function: CStan.function -> CStan.function -> Prop := *)
(*   | tr_function_intro: forall f tf, *)
(*       (* tr_stmt f.(CStan.fn_body) tf.(fn_body) -> *) *)
(*       fn_return tf = CStan.fn_return f -> *)
(*       fn_callconv tf = CStan.fn_callconv f -> *)
(*       fn_params tf = CStan.fn_params f -> *)
(*       fn_vars tf = CStan.fn_vars f -> *)
(*       tr_function f tf. *)

(* Inductive tr_fundef: CStan.fundef -> Clight.fundef -> Prop := *)
(*   | tr_internal: forall f tf, *)
(*       tr_function f tf -> *)
(*       tr_fundef (Internal f) (Internal tf) *)
(*   | tr_external: forall ef targs tres cconv, *)
(*       tr_fundef (External ef targs tres cconv) (External ef targs tres cconv). *)

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof.
  apply (Genv.senv_match (proj1 TRANSL)).
Qed.

Lemma symbols_preserved:
  forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof.
  apply (Genv.find_symbol_match (proj1 TRANSL)).
Qed.

(* Lemma functions_translated: *)
(*   forall (v: val) (f: CStan.fundef), *)
(*   Genv.find_funct ge v = Some f -> *)
(*   exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf. *)
(* Proof. *)
(*   intros. *)
(*   edestruct (Genv.find_funct_match (proj1 TRANSL)) as (ctx' & tf & A & B & C'); eauto. *)
(* Qed. *)

(* Lemma type_of_fundef_preserved: *)
(*   forall fd tfd, *)
(*   transf_fundef fd = OK tfd -> type_of_fundef tfd = CStan.type_of_fundef fd. *)
(* Proof. *)
(*   intros. destruct fd; monadInv H; auto. *)
(*   monadInv EQ. simpl; unfold type_of_function; simpl. auto. *)
(* Qed. *)

Lemma sizeof_equiv :
  forall t,
  sizeof ge t = sizeof tge t.
Proof.
  rewrite comp_env_preserved.
  auto.
Qed.

Lemma alignof_equiv :
  forall t,
  alignof ge t = alignof tge t.
Proof.
  rewrite comp_env_preserved.
  auto.
Qed.

Lemma transf_types_eq :
  forall e te i,
  Target.transf_etarget_expr i e = OK te -> typeof e = typeof te.
Proof.
  intro e.
  induction e; intros; inv H;
    (* base cases *)
    try (simpl in *; reflexivity);

    (* cases with inductive hypothesis: Ederef, Eunop, Ebinop *)
    try (monadInv H1;  (* invert our inductive transf_expression *)
         constructor). (* the rest of the proof follows precisely by constructor *)
Qed.

Lemma eval_expr_correct:
  forall e le m a v bs ta i
  (TRE: Target.transf_etarget_expr i a = OK ta),
  CStanSemanticsTarget.eval_expr ge e le m bs a v -> eval_expr tge e le m ta v.
Proof.
  intros e le m a.
  induction a; intros;
  simpl in TRE; monadInv TRE; simpl.
    (* Econsts *)
  - inv H; try constructor; inv H0.
  - inv H; try constructor; inv H0.
  - inv H; try constructor; inv H0.
  - inv H; try constructor; inv H0.

  - (* Evar expressions *)
    inv H. (* apply inversion on our CStan.eval_expr, this matches eval_lvalue. *)
    eapply CStanSemanticsBackend.eval_Elvalue; eauto.
    inv H0.
    eapply CStanSemanticsBackend.eval_Evar_local; eauto.
    eapply CStanSemanticsBackend.eval_Evar_global; eauto.
    rewrite symbols_preserved; eauto.

  - (* Etempvar *)
    inv H. constructor; eauto. inv H0.
  - (* Ederef *)
    inv H. inv H0.
  - (*Ecast*)
    admit. (* inv H3. *)
    (* apply (IHa v bs ta i). *)
  (*   monadInv TRE. *)
  (*   eapply IHa. *)
  (*   econstructor. *)
  (*   eapply (IHa v bs (Ecast a t) i). *)
  - (* field *)
    inv H.
    admit. (* inv H4. *)
    admit.
  - (* Eaddrof *)
    inv H.
    inv H0.
  - (* Eunop expressions *)
    inv H.                               (* invert with CStan.eval_Eunop -- we must additionally show CStan.eval_lvalue is invalid. *)
    econstructor.                        (* apply Clight.eval_Eunop -- we must additionally show Cop.sem_unary_operation *)
    apply (IHa v1 bs x i EQ H4).       (* Eunop is then shown to be valid by inductive case of it's argument *)
    rewrite (transf_types_eq a x i) in H5; eauto. (* Cop.sem_unary_operation is true by transf_types_eq, so long as EQ *)
    inv H0.                                     (* CStan.eval_lvalue is invalid. *)

  - (* Ebinop expressions *)
    inv H.                                 (* invert with CStan.eval_Ebinop *)
    Focus 2. inv H0.                       (* this also pattern-matches on the invalid CStan.eval_lvalue -- just deal with that now. *)
    econstructor.                          (* apply Clight.eval_Ebinop *)
    apply (IHa1 v1 bs x  i EQ H5).        (* The first argument is then proven true by the first inductive case*)
    apply (IHa2 v2 bs x0 i EQ1 H6).      (* The second argument is then proven true by the second inductive case*)

    rewrite (transf_types_eq a1 x  i) in H7. (* we additionally need to show that Cop.sem_binary_operation is true. *)
    rewrite (transf_types_eq a2 x0 i) in H7.
    rewrite comp_env_preserved.
    eauto.
    eauto.
    eauto.

  (* Two more base cases *)

  - (* Esizeof expressions *)
    inv H.
    rewrite sizeof_equiv.
    econstructor.
    inv H0.

  - (* Ealignof expressions *)
    inv H.
    rewrite alignof_equiv.
    constructor.
    inv H0.
Admitted.

Lemma eval_lvalue_correct:
  forall e le m a b ofs target ta i
  (TRE: transf_etarget_expr i a = OK ta),
  CStanSemanticsTarget.eval_lvalue ge e le m target a b ofs -> CStanSemanticsBackend.eval_lvalue tge e le m ta b ofs.
Proof.
  intros e le m a.
  induction a; intros; monadInv TRE; try (inv H).
  - econstructor. eauto.
  - eapply CStanSemanticsBackend.eval_Evar_global; eauto.
    rewrite symbols_preserved; eauto.
Qed.

Lemma types_correct:
  forall e x t, transf_etarget_expr t e = OK x -> typeof e = typeof x.
Proof.
  intro e.
  induction e; intros; simpl in *; monadInv H; simpl; trivial.
Qed.

Lemma functions_translated:
  forall (v: val) (f: fundef) ,
  Genv.find_funct ge v = Some f ->
  exists tf, Genv.find_funct tge v = Some tf /\ transf_fundef (prog_target prog) f = OK tf.
Proof.
  intros.
  edestruct (Genv.find_funct_match (proj1 TRANSL)) as (ctx' & tf & A & B & C'); eauto.
Qed.

(* Lemma match_cont_call_cont: *)
(*   forall k tk , *)
(*   match_cont k tk  -> *)
(*   match_cont (CStanSemanticsTarget.call_cont k) (call_cont tk) . *)
(* Proof. *)
(*   induction 1; simpl; auto; intros; econstructor; eauto. *)
(* Qed. *)

(* Lemma blocks_of_env_preserved: *)
(*   forall e, CStanSemanticsTarget.blocks_of_env tge e = CStanSemanticsBackend.blocks_of_env ge e. *)
(* Proof. *)
(*   intros; unfold blocks_of_env, CStanSemanticsBackend.blocks_of_env. *)
(*   unfold block_of_binding, CStanSemanticsBackend.block_of_binding. *)
(*   rewrite comp_env_preserved. auto. *)
(* Qed. *)

(* Lemma transf_sem_cast_inject: *)
(*   forall f tf x tx v v' m, *)
(*   transf_expression x = OK tx -> *)
(*   transf_function f = OK tf -> *)
(*   Cop.sem_cast v (CStan.typeof x) (CStan.fn_return f) m = Some v' -> *)
(*   Cop.sem_cast v (typeof tx) (fn_return tf) m = Some v'. *)
(* Proof. *)
(*   intros. *)
(*   generalize (types_correct _ _ H); intro. *)
(*   monadInv H0. simpl in *. *)
(*   rewrite <- H2. *)
(*   auto. *)
(* Qed. *)

(* Lemma alloc_variables_preserved: *)
(*   forall e m params e' m', *)
(*   CStanSemanticsBackend.alloc_variables ge e m params e' m' -> *)
(*   alloc_variables tge e m params e' m'. *)
(* Proof. *)
(*   induction 1; econstructor; eauto. rewrite comp_env_preserved; auto. *)
(* Qed. *)

(* Lemma bind_parameters_preserved: *)
(*   forall e m params args m', *)
(*   CStanSemanticsBackend.bind_parameters ge e m params args m' -> *)
(*   bind_parameters tge e m params args m'. *)
(* Proof. *)
(*   induction 1; econstructor; eauto. inv H0. *)
(* - eapply assign_loc_value; eauto. *)
(* - eapply assign_loc_copy; eauto; rewrite <- comp_env_preserved in *; auto. *)
(* Qed. *)

Lemma eval_exprlist_correct_simple:
  forall env le es tes tys m vs ta t
  (TREL: res_mmap (transf_etarget_expr t) es = OK tes)
  (EVEL: CStanSemanticsTarget.eval_exprlist ge env le m ta es tys vs),
  eval_exprlist tge env le m tes tys vs.
Proof.
  intros env le es.
  induction es; intros.
  monadInv TREL.
  inv EVEL; eauto.
  econstructor.
  monadInv TREL.
  inv EVEL; eauto.
  econstructor; eauto.
  eapply eval_expr_correct; eauto.
  generalize (types_correct _ _ _ EQ); intro.
  rewrite <- H; eauto.
Qed.


Lemma step_simulation:
  forall S1 t S2 i, CStanSemanticsTarget.stepf ge S1 t S2 ->
  forall S1' (MS: match_states i S1 S1'), exists S2', plus CStanSemanticsBackend.stepf tge S1' t S2' /\ match_states i S2 S2'.
Proof.
  induction 1.

  - (* assign *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    + (* assin in Other block *)
      exists (State tf Sskip tk e le m').
      split.
      eapply plus_one.
      generalize (types_correct _ _ _ EQ); intro.
      generalize (types_correct _ _ _ EQ0); intro.
      rewrite H3 in *.
      rewrite H4 in *.
      unfold stepf.
      eapply step_assign; eauto.
      eapply eval_lvalue_correct; eauto.
      eapply eval_expr_correct; eauto.
      inv H2.
      eapply assign_loc_value; eauto.
      eapply assign_loc_copy; try (rewrite comp_env_preserved); eauto.
      eapply match_regular_states; eauto.

    + (* assign in Model Block *)
      exists (State tf Sskip tk e le m').
      split.
      eapply plus_one.
      generalize (types_correct _ _ _ EQ); intro.
      generalize (types_correct _ _ _ EQ0); intro.
      rewrite H3 in *.
      rewrite H4 in *.
      unfold stepf.
      eapply step_assign; eauto.
      eapply eval_lvalue_correct; eauto.
      eapply eval_expr_correct; eauto.
      inv H2.
      eapply assign_loc_value; eauto.
      eapply assign_loc_copy; try (rewrite comp_env_preserved); eauto.
      eapply match_regular_states_model; eauto.

  - (* set *)
    simpl; intros; inv MS; simpl in *.
    + (* in other *)
      monadInv TRS; monadInv EQ; monadInv EQ0.
      econstructor.
      split. eapply plus_one.
      destruct (id =? i)%positive eqn:TEQ.
      inv EQ1.
      monadInv EQ1.
      unfold stepf.
      econstructor.
      eapply eval_expr_correct; eauto.
      eapply match_regular_states; eauto.
    + (* in model *)
      monadInv TRS.
      monadInv EQ.
      monadInv EQ0.
      econstructor.
      destruct (id =? i)%positive eqn:TEQ.
      inv EQ1.
      monadInv EQ1.
      split. eapply plus_one.
      unfold stepf.
      econstructor.
      eapply eval_expr_correct; eauto.
      eapply match_regular_states_model; eauto.
      apply Pos.eqb_neq in TEQ.
      Search PTree.set.
      rewrite PTree.gso; auto.

  - (* call *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    exploit eval_expr_correct; eauto; intro.
    exploit eval_exprlist_correct_simple; eauto. intro tvargs.
    exploit functions_translated; eauto. intros [tfd [P Q]].
    econstructor. split. eapply plus_one. eapply step_call with (fd := tfd).
    generalize (types_correct _ _ EQ); intro TYA. rewrite<-TYA. eauto.
    eauto. eauto. eauto.
    rewrite (type_of_fundef_preserved fd); eauto.
    eapply match_call_state; eauto.
    econstructor; eauto.


    intros; inv MS.
    monadInv TRS.
    econstructor.
  (*   eapply eval_expr_correct; eauto. *)
  (*   exploit eval_expr_correct; eauto; intro. *)
  (*   exploit eval_exprlist_correct_simple; eauto. intro tvargs. *)
  (*   exploit functions_translated; eauto. intros [tfd [P Q]]. *)
  (*   econstructor. split. eapply plus_one. eapply step_call with (fd := tfd). *)
  (*   generalize (types_correct _ _ EQ); intro TYA. rewrite<-TYA. eauto. *)
  (*   eauto. eauto. eauto. *)
  (*   rewrite (type_of_fundef_preserved fd); eauto. *)
  (*   eapply match_call_state; eauto. *)
  (*   econstructor; eauto. *)

  (* - (* builtin *) *)
  (*   intros; inv MS. *)
  (*   monadInv TRS. *)
  (*   exists (State tf Sskip tk e (set_opttemp optid vres le) m'). *)
  (*   split. eapply plus_one. unfold step1. *)
  (*   eapply step_builtin. *)
  (*   eapply eval_exprlist_correct_simple; eauto. *)
  (*   eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved. *)
  (*   eapply match_regular_states; eauto. *)
  (* - (* sequence seq *) *)
  (*   intros. *)
  (*   inv MS; monadInv TRS. *)
  (*   exists (State tf x (Kseq x0 tk) e le m). *)
  (*   split. *)
  (*   eapply plus_one. *)
  (*   unfold step1. *)
  (*   eapply step_seq. *)
  (*   eapply match_regular_states; eauto. *)
  (*   econstructor; eauto. *)
  (* - (* skip sequence *) *)
  (*   intros. *)
  (*   inv MS; monadInv TRS. *)
  (*   inv MCONT. *)
  (*   exists (State tf ts tk0 e le m). *)
  (*   split. *)
  (*   eapply plus_one. *)
  (*   unfold step1. *)
  (*   eapply step_skip_seq. *)
  (*   eapply match_regular_states; eauto. *)
  (* - (* continue sequence *) *)
  (*   intros; inv MS; monadInv TRS. *)
  (*   inv MCONT. *)
  (*   exists (State tf Scontinue tk0 e le m). *)
  (*   split. *)
  (*   eapply plus_one. *)
  (*   unfold step1. *)
  (*   eapply step_continue_seq. *)
  (*   eapply match_regular_states; eauto. *)
  (* - (* break sequence *) *)
  (*   intros; inv MS; monadInv TRS. *)
  (*   inv MCONT. *)
  (*   exists (State tf Sbreak tk0 e le m). *)
  (*   split. *)
  (*   eapply plus_one; unfold step1. *)
  (*   eapply step_break_seq. *)
  (*   eapply match_regular_states; eauto. *)
  (* - (* if then else *) *)
  (*   intros; inv MS; monadInv TRS. *)
  (*   econstructor. *)
  (*   split. *)
  (*   eapply plus_one; unfold step1. *)
  (*   econstructor. *)
  (*   eapply eval_expr_correct; eauto. *)
  (*   generalize (types_correct _ _ EQ); intro. *)
  (*   rewrite <- H1; eauto. *)
  (*   eapply match_regular_states; eauto. *)
  (*   destruct b; eauto. *)
  (* - (* step_loop *) *)
  (*   intros; inv MS; monadInv TRS. *)
  (*   exists (State tf x (Kloop1 x x0 tk) e le m). *)
  (*   split. *)
  (*   eapply plus_one; unfold step1. *)
  (*   eapply step_loop. *)
  (*   eapply match_regular_states; eauto. *)
  (*   eapply match_Kloop1; eauto. *)
  (* - (* step_skip_or_continue_loop1 *) *)
  (*   intros. inv MS; inv MCONT; destruct H; *)
  (*   repeat ( *)
  (*     econstructor; split; *)
  (*     try (eapply plus_one; unfold step1; *)
  (*       eapply step_skip_or_continue_loop1; *)
  (*       monadInv TRF; monadInv TRS; eauto); *)
  (*     eapply match_regular_states; eauto; eapply match_Kloop2; eauto *)
  (*   ). *)

  (* - (* step_break_loop1 *) *)
  (*   intros; inv MS; monadInv TRS; inv MCONT. *)
  (*   econstructor. split. *)
  (*   eapply plus_one; unfold step1. *)
  (*   eapply step_break_loop1; eauto. *)
  (*   eapply match_regular_states; eauto. *)
  (* - (* step_skip_loop2 *) *)
  (*   intros; inv MS; monadInv TRS; inv MCONT. *)
  (*   exists (State tf (Sloop ts1 ts2) tk0 e le m). *)
  (*   split. *)
  (*   eapply plus_one; unfold step1. *)
  (*   eapply step_skip_loop2. *)
  (*   eapply match_regular_states; eauto. *)
  (*   simpl. rewrite H2. rewrite H4. auto. *)

  (* - (* step_break_loop2 *) *)
  (*   intros; inv MS; monadInv TRS; inv MCONT. *)
  (*   exists (State tf Sskip tk0 e le m). *)
  (*   split. eapply plus_one; unfold step1. *)
  (*   eapply  step_break_loop2. *)
  (*   eapply match_regular_states; eauto. *)

  (* - (* step_return_0 *) *)
  (*   intros; inv MS; monadInv TRS. *)
  (*   exists (Returnstate Values.Vundef (call_cont tk) m'). *)
  (*   split. eapply plus_one; unfold step1. *)
  (*   eapply step_return_0; eauto. rewrite blocks_of_env_preserved. eauto. *)
  (*   eapply match_return_state; eauto. *)
  (*   eapply match_cont_call_cont; eauto. *)
  (* - (* step_return_1 *) *)
  (*   intros; inv MS. *)
  (*   exists (Returnstate v' (call_cont tk) m'). *)
  (*   monadInv TRS. *)
  (*   split. eapply plus_one; unfold step1. *)
  (*   econstructor; eauto. *)
  (*   eapply eval_expr_correct; eauto. *)
  (*   eapply transf_sem_cast_inject; eauto. *)
  (*   rewrite blocks_of_env_preserved. eauto. *)
  (*   eapply match_return_state; eauto. *)
  (*   eapply match_cont_call_cont; eauto. *)

  (* - (* step_skip_call *) *)
  (*   intros; inv MS; monadInv TRS. *)
  (*   econstructor. *)
  (*   split. eapply plus_one; unfold step1. *)
  (*   econstructor. *)
  (*   unfold CStanSemanticsTarget.is_call_cont in H. *)
  (*   assert (is_call_cont tk). inv MCONT; simpl in *; auto. auto. *)
  (*   rewrite blocks_of_env_preserved. eauto. *)
  (*   eapply match_return_state; eauto. *)

  (* - (* step_skip_break_switch *) *)
  (*   intros; inv MS. inv MCONT. *)
  (*   econstructor. *)
  (*   split. eapply plus_one; unfold step1. *)
  (*   econstructor. *)
  (*   destruct H; simpl in *. *)
  (*   monadInv TRF; monadInv TRS; eauto. *)
  (*   monadInv TRF; monadInv TRS; eauto. *)
  (*   eapply match_regular_states; eauto. *)

  (* - (* step_continue_switch *) *)
  (*   intros; inv MS; monadInv TRS; inv MCONT. *)
  (*   exists (State tf Scontinue tk0 e le m). *)
  (*   split. eapply plus_one; unfold step1. *)
  (*   econstructor. *)
  (*   eapply match_regular_states; eauto. *)

  (* - (* step_internal_function *) *)
  (*   intros; inv MS. *)
  (*   monadInv TRFD. *)
  (*   exists (State x x.(fn_body) tk e le m1). *)
  (*   split. eapply plus_one; unfold step1. *)
  (*   eapply step_internal_function. *)
  (*   inversion H. *)
  (*   assert (tr_function f x). { *)
  (*     intros; monadInv EQ. *)
  (*     econstructor; eauto. *)
  (*   }. *)
  (*   inv H4. *)
  (*   econstructor; try (rewrite H7); try (rewrite H8); eauto. *)
  (*   eapply alloc_variables_preserved; eauto. *)
  (*   eapply bind_parameters_preserved; eauto. *)
  (*   monadInv EQ; eauto. *)
  (*   eapply match_regular_states; eauto. *)
  (*   monadInv EQ. eauto. *)

  (* - (* step_external_function *) *)
  (*   intros. inv MS. *)
  (*   monadInv TRFD. *)
  (*   exists (Returnstate vres tk m'). *)
  (*   split. eapply plus_one. eapply step_external_function. eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved. *)
  (*   eapply match_return_state; eauto. *)
  (* - (* step_returnstate *) *)
  (*   intros. inv MS. *)
  (*   inv MCONT. *)
  (*   exists (State tfn Sskip tk0 e (set_opttemp optid v le) m). *)
  (*   split. apply plus_one. eapply step_returnstate. *)
  (*   eapply match_regular_states; eauto. *)
  (*   (***************************************************************************************************) *)
  (* - (* target *) *)
  (*   intros. inv MS. *)
  (*   exists (State f (Starget ta) k e le m (CStanSemanticsTarget.Model (Floats.Float.add ta ta'))). *)
  (*   econstructor. *)
  (*   split. *)
  (*   eapply plus_one. *)
  (*   unfold step1. *)
  (*   inversion TRS. *)
  (*   eapply match_regular_states; eauto. *)
  (*   admit. *)
Admitted.

Lemma function_ptr_translated:
(*   forall m0 *)
(*     (b: block) (f: CStan.fundef) *)
(*     (tgt: AST.ident) *)
(*   (H0 : Genv.init_mem prog = Some m0) *)
(*   (H1 : Genv.find_symbol ge (CStan.prog_main prog) = Some b) *)
(*   (H2 : Genv.find_funct_ptr ge b = Some f) *)
(*   (H3 : CStan.type_of_fundef f = Tfunction Tnil type_int32s AST.cc_default) *)
(*   , Genv.find_funct_ptr ge b = Some f -> *)
(*   exists tf, Genv.find_funct_ptr ge b = Some tf /\ transf_fundef prog tgt f = OK tf. *)
(* Proof. *)
(*   intros. *)
(*   admit. *)
(* Admitted. *)
(*   (* edestruct (Genv.find_funct_ptr_match (proj1 TRANSL)) as (ctx' & tf & A & B & C'); eauto. *) *)
(* (* Qed. *) *)

Lemma initial_states_simulation:
  forall S, CStanSemanticsTarget.initial_state prog S ->
  exists R, CStanSemanticsBackend.initial_state tprog R /\ match_states prog.(prog_target) S R.
Proof.
  intros. inv H.
  (* exploit function_ptr_translated; eauto. *)
  exists (CStanSemanticsBackend.Callstate f nil Kstop m0).
  split.
  eapply CStanSemanticsBackend.initial_state_data_intro; eauto.
  inv H0.
Admitted.
(*   erewrite <- (Genv.init_mem_match (proj1 TRANSL)); eauto. *)
(*   replace (prog_main tprog) with (CStan.prog_main prog). *)
(*   rewrite <- H1. apply symbols_preserved. *)
(*   generalize (match_program_main (proj1 TRANSL)). *)
(*   unfold AST.prog_main. *)
(*   unfold CStan.program_of_program. *)
(*   simpl; eauto. *)
(*   exploit type_of_fundef_preserved; eauto. *)
(*   intro FDTY. rewrite FDTY; eauto. *)
(*   econstructor; eauto. *)
(*   eapply match_Kstop. *)
(* Qed. *)

Lemma final_states_simulation:
  forall S R r i,
  match_states i S R -> CStanSemanticsTarget.final_state S r -> final_state R r.
Proof.
  intros. inv H0. inv H; inv MCONT; constructor.
Qed.

Theorem transf_program_correct:
  forward_simulation (CStanSemanticsTarget.semantics prog) (CStanSemanticsBackend.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact initial_states_simulation.
  intros. (* deal with ordering of additional target ident *)
  eapply final_states_simulation; eauto.
  intros. (* same here *)
  eapply step_simulation; eauto.
Qed.

End PRESERVATION.
