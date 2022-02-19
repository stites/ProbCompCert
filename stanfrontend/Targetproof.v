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

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: Target.transf_program prog = OK tprog.
(* Variable ge: genv. *)

Let ge := globalenv prog.
Let tge := globalenv tprog.

Definition match_temps tgt (le1 le2: temp_env) : Prop :=
  (forall i v, i <> tgt -> le1!i = Some v -> le2!i = Some v).

Definition get_blockstate (bs : CStanSemanticsTarget.block_state) : blocktype :=
match bs with
| CStanSemanticsTarget.Other => BTOther
| CStanSemanticsTarget.Model f => BTModel
end.

(** Matching continuations *)
Inductive match_cont : blocktype -> cont -> cont -> Prop :=
  | match_Kstop: forall bt,
      match_cont bt Kstop Kstop
  | match_Kseq: forall s k ts tk bt ,
      transf_statement (prog_target prog) s = OK ts ->
      match_cont bt k tk ->
      match_cont bt (Kseq s k) (Kseq ts tk)
  | match_Kloop1: forall s1 s2 k ts1 ts2 tk bt,
      transf_statement (prog_target prog) s1 = OK ts1 ->
      transf_statement (prog_target prog) s2 = OK ts2 ->
      match_cont bt k tk ->
      match_cont bt (Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk)
  | match_Kloop2: forall s1 s2 k ts1 ts2 tk bt ,
      transf_statement (prog_target prog) s1 = OK ts1 ->
      transf_statement (prog_target prog) s2 = OK ts2 ->
      match_cont bt k tk ->
      match_cont bt (Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk)
  | match_Kswitch: forall k tk bt ,
      match_cont bt k tk ->
      match_cont bt (Kswitch k) (Kswitch tk)
  | match_Kcall: forall optid fn e le k tfn tle tk bt,
      transf_function (prog_target prog) fn = OK tfn ->
      match_temps (prog_target prog) le tle ->
      bt <> BTModel ->
      match_cont fn.(fn_blocktype) k tk ->
      match_cont bt (Kcall optid fn e le k)
                        (Kcall optid tfn e le tk)
  | match_Kcall_model: forall optid fn e le k tfn tle tk bt,
      transf_function (prog_target prog) fn = OK tfn ->
      match_temps (prog_target prog) le tle ->
      bt = BTModel ->
      match_cont fn.(fn_blocktype) k tk ->
      match_cont bt (Kcall optid fn e le k)
                        (Kseq (Sreturn (Some (Etempvar (prog_target prog) tdouble))) (Kcall optid tfn e le tk))
.

Inductive match_states: CStanSemanticsTarget.state -> CStanSemanticsBackend.state -> Prop :=
  | match_regular_states:
      forall f s k e le m tf ts tk tle bs
      (TRF: transf_function (prog_target prog) f = OK tf)
      (TRS: transf_statement (prog_target prog) s = OK ts)
      (BS_OTHER: bs = CStanSemanticsTarget.Other)
      (BS_SYNC: f.(fn_blocktype) = BTOther)
      (MTMP: match_temps (prog_target prog) le tle)
      (MCONT: match_cont (get_blockstate bs) k tk),
      match_states (CStanSemanticsTarget.State f s k e le m bs)
                   (CStanSemanticsBackend.State tf ts tk e tle m)
  | match_call_state:
      forall fd vargs k m tfd tk bs
      (TRFD: transf_fundef (prog_target prog) fd = OK tfd)
      (* (GET_FN: (exists e tl r cc, fd = External e tl r cc) \/ (exists fn, fd = Internal fn /\ fn.(fn_blocktype) <> BTModel)) *)
      (MCONT: match_cont BTOther k tk),
      match_states (CStanSemanticsTarget.Callstate fd vargs k m bs)
                   (CStanSemanticsBackend.Callstate tfd vargs tk m)
  | match_return_state:
      forall v k m tk bs
      (BS_OTHER: bs = CStanSemanticsTarget.Other)
      (MCONT: match_cont (get_blockstate bs) k tk),
      match_states (CStanSemanticsTarget.Returnstate v k m bs)
                   (CStanSemanticsBackend.Returnstate v tk m)

  | match_regular_states_model:
      forall f s k e le m tf ts tk tle bs ta
      (TRF: transf_function (prog_target prog) f = OK tf)
      (TRS: transf_statement (prog_target prog) s = OK ts)
      (* (TREPI: exists a, transf_etarget_expr (prog_target prog) a = OK (Etempvar (prog_target prog) tdouble)) *)
      (* (TCAST:  Cop.sem_cast (Vfloat ta) tdouble (fn_return tf) m = Some (Vfloat ta)) *)
      (BS_MODEL: bs = CStanSemanticsTarget.Model ta)
      (BS_SYNC: f.(fn_blocktype) = BTModel)
      (TAR_MATCH: le!(prog_target prog) = Some (Vfloat ta)) (* FIXME: needs to access e, but also lookup block in memory*)
      (MTMP: match_temps (prog_target prog) le tle)
      (MCONT: match_cont (get_blockstate bs) k tk),
      match_states (CStanSemanticsTarget.State f s k e le m bs)
                   (CStanSemanticsBackend.State tf ts tk e tle m)
  (* | match_call_state_model: *)
  (*     forall fd vargs k m tfd tk bs fn *)
  (*     (GET_FN: fd = Internal fn) *)
  (*     (BS_OTHER: bs = CStanSemanticsTarget.Other) *)
  (*     (BMODEL: fn.(fn_blocktype) = BTModel) *)
  (*     (TRFD: transf_fundef (prog_target prog) fd = OK tfd) *)
  (*     (* (MCONT: match_cont (get_blockstate bs) k (Kseq (Sreturn (Some (Evar (prog_target prog) tdouble))) tk)), *) *)
  (*     (MCONT: match_cont (get_blockstate bs) k tk), *)
  (*     match_states (CStanSemanticsTarget.Callstate fd vargs k m bs) *)
  (*                  (CStanSemanticsBackend.Callstate tfd vargs tk m) *)
  | match_return_state_model:
      forall v k m tk bs ta
      (BS_MODEL: bs = CStanSemanticsTarget.Model ta)
      (MCONT: match_cont (get_blockstate bs) k tk),
      match_states (CStanSemanticsTarget.Returnstate v k m bs)
                   (CStanSemanticsBackend.Returnstate v tk m)
.

(** * Relational specification of the transformation *)

Definition match_prog (p: CStan.program) (tp: CStan.program) :=
    match_program (fun ctx f tf => Target.transf_fundef p.(prog_target) f = OK tf) eq p tp
 /\ prog_types tp = prog_types p.

Lemma match_temps_assign_tgt:
  forall tgt le te id v,
  tgt = id ->
  match_temps tgt le te ->
  match_temps tgt le (PTree.set id v te).
Proof.
  intros tgt le te id v Heq Hmatch.
  red; intros. rewrite PTree.gsspec in *. subst. destruct (peq i id); auto.
  congruence.
Qed.

Lemma match_temps_assign:
  forall tgt le te id v,
  match_temps tgt le te ->
  match_temps tgt (PTree.set id v le) (PTree.set id v te).
Proof.
  intros tgt le te id v Hmatch.
  red; intros. rewrite PTree.gsspec in *. destruct (peq i id); auto.
Qed.

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

Inductive tr_function: CStan.function -> CStan.function -> Prop :=
  | tr_function_intro: forall f tf,
      (* tr_stmt f.(CStan.fn_body) tf.(fn_body) -> *)
      fn_return tf = CStan.fn_return f ->
      fn_callconv tf = CStan.fn_callconv f ->
      fn_params tf = CStan.fn_params f ->
      fn_vars tf = CStan.fn_vars f ->
      tr_function f tf.

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

Lemma type_of_fundef_preserved:
  forall fd tfd ,
  transf_fundef (prog_target prog) fd = OK tfd -> type_of_fundef tfd = CStan.type_of_fundef fd.
Proof.
  intros. destruct fd; monadInv H; auto.
  monadInv EQ. simpl; unfold type_of_function; simpl. auto.
Qed.

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
  forall e te ,
  Target.transf_etarget_expr (prog_target prog) e = OK te -> typeof e = typeof te.
Proof.
  intro e.
  induction e; intros; inv H;
    (* base cases *)
    try (simpl in *; reflexivity);

    (* cases with inductive hypothesis: Ederef, Eunop, Ebinop *)
    try (monadInv H1;  (* invert our inductive transf_expression *)
         constructor).

    try (destruct (Pos.eqb _ _); monadInv H1; constructor).
Qed.

Lemma eval_expr_correct:
  forall e le tle m a v bs ta
   (TAR: match bs with
         | CStanSemanticsTarget.Other => True
         | CStanSemanticsTarget.Model tv => tle!(prog_target prog) = Some (Vfloat tv)
         end)
   (MTMP: match_temps (prog_target prog) le tle)
   (TRE: Target.transf_etarget_expr (prog_target prog) a = OK ta),
  CStanSemanticsTarget.eval_expr ge e le m bs a v ->
  eval_expr tge e tle m ta v.
Proof.
  intros e le tle m a.
  induction a; intros;
  simpl in TRE; try monadInv TRE; simpl.
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
    destruct (Pos.eqb_spec i (prog_target prog)); try monadInv TRE; [].
    simpl. inv H.
    * constructor; eauto.
    * inversion H0.
  - (* Ederef *)
    inv H.
    inv H0.
    eapply eval_Elvalue.
    eapply eval_Ederef; eauto.
    simpl in *.
    destruct H1.
    eapply deref_loc_value; eauto.
    eapply deref_loc_reference; eauto.
    eapply deref_loc_copy; eauto.
    eapply deref_loc_bitfield; eauto.
  - inv H.
    ** econstructor. eapply IHa; eauto.
       rewrite <-(transf_types_eq a x); eauto.
    ** inversion H0.
  - (* field struct *)
    inv H.

    {
      inv H0.
      simpl in *.
      eapply eval_Elvalue.
      eapply eval_Efield_struct; eauto.
      rewrite (transf_types_eq a x) in H5; eauto.
      assert (SUB: CStan.prog_comp_env prog = ge); eauto; rewrite SUB in *.
      rewrite comp_env_preserved in *; eauto.
      assert (SUB: CStan.prog_comp_env prog = ge); eauto; rewrite SUB in *.
      rewrite comp_env_preserved in *; eauto.
      destruct H1.
      eapply deref_loc_value; eauto.
      eapply deref_loc_reference; eauto.
      eapply deref_loc_copy; eauto.
      eapply deref_loc_bitfield; eauto.
    }
  - (* Eaddrof *)
    inv H.
    inv H0.
  - (* Eunop expressions *)
    inv H.
    econstructor.
    apply (IHa v1 bs x TAR MTMP EQ H4).
    (* Cop.sem_unary_operation is true by transf_types_eq, so long as EQ *)
    rewrite (transf_types_eq a x) in H5; eauto.
    inv H0.

  - (* Ebinop expressions *)
    inv H.                                 (* invert with CStan.eval_Ebinop *)
    (* this also pattern-matches on the invalid CStan.eval_lvalue -- just deal with that now. *)
    2:{ inv H0. }
    econstructor; eauto.
    rewrite (transf_types_eq a1 x ) in H7.
    rewrite (transf_types_eq a2 x0) in H7.
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
  - inv H.
    { inv H0. }
    econstructor. eauto.
Qed.

Lemma eval_lvalue_correct:
  forall e le m a b ofs bf target ta
  (TRE: transf_etarget_expr (prog_target prog) a = OK ta),
  CStanSemanticsTarget.eval_lvalue ge e le m target a b ofs bf -> CStanSemanticsBackend.eval_lvalue tge e le m ta b ofs bf.
Proof.
  intros e le m a.
  induction a; intros; try monadInv TRE; try (inv H).
  - eapply eval_Evar_local; eauto.
  - eapply eval_Evar_global; eauto.
    rewrite symbols_preserved; auto.
  - eapply eval_Ederef.
    eapply eval_expr_correct; eauto.
  - eapply eval_Efield_struct.
    eapply eval_expr_correct; eauto.
    rewrite (transf_types_eq a x) in *; eauto.
    rewrite comp_env_preserved in *; eauto.
    rewrite comp_env_preserved in *; eauto.
Qed.

Lemma types_correct:
  forall e x , transf_etarget_expr (prog_target prog)  e = OK x -> typeof e = typeof x.
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

Lemma match_cont_call_cont:
  forall bt k tk
  (MCONT: match_cont bt k tk)
  (BTOTHER: bt <> BTModel),
  match_cont bt (call_cont k) (call_cont tk) .
Proof.
  induction 1; simpl; auto; intros; econstructor; eauto.
Qed.

Lemma blocks_of_env_preserved:
  forall e, blocks_of_env tge e = blocks_of_env ge e.
Proof.
  intros; unfold blocks_of_env, CStanSemanticsBackend.blocks_of_env.
  unfold block_of_binding, CStanSemanticsBackend.block_of_binding.
  rewrite comp_env_preserved. auto.
Qed.

Lemma transf_sem_cast_inject:
  forall f tf x tx v v' m,
  transf_etarget_expr (prog_target prog) x = OK tx ->
  transf_function (prog_target prog) f = OK tf ->
  Cop.sem_cast v (CStan.typeof x) (CStan.fn_return f) m = Some v' ->
  Cop.sem_cast v (typeof tx) (fn_return tf) m = Some v'.
Proof.
  intros.
  generalize (types_correct _ _ H); intro.
  monadInv H0. simpl in *.
  rewrite <- H2.
  auto.
Qed.

Lemma alloc_variables_preserved:
  forall e m params e' m',
  CStanSemanticsBackend.alloc_variables ge e m params e' m' ->
  alloc_variables tge e m params e' m'.
Proof.
  induction 1; econstructor; eauto. rewrite comp_env_preserved; auto.
Qed.

Lemma bind_parameters_preserved:
  forall e m params args m',
  CStanSemanticsBackend.bind_parameters ge e m params args m' ->
  bind_parameters tge e m params args m'.
Proof.
  induction 1; econstructor; eauto. inv H0.
- eapply assign_loc_value; eauto.
- eapply assign_loc_copy; eauto; rewrite <- comp_env_preserved in *; auto.
Qed.

Lemma eval_exprlist_correct_simple:
  forall env le es tes tys m vs ta
  (TREL: res_mmap (transf_etarget_expr (prog_target prog)) es = OK tes)
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
  generalize (types_correct _ _ EQ); intro.
  rewrite <- H; eauto.
Qed.

(* Lemma seq_both_transf_statement: *)
(*   forall s0 s1 sfin *)
(*   (STARGET: transf_starget_statement s0 = OK s1) *)
(*   (ETARGET: transf_etarget_statement (prog_target prog) s1 = OK sfin) *)
(*   , transf_statement (prog_target prog) s0 = OK sfin. *)
(* Proof. *)
(*   intros. *)
(*   inv STARGET. *)
(*   inv ETARGET. *)
(*   simpl. *)
(*   inv H0. *)
(* Admitted. *)

Lemma step_simulation:
  forall S1 t S2, CStanSemanticsTarget.stepf ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus CStanSemanticsBackend.stepf tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1.

  - (* step_assign *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    + (* other *)
      exists (State tf Sskip tk e le m').
      split.
      eapply plus_one.
      generalize (types_correct _ _ EQ); intro.
      generalize (types_correct _ _ EQ1); intro.
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

    + (* model *)
      exists (State tf Sskip tk e le m').
      split.
      eapply plus_one.
      generalize (types_correct _ _ EQ); intro.
      generalize (types_correct _ _ EQ1); intro.
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

  - (* step_set *)
    simpl; intros; inv MS; simpl in *.
    + (* other *)
      monadInv TRS; monadInv EQ.
      destruct (id =? (prog_target prog))%positive eqn:TEQ.
      (* id = target is impossible *) monadInv EQ2.
      (* otherwise *) inv EQ2. monadInv EQ0.
      econstructor.
      split. eapply plus_one.
      unfold stepf.
      econstructor.
      eapply eval_expr_correct; eauto.
      eapply match_regular_states; eauto.
    + (* other *)
      monadInv TRS; monadInv EQ.
      destruct (id =? (prog_target prog))%positive eqn:TEQ.
      (* id = target is impossible *) monadInv EQ2.
      (* otherwise *) inv EQ2. monadInv EQ0.
      econstructor.
      split. eapply plus_one.
      unfold stepf.
      econstructor.
      eapply eval_expr_correct; eauto.
      eapply match_regular_states_model; eauto.
      apply Pos.eqb_neq in TEQ.
      rewrite PTree.gso; auto.

  - (* call *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    + (* other *)
      exploit eval_expr_correct; eauto; intro.
      exploit eval_exprlist_correct_simple; eauto. intro tvargs.
      exploit functions_translated; eauto. intros [tfd [P Q]].
      econstructor. split. eapply plus_one. eapply step_call with (fd := tfd).
      generalize (types_correct _ _ EQ1); intro TYA. rewrite<-TYA. eauto.
      eauto. eauto. eauto.
      rewrite (type_of_fundef_preserved fd _); eauto.
      eapply match_call_state; eauto.
      econstructor; eauto. simpl. congruence. rewrite BS_SYNC; auto.
    + (* model *)
      exploit eval_expr_correct; eauto; intro.
      exploit eval_exprlist_correct_simple; eauto. intro tvargs.
      exploit functions_translated; eauto. intros [tfd [P Q]].
      econstructor. split. eapply plus_one. eapply step_call with (fd := tfd).
      generalize (types_correct _ _ EQ1); intro TYA. rewrite<-TYA. eauto.
      eauto. eauto. eauto.
      rewrite (type_of_fundef_preserved fd _); eauto.
      eapply match_call_state; eauto.
      econstructor; eauto. simpl. congruence. rewrite BS_SYNC; auto.

  - (* builtin *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    admit.
    admit.

  - (* step_seq *)
    simpl; intros; inv MS; simpl in *.
    + (* other *)
      monadInv TRS.
      monadInv EQ; monadInv EQ0.
      econstructor.
      split.
      eapply plus_one.
      unfold stepf.
      eapply step_seq.
      eapply match_regular_states; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      econstructor.
      unfold transf_statement.
      rewrite EQ; simpl; eauto.
      simpl. eauto.
    + (* model *)
      monadInv TRS.
      monadInv EQ; monadInv EQ0.
      econstructor.
      split.
      eapply plus_one.
      unfold stepf.
      eapply step_seq.
      eapply match_regular_states_model; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      econstructor.
      unfold transf_statement.
      rewrite EQ; simpl; eauto.
      simpl. eauto.

  - (* step_skip_seq *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    + (* other *)
      inv MCONT.
      econstructor.
      split.
      eapply plus_one.
      unfold stepf.
      eapply step_skip_seq.
      eapply match_regular_states; eauto.
    + (* model *)
      inv MCONT.
      econstructor.
      split.
      eapply plus_one.
      unfold stepf.
      eapply step_skip_seq.
      eapply match_regular_states_model; eauto.

  - (* step_continue_seq *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    + (* other *)
      inv MCONT.
      econstructor.
      split.
      eapply plus_one.
      unfold stepf.
      eapply step_continue_seq.
      eapply match_regular_states; eauto.
    + (* model *)
      inv MCONT.
      econstructor.
      split.
      eapply plus_one.
      unfold stepf.
      eapply step_continue_seq.
      eapply match_regular_states_model; eauto.

  - (* step_break_seq *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    + (* other *)
      inv MCONT.
      econstructor.
      split.
      eapply plus_one; unfold stepf.
      eapply step_break_seq.
      eapply match_regular_states; eauto.
    + (* model *)
      inv MCONT.
      econstructor.
      split.
      eapply plus_one; unfold stepf.
      eapply step_break_seq.
      eapply match_regular_states_model; eauto.
  - (* step_ifthenelse *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    + (* other *)
      econstructor.
      split.
      eapply plus_one; unfold stepf.
      econstructor.
      eapply eval_expr_correct; eauto.
      generalize (types_correct _ _ EQ1); intro.
      rewrite <- H1; eauto.
      eapply match_regular_states; eauto.
      destruct b; eauto.
      destruct EQ0; eauto.
      unfold transf_statement.
      rewrite EQ; simpl; eauto.
      unfold transf_statement.
      rewrite EQ2; simpl; eauto.
    + (* model*)
      econstructor.
      split.
      eapply plus_one; unfold stepf.
      econstructor.
      eapply eval_expr_correct; eauto.
      generalize (types_correct _ _ EQ1); intro.
      rewrite <- H1; eauto.
      eapply match_regular_states_model; eauto.
      destruct b; eauto.
      destruct EQ0; eauto.
      unfold transf_statement.
      rewrite EQ; simpl; eauto.
      unfold transf_statement.
      rewrite EQ2; simpl; eauto.

  - (* step_loop *)
    simpl; intros; inv MS; simpl in *; try (monadInv TRS; monadInv EQ; monadInv EQ0).
    + (* other *)
      econstructor.
      split.
      eapply plus_one; unfold stepf.
      eapply step_loop.
      eapply match_regular_states; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      simpl.
      eapply match_Kloop1; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      unfold transf_statement.
      rewrite EQ; simpl; eauto.
    + (* model *)
      econstructor.
      split.
      eapply plus_one; unfold stepf.
      eapply step_loop.
      eapply match_regular_states_model; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      simpl.
      eapply match_Kloop1; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      unfold transf_statement.
      rewrite EQ; simpl; eauto.

  - (* step_skip_or_continue_loop1 *)
    simpl; intros; inv MS; simpl in *; inv MCONT.
    + (* other *)
      monadInv TRS. monadInv H4. monadInv H6.
      destruct H eqn:F.
      econstructor; split.
      eapply plus_one; unfold stepf.
      eapply step_skip_or_continue_loop1.
      monadInv TRF; monadInv EQ; monadInv EQ0; eauto.
      eapply match_regular_states; eauto.
      unfold transf_statement.
      rewrite EQ3; simpl; eauto.
      eapply match_Kloop2; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      unfold transf_statement.
      rewrite EQ3; simpl; eauto.

      econstructor; split.
      eapply plus_one; unfold stepf.
      eapply step_skip_or_continue_loop1.
      monadInv TRF; monadInv EQ; monadInv EQ0; eauto.
      eapply match_regular_states; eauto.
      unfold transf_statement.
      rewrite EQ3; simpl; eauto.
      eapply match_Kloop2; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      unfold transf_statement.
      rewrite EQ3; simpl; eauto.

    + (* model *)
      monadInv TRS. monadInv H4. monadInv H6.
      destruct H eqn:F.
      econstructor; split.
      eapply plus_one; unfold stepf.
      eapply step_skip_or_continue_loop1.
      monadInv TRF; monadInv EQ; monadInv EQ0; eauto.
      eapply match_regular_states_model; eauto.
      unfold transf_statement.
      rewrite EQ3; simpl; eauto.
      eapply match_Kloop2; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      unfold transf_statement.
      rewrite EQ3; simpl; eauto.

      econstructor; split.
      eapply plus_one; unfold stepf.
      eapply step_skip_or_continue_loop1.
      monadInv TRF; monadInv EQ; monadInv EQ0; eauto.
      eapply match_regular_states_model; eauto.
      unfold transf_statement.
      rewrite EQ3; simpl; eauto.
      eapply match_Kloop2; eauto.
      unfold transf_statement.
      rewrite EQ1; simpl; eauto.
      unfold transf_statement.
      rewrite EQ3; simpl; eauto.

  - (* step_break_loop1 *)
    simpl; intros; inv MS; simpl in *; monadInv TRS; monadInv EQ; monadInv EQ0; inv MCONT.
    + (* other *)
      econstructor. split.
      eapply plus_one; unfold stepf.
      eapply step_break_loop1; eauto.
      eapply match_regular_states; eauto.
    + (* model *)
      econstructor. split.
      eapply plus_one; unfold stepf.
      eapply step_break_loop1; eauto.
      eapply match_regular_states_model; eauto.

  - (* step_skip_loop2 *)
    simpl; intros; inv MS; simpl in *; monadInv TRS; monadInv EQ; monadInv EQ0; inv MCONT.
    + (* other *)
      econstructor.
      split.
      eapply plus_one; unfold stepf.
      eapply step_skip_loop2.
      eapply match_regular_states; eauto.
      unfold transf_statement.
      simpl.
      monadInv H3.
      monadInv H5.
      rewrite EQ.
      rewrite EQ1.
      simpl.
      rewrite EQ0.
      rewrite EQ2.
      simpl.
      auto.
    + (* model *)
      econstructor.
      split.
      eapply plus_one; unfold stepf.
      eapply step_skip_loop2.
      eapply match_regular_states_model; eauto.
      unfold transf_statement.
      simpl.
      monadInv H3.
      monadInv H5.
      rewrite EQ.
      rewrite EQ1.
      simpl.
      rewrite EQ0.
      rewrite EQ2.
      simpl.
      auto.

  - (* step_break_loop2 *)
    simpl; intros; inv MS; simpl in *; monadInv TRS; monadInv EQ; monadInv EQ0; inv MCONT.
    + (* other *)
      econstructor.
      split. eapply plus_one; unfold stepf.
      eapply  step_break_loop2.
      eapply match_regular_states; eauto.
    + (* model *)
      econstructor.
      split. eapply plus_one; unfold stepf.
      eapply  step_break_loop2.
      eapply match_regular_states_model; eauto.

  - (* step_return_0 *)
    simpl; intros; inv MS; simpl in *; monadInv TRS; monadInv EQ; monadInv EQ0.
    + (* other *)
      econstructor.
      split. eapply plus_one; unfold stepf.
      eapply step_return_0; eauto. rewrite blocks_of_env_preserved. eauto.
      eapply match_return_state; eauto.
      eapply match_cont_call_cont; eauto.
      simpl. congruence.
    + (* model *)
      econstructor.
      split. eapply plus_one; unfold stepf.
      eapply step_return_0; eauto. rewrite blocks_of_env_preserved. eauto.
      eapply match_return_state_model; eauto.
      eapply match_cont_call_cont; eauto.

  - (* step_return_1 *)
    (* intros; inv MS. *)
    simpl; intros; inv MS; simpl in *.
    + (* other *)
      monadInv TRS. monadInv EQ. monadInv EQ0. monadInv EQ1.
      econstructor.
      split. eapply plus_one; unfold stepf.
      eapply step_return_1.
      eapply eval_expr_correct; eauto.
      eapply transf_sem_cast_inject; eauto.
      rewrite blocks_of_env_preserved. eauto.
      eapply match_return_state; eauto.
      eapply match_cont_call_cont; eauto.
      simpl; congruence.
    + (* model *)
      simpl in *; congruence.

  - (* step_skip_call *)
    simpl; intros; inv MS; simpl in *; monadInv TRS; monadInv EQ; monadInv EQ0.
    + (* other *)
      econstructor.
      split. eapply plus_one; unfold stepf.
      econstructor.
      unfold CStanCont.is_call_cont in H.
      assert (is_call_cont tk). inv MCONT; simpl in *; auto; try congruence.
      exact H2.
      rewrite blocks_of_env_preserved. eauto.
      eapply match_return_state; eauto.
    + (* model *)
      simpl in *; congruence.
  - (* step_skip_call_model *)
    simpl; intros; inv MS; simpl in *; monadInv TRS; monadInv EQ; monadInv EQ0.
    + (* other *)
      simpl in *; congruence.
    + (* model *)
      inv MCONT; simpl in H; destruct H.
      admit. (* we don't want this state to arrive because we don't want to stop the program during the model block *)
      congruence.
      econstructor.
      split.
      * eapply plus_left'; unfold stepf.
        econstructor.
        eapply plus_one; unfold stepf.
        econstructor.
        eapply eval_Etempvar; eauto.
        simpl in *.
        admit. (*I think I need to strengthen this argument*)
        rewrite blocks_of_env_preserved; eauto.
        simpl; congruence.
      * (* eapply match_regular_states_model. *) (* need to pop off this continuation before getting to the match_return_state_model but not sure how *)
        eapply match_return_state_model.
        admit. (* now, I think because I didn't pop off the kcall, we have a funny state here that doesn't make sense *)
        simpl in *.
        eapply match_Kcall; auto.
        congruence.
  - (* step_skip_break_switch *)
    simpl; intros; inv MS; simpl in *; monadInv TRS.
    + (* other *)
       destruct H as [Hskip | Hbreak] eqn:Hboth.
       * (* skip *)
         rewrite Hskip in EQ.
         inversion EQ. rewrite <- H1 in EQ0.
         inversion EQ0.
         inversion MCONT.
         exists (State tf Sskip tk0 e le m).
         split.
         eapply plus_one. unfold stepf.
         eapply step_skip_break_switch.
         auto.
         eapply match_regular_states; simpl in *; eauto.

       * (* break -- how to fold this into a repeat? *)
         rewrite Hbreak in EQ.
         inversion EQ. rewrite <- H1 in EQ0.
         inversion EQ0.
         inversion MCONT.
         exists (State tf Sskip tk0 e le m).
         split.
         eapply plus_one. unfold stepf.
         eapply step_skip_break_switch.
         auto.
         eapply match_regular_states; simpl in *; eauto.
    + (* model *)
       destruct H as [Hskip | Hbreak] eqn:Hboth.
       * (* skip *)
         rewrite Hskip in EQ.
         inversion EQ. rewrite <- H1 in EQ0.
         inversion EQ0.
         inversion MCONT.
         exists (State tf Sskip tk0 e le m).
         split.
         eapply plus_one. unfold stepf.
         eapply step_skip_break_switch.
         auto.
         eapply match_regular_states_model; simpl in *; eauto.

       * (* break -- how to fold this into a repeat? *)
         rewrite Hbreak in EQ.
         inversion EQ. rewrite <- H1 in EQ0.
         inversion EQ0.
         inversion MCONT.
         exists (State tf Sskip tk0 e le m).
         split.
         eapply plus_one. unfold stepf.
         eapply step_skip_break_switch.
         auto.
         eapply match_regular_states_model; simpl in *; eauto.
  - (* step_continue_switch *)
    intros; simpl; intros; inv MS; simpl in *; monadInv TRS; monadInv EQ; monadInv EQ0.
    + (* other *)
      inv MCONT.
      exists (State tf Scontinue tk0 e le m).
      split. eapply plus_one; unfold stepf.
      econstructor.
      eapply match_regular_states; eauto.
    + (* model *)
      inv MCONT.
      exists (State tf Scontinue tk0 e le m).
      split. eapply plus_one; unfold stepf.
      econstructor.
      eapply match_regular_states_model; eauto.

  - (* step_internal_function *)
    (* other-only *)
    intros; simpl; intros; inv MS; simpl in *.
    monadInv TRFD.
    exists (State x (fn_body x) tk e (create_undef_temps (fn_temps x)) m1).
    (* econstructor. *)
    split. eapply plus_one; unfold stepf.
    eapply step_internal_function.
    inversion H.
    assert (tr_function f x).
      intros; monadInv EQ.
      econstructor; eauto.
    inv H4.
    econstructor; try (rewrite H7); try (rewrite H8); monadInv EQ; eauto.
    eapply alloc_variables_preserved; eauto.
    eapply bind_parameters_preserved; eauto.
    assert (create_undef_temps (fn_temps x) = le). {
      (* lost information about (le = create_undef_temps (fn_temps x)) *)
      Search create_undef_temps.
      admit.
    }.
    admit.
    (* rewrite H1. *)
    (* induction (get_blockstate ta). *)
    (* apply get_blockstate in ta. *)
    (* eapply match_regular_states; eauto. *)
    (* admit. (* transf_statement *) *)

    (* admit. (* transf_statement *) *)
    (* (* Search create_undef_temps. *) *)
    (* (* eapply match_regular_states; eauto. *) *)
    (* admit. *)

  - (* step_internal_function_model *)
    (* model-only *)
    intros; simpl; intros; inv MS; simpl in *.
    monadInv TRFD.
    econstructor.
    split. eapply plus_one; unfold stepf.
    eapply step_internal_function.
    inversion H.
    assert (tr_function f x).
      intros; monadInv EQ.
      econstructor; eauto.
    inv H4.
    econstructor; try (rewrite H7); try (rewrite H8); monadInv EQ; eauto.
    eapply alloc_variables_preserved; eauto.
    eapply bind_parameters_preserved; eauto.
    (* lost information about (le = create_undef_temps (fn_temps x)) *)
    (* Search create_undef_temps. *)
    (* eapply match_regular_states_model; eauto. *)
    admit.

  - (* step_external_function *)
    intros.
    destruct ta.
    * (* model *)
      inv MS.
      monadInv TRFD.
      exists (Returnstate vres tk m').
      split. eapply plus_one. eapply step_external_function. eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
      unfold transf_external in EQ.
      induction ef; monadInv EQ; eauto.
      eapply match_return_state_model; eauto.
      simpl.
      auto.
      admit. (* needed to do inversion, maybe on MCONT, much earlier to propagate the block_state *)
    * (* model *)
      inv MS.
      monadInv TRFD.
      exists (Returnstate vres tk m').
      split. eapply plus_one. eapply step_external_function. eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
      unfold transf_external in EQ.
      induction ef; monadInv EQ; eauto.
      eapply match_return_state; eauto.

  - (* step_returnstate *)
    intros. inv MS.
    + (* other *)
      inv MCONT.
      * econstructor. split. apply plus_one. eapply step_returnstate.
        eapply match_regular_states; eauto. (* lost the fn_blocktype too early *)
        admit.
        monadInv H6.
        inversion H8.
        ** (* Kstop *) econstructor.
        ** (* Kseq *) econstructor; eauto.
           (* we don't have a link from match_cont (fn_blocktype f) to (get_blockstate Other)*)
           (* what we need is to loosen get_blockstate to be an inductive type that introduces that bt <> BTModel, I think *)
           admit.
        ** (* Kloop1 *) econstructor; eauto. admit.
        ** (* Kloop2 *) econstructor; eauto. admit.
        ** (* Kswitch *) econstructor; eauto. admit.
        ** (* Kcall *) econstructor; eauto.
        ** (* Kcall to Kseq *) econstructor; eauto. (* here, I think the above solution would fix this as well *) admit.
      * discriminate.
    + (* model *)
      simpl in *.
      inv MCONT.
      * simpl in H7. congruence.
      * simpl in *.
        econstructor. split.
        (* we are in the returnstate of the model. Kcall will continue in the outer function. *)
        (* We want to step through the known continuation of the model's Kseq to get to the  *)
        (* final return of the prog_target prog but we get an error of not finding the correct *)
        eapply plus_left'. unfold stepf.
        admit. (* We need a way to have something like a step_return_1_model otherwise we can't unify *)
                (* stepping through the continuation here, I think. *)
        eapply plus_one. unfold stepf.
        eapply step_returnstate.
        admit. (* everything gets messy here. eapply step_returnstate makes sense, but *)
               (* gives me this ridiculous statement E0 = Eapp _ E0 ... I need to review eventing *)
        eapply match_regular_states_model; eauto.
        admit. (* lost the blocktype f = BTModel *)
        (* Search set_opttemp. *)
        admit. (* hmm... I guess the continuation doesn't add any additional context *)
               (* about setting the ident in this goal.... *)
        simpl in *.
        admit. (* and, again, lost that blocktype f = BTModel *)

        (* (* now deal with the epilouge *) *)
        (* * inv MCONT; simpl in *. *)
        (* ** admit. *)
        (* ** eapply match_regular_states_model; eauto. *)
        (* *** rewrite H6. *)
        (*   admit. (* transf_function (prog_target prog) f = OK ? *) *)
        (* *** admit. (* transf_statement (prog_target prog) Sskip = OK ? *) *)
        (* *** admit. (* fn_blocktype f = BTModel *) *)
        (* *** admit. (* (set_opttemp optid v le) ! (prog_target prog) = Some (Vfloat ta0) *) *)
        (* *** admit. (* (set_opttemp optid v le) ! (prog_target prog) = Some (Vfloat ta0) *) *)
  - (* step_target *)
    intros; inv MS; monadInv TRS; monadInv EQ; monadInv EQ0; simpl in *.
    + (* other *) discriminate.
    + (* model *)
      econstructor. split. eapply plus_left'. unfold stepf.
      eapply step_set.
      eapply eval_expr_correct.
      simpl in *.
      (* need to review the workshop sequences module... *)




      econstructor. split. eapply plus_one. unfold stepf.
      eapply step_set.
      eapply eval_expr_correct.
      admit. (*not sure how to do this one*)
      admit.





      inv H.
      (* step the expression *)
      monadInv EQ.
        eapply step_assign; eauto.
        eapply eval_lvalue_correct; eauto.
        (* assert (eval_lvalue tge e le (Evar (prog_target prog) tdouble )). *)
      (*   eapply eval_expr_correct; eauto. *)
      (* inv H2. *)
      (* eapply assign_loc_value; eauto. *)
      (* eapply assign_loc_copy; try (rewrite comp_env_preserved); eauto. *)
      (* eapply match_regular_states; eauto. *)


      * (* match the states *)

Lemma eval_lvalue_correct:
  forall e le m a b ofs target ta
  (TRE: transf_etarget_expr (prog_target prog) a = OK ta),
  CStanSemanticsTarget.eval_lvalue ge e le m target a b ofs -> CStanSemanticsBackend.eval_lvalue tge e le m ta b ofs.
Proof.
  intros e le m a.
  induction a; intros; monadInv TRE; try (inv H).
  - econstructor. eauto.
  - eapply CStanSemanticsBackend.eval_Evar_global; eauto.
    rewrite symbols_preserved; eauto.
Qed.





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
