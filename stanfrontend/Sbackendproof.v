Require Import Coqlib.
Require Import Smallstep.
Require Import Sbackend.
Require Import CStan.
Require Import Clight.
Require Import Ssemantics.
Require Import Errors.
Require Import Globalenvs.
Require Import Memory.
Require Import Maps.
Require Import Values.
Require Import Linking Ctypes Stypes.
Import Integers.

Section PRESERVATION.

Variable prog: CStan.program.
Variable tprog: Clight.program.
Hypothesis TRANSF: Sbackend.backend prog = OK tprog.
Let ge := CStan.globalenv prog.
Let tge := globalenv tprog.

Inductive match_globalenvs (f: Values.meminj) (bound: Values.block): Prop :=
  | mk_match_globalenvs
      (DOMAIN: forall b, Plt b bound -> f b = Some(b, 0))
      (IMAGE: forall b1 b2 delta, f b1 = Some(b2, delta) -> Plt b2 bound -> b1 = b2)
      (SYMBOLS: forall id b, Genv.find_symbol ge id = Some b -> Plt b bound)
      (FUNCTIONS: forall b fd, Genv.find_funct_ptr ge b = Some fd -> Plt b bound)
      (VARINFOS: forall b gv, Genv.find_var_info ge b = Some gv -> Plt b bound).


(** Matching continuations *)
Inductive match_cont : CStan.cont -> Clight.cont -> Prop :=
  | match_Kstop:
      (* match_globalenvs f hi -> Ple hi bound -> Ple hi tbound -> *)
      match_cont CStan.Kstop Kstop
  | match_Kseq: forall s k ts tk ,
      transf_statement s = OK ts ->
      match_cont k tk ->
      match_cont (CStan.Kseq s k) (Kseq ts tk)
  | match_Kloop1: forall s1 s2 k ts1 ts2 tk ,
      transf_statement s1 = OK ts1 ->
      transf_statement s2 = OK ts2 ->
      match_cont k tk ->
      match_cont (CStan.Kloop1 s1 s2 k) (Kloop1 ts1 ts2 tk)
  | match_Kloop2: forall s1 s2 k ts1 ts2 tk ,
      transf_statement s1 = OK ts1 ->
      transf_statement s2 = OK ts2 ->
      match_cont k tk ->
      match_cont (CStan.Kloop2 s1 s2 k) (Kloop2 ts1 ts2 tk)
  | match_Kswitch: forall k tk ,
      match_cont k tk ->
      match_cont (CStan.Kswitch k) (Kswitch tk)
  | match_Kcall: forall optid fn e le k tfn tk ,
      transf_function fn = OK tfn ->
      (* match_envs f e le m lo hi te tle tlo thi -> *)
      match_cont k tk ->
      (* match_cont_exp a k tk -> *)
      (* Ple hi bound -> Ple thi tbound -> *)
      match_cont (CStan.Kcall optid fn e le k)
                        (Kcall optid tfn e le tk) (* FIXME: also asserting that te = e since this is an identity tranformation *)

(* with match_cont_exp : expr -> CStan.cont -> cont -> Prop := *)
(*   | match_Kseq: forall s ts k tk, *)
(*       transf_statement s ts -> *)
(*       match_cont k tk -> *)
(*       match_cont_exp a (CStan.Kseq s k) (Kseq ts tk) *)
(*   (* | match_Kfor2: forall r s3 s k s' a ts3 ts tk, *) *)
(*   (*     transf_statement s1 ts1 -> *) *)
(*   (*     transf_statement s2 ts2 -> *) *)
(*   (*     match_cont k tk -> *) *)
(*   (*     match_cont_exp a *) *)
(*   (*       (CStan.Kloop2 s1 s2 k) *) *)
(*   (*       (Kseq ts1 *) *)
(*   (*         (Kseq ts (Kloop1 (Ssequence s' ts) ts3 tk))) *) *)
(*   | match_Kswitch1: forall ls k a tls tk, *)
(*       tr_lblstmts ls tls -> *)
(*       match_cont k tk -> *)
(*       match_cont_exp a (CStan.Kswitch ls k) (Kseq (Sswitch a tls) tk) *)
(*   (* | Kstop: cont *) *)
(*   (* | Kseq: statement -> cont -> cont       (**r [Kseq s2 k] = after [s1] in [s1;s2] *) *) *)
(*   (* | Kloop1: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s1] in [Sloop s1 s2] *) *) *)
(*   (* | Kloop2: statement -> statement -> cont -> cont (**r [Kloop1 s1 s2 k] = after [s2] in [Sloop s1 s2] *) *) *)
(*   (* | Kswitch: cont -> cont       (**r catches [break] statements arising out of [switch] *) *) *)

.

Fixpoint Kseqlist (sl: list statement) (k: cont) :=
  match sl with
  | nil => k
  | s :: l => Kseq s (Kseqlist l k)
  end.

Inductive match_states: CStan.state -> Clight.state -> Prop :=
  | match_regular_states:
      forall f s k e le m tf ts tk
      (TRF: transf_function f = OK tf)
      (TRS: transf_statement s = OK ts)
      (MCONT: match_cont k tk),
      match_states (CStan.State f s k e le m)
                   (Clight.State tf ts tk e le m)
  | match_call_state:
      forall fd vargs k m tfd tk
      (TRFD: transf_fundef fd = OK tfd)
      (MCONT: match_cont k tk),
      match_states (CStan.Callstate fd vargs k m)
                   (Clight.Callstate tfd vargs tk m)
  | match_return_state:
      forall v k m tk
      (MCONT: match_cont k tk),
      match_states (CStan.Returnstate v k m)
                   (Clight.Returnstate v tk m).


(* --_-_-_-_---                            --_-_-_-_--- *)
(*     -_-_-     d$$$$"   d$$$$"  d$$$$"       -_-_-    *)
(*      -__-    **$$$"   **$$$"  **$$$"         -__-    *)
(*     _-_      .$$$$$"  .$$$$$" .$$$$$"       _-_      *)
(*    _-           z$"      z$"     z$"       _-        *)
(*    -_          zP       zP      zP         -_        *)
(*     _-        ,"       ,"      ,"           _-       *)
(*                                                      *)
(*      ░█▀▄░█▀█░█▀█░█▀▀░█▀▀░█▀▄░░░▀▀█░█▀█░█▀█░█▀▀      *)
(*      ░█░█░█▀█░█░█░█░█░█▀▀░█▀▄░░░▄▀░░█░█░█░█░█▀▀      *)
(*      ░▀▀░░▀░▀░▀░▀░▀▀▀░▀▀▀░▀░▀░░░▀▀▀░▀▀▀░▀░▀░▀▀▀      *)
(*                      ,---------,         ,---------, *)
(*              ,______;       ,____________;           *)
(*  ,__-----__,-    __'      _;         ,_______,       *)
(* ;__________;________________________________________ *)
(* //////////////////////////////////////////////////// *)

Context {C: Type} {LC: Linker C} {LF: Linker CStan.fundef} {LV: Linker CStan.type}.
Variable ctx: C.
Hypothesis TRANSL:
  match_program_gen
    (fun ctx f tf => Sbackend.transf_fundef f = OK tf)
    (fun cs cl => eq cl (CStan.vd_type cs))
    ctx
    prog
    tprog.

Lemma comp_env_preserved:
  genv_cenv tge = CStan.genv_cenv ge.
Proof.
  unfold tge, ge. destruct prog, tprog; simpl. destruct TRANSL as [_ EQ]. simpl in EQ.
  Admitted.
  (* congruence. *) (* I think congruence requires an instantiation of match_prog *)
(* Qed. *)


(** Relational presentation for the transformation of functions, fundefs, and variables. *)

Inductive tr_function: CStan.function -> Clight.function -> Prop :=
  | tr_function_intro: forall f tf,
      (* tr_stmt f.(CStan.fn_body) tf.(fn_body) -> *)
      fn_return tf = CStan.fn_return f ->
      fn_callconv tf = CStan.fn_callconv f ->
      fn_params tf = CStan.fn_params f ->
      fn_vars tf = CStan.fn_vars f ->
      tr_function f tf.

Inductive tr_fundef: CStan.fundef -> Clight.fundef -> Prop :=
  | tr_internal: forall f tf,
      tr_function f tf ->
      tr_fundef (Internal f) (Internal tf)
  | tr_external: forall ef targs tres cconv,
      tr_fundef (External ef targs tres cconv) (External ef targs tres cconv).

(*      .                       *)
(*    \ | /      All clear!     *)
(*  '-.;;;.-'                   *)
(* -==;;;;;==-                  *)
(* ---------------------------- *)

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma symbols_preserved:
  forall (s: AST.ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSL).

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf (* /\ tr_fundef f tf *)
  .
Proof.
  intros.
  edestruct (Genv.find_funct_match TRANSL) as (ctx' & tf & A & B & C'); eauto.
Qed.

Lemma type_of_fundef_preserved:
  forall fd tfd,
  transf_fundef fd = OK tfd -> type_of_fundef tfd = CStan.type_of_fundef fd.
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
  forall e te,
  transf_expression e = OK te -> CStan.typeof e = Clight.typeof te.
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
  forall e le m a v target ta
  (TRE: transf_expression a = OK ta),
  CStan.eval_expr ge e le m target a v -> Clight.eval_expr tge e le m ta v.
Proof.
  intros e le m a.
  induction a; intros; simpl in TRE; monadInv TRE; simpl.

  (* Econst expressions: *)
  - (* inversion identifies the eval_Econst_* and eval_lvalue as possibilities *)
    inv H. (* apply inversion on our CStan.eval_expr *)
    constructor. (* for eval_Econst_*, apply the corresponding constructor *)
    inv H0.      (* for eval_lvalue, inversion on the new hypothesis shows that the pattern is invalid *)
  - inv H. constructor. inv H0.
  - inv H. constructor. inv H0.
  - inv H; try constructor; inv H0.

  - (* Evar expressions *)
    inv H. (* apply inversion on our CStan.eval_expr, this matches eval_lvalue. *)
    eapply eval_Elvalue.
    (* redo *)

    Focus 2. (* examine the new deref clauses first *)
    inv H1; simpl in *.
    eapply Clight.deref_loc_value; eauto.
    eapply Clight.deref_loc_reference; eauto.
    eapply Clight.deref_loc_copy; eauto.

    inv H0.
    eapply eval_Evar_local. eauto.
    eapply eval_Evar_global; eauto.
    rewrite symbols_preserved. eauto.

  - (* Etempvar expressions *)
    inv H.
    constructor. eauto. inv H0.

  (* Inductive-hypotheses *)

  - (* Ederef expressions *)
    inv H. (* invert with CStan.eval_lvalue... *)
    inv H0. (* but look! we can only load variables. *)

  - (* Eunop expressions *)
    inv H.                               (* invert with CStan.eval_Eunop -- we must additionally show CStan.eval_lvalue is invalid. *)
    econstructor.                        (* apply Clight.eval_Eunop -- we must additionally show Cop.sem_unary_operation *)
    apply (IHa v1 target x EQ H4).       (* Eunop is then shown to be valid by inductive case of it's argument *)
    rewrite (transf_types_eq a x) in H5; eauto. (* Cop.sem_unary_operation is true by transf_types_eq, so long as EQ *)
    inv H0.                                     (* CStan.eval_lvalue is invalid. *)

  - (* Ebinop expressions *)
    inv H.                                 (* invert with CStan.eval_Ebinop *)
    Focus 2. inv H0.                       (* this also pattern-matches on the invalid CStan.eval_lvalue -- just deal with that now. *)
    econstructor.                          (* apply Clight.eval_Ebinop *)
    apply (IHa1 v1 target x EQ H5).        (* The first argument is then proven true by the first inductive case*)
    apply (IHa2 v2 target x0 EQ1 H6).      (* The second argument is then proven true by the second inductive case*)

    rewrite (transf_types_eq a1 x ) in H7. (* we additionally need to show that Cop.sem_binary_operation is true. *)
    rewrite (transf_types_eq a2 x0) in H7.
    rewrite comp_env_preserved.
    eauto.
    eauto.
    eauto.

  (* Two more base cases *)

  - (* Esizeof expressions *)
    inv H.
    rewrite sizeof_equiv.
    apply Clight.eval_Esizeof.
    inv H0.

  - (* Ealignof expressions *)
    inv H.
    rewrite alignof_equiv.
    apply Clight.eval_Ealignof.
    inv H0.
Qed.

Lemma eval_lvalue_correct:
  forall e le m a b ofs target ta
  (TRE: transf_expression a = OK ta),
  CStan.eval_lvalue ge e le m target a b ofs -> Clight.eval_lvalue tge e le m ta b ofs.
Proof.
  intros e le m a.
  induction a; intros; monadInv TRE; try (inv H).
  - econstructor. eauto.
  - eapply eval_Evar_global; eauto.
    rewrite symbols_preserved. auto.
Qed.

Lemma types_correct:
  forall e x, transf_expression e = OK x -> CStan.typeof e = Clight.typeof x.
Proof.
  intro e.
  induction e; intros; simpl in *; monadInv H; simpl; trivial.
Qed.

Lemma match_cont_call_cont:
  forall k tk ,
  match_cont k tk  ->
  match_cont (CStan.call_cont k) (call_cont tk) .
Proof.
  induction 1; simpl; auto; intros; econstructor; eauto.
Qed.

Lemma blocks_of_env_preserved:
  forall e, blocks_of_env tge e = CStan.blocks_of_env ge e.
Proof.
  intros; unfold blocks_of_env, CStan.blocks_of_env.
  unfold block_of_binding, CStan.block_of_binding.
  rewrite comp_env_preserved. auto.
Qed.

Lemma transf_sem_cast_inject:
  forall f tf x tx v v' m,
  transf_expression x = OK tx ->
  Sbackend.transf_function f = OK tf ->
  Cop.sem_cast v (CStan.typeof x) (CStan.fn_return f) m = Some v' ->
  (* exists tv, Cop.sem_cast v (typeof tx) (fn_return tf) m = Some tv. *)
  Cop.sem_cast v (typeof tx) (fn_return tf) m = Some v'.
Proof.
  intros.
  generalize (types_correct _ _ H); intro.
  monadInv H0. simpl in *.
  rewrite <- H2.
  auto.
  (* econstructor; eauto. *)
Qed.

Lemma alloc_variables_preserved:
  forall e m params e' m',
  CStan.alloc_variables ge e m params e' m' ->
  alloc_variables tge e m params e' m'.
Proof.
  induction 1; econstructor; eauto. rewrite comp_env_preserved; auto.
Qed.

Lemma bind_parameters_preserved:
  forall e m params args m',
  CStan.bind_parameters ge e m params args m' ->
  bind_parameters tge e m params args m'.
Proof.
  induction 1; econstructor; eauto. inv H0.
- eapply assign_loc_value; eauto.
- eapply assign_loc_copy; eauto; rewrite <- comp_env_preserved in *; auto.
Qed.

Lemma create_undef_temps_preserved :
  forall f tf,
  transf_function f = OK tf ->
  CStan.create_undef_temps (CStan.fn_temps f) = create_undef_temps (fn_temps tf).
Proof.
  intros. monadInv H; auto.
Qed.

Lemma transf_implies_spec_no_statements :
  forall f tf,
  transf_function f = OK tf ->
  tr_function f tf.
Proof.
  intros.
  monadInv H.
  econstructor; eauto.
Qed.

Lemma eval_exprlist_correct:
  forall env tenv le tle es tes tys m vs ta
  (TREL: transf_expression_list es = OK tes)
  (EVEL: CStan.eval_exprlist ge env le m ta es tys vs),
  eval_exprlist tge tenv tle m tes tys vs.
Proof.
  intros env tenv le tle es.
  induction es; intros.
  monadInv TREL.
  inv EVEL; eauto.
  econstructor.
  monadInv TREL.
  inv EVEL; eauto.
  econstructor.
  eapply eval_expr_correct; eauto.
  admit.
  generalize (types_correct _ _ EQ); intro.
  rewrite <- H; eauto.
  eapply IHes; eauto.
Admitted.

  (* intros le es tes. *)
  (* induction tes; intros. *)
  (* (* unfold transf_expression_list in TREL. *) *)
  (* (* simpl in TREL. *) *)
  (* econstructor.  *)
  (* eapply eval_Enil. *)
  (* unfold  *)
  (*  TREL. *)
  (* intros  *)
  (* unfold transf_expression_list in TREL. *)
  (* Admitted. *)
(*  Lemma eval_simpl_exprlist: *)
(*   forall al tyl vl, *)
(*   eval_exprlist ge e le m al tyl vl -> *)
(*   compat_cenv (addr_taken_exprlist al) cenv -> *)
(*   val_casted_list vl tyl /\ *)
(*   exists tvl, *)
(*      eval_exprlist tge te tle tm (simpl_exprlist cenv al) tyl tvl *)
(*   /\ Val.inject_list f vl tvl. *)
(* Proof. *)

 Lemma match_cont_find_funct:
  forall k tk vf fd tvf
  (* forall f k tk vf fd tvf *)
  (MCONT: match_cont k tk),
  Genv.find_funct ge vf = Some fd ->
  (* Val.inject f vf tvf -> *)
  exists tfd, Genv.find_funct tge tvf = Some tfd /\ transf_fundef fd = OK tfd.
Proof.
  Admitted.
(*   intros. exploit match_cont_globalenv; eauto. intros [bound1 MG]. destruct MG. *)
(*   inv H1; simpl in H0; try discriminate. destruct (Ptrofs.eq_dec ofs1 Ptrofs.zero); try discriminate. *)
(*   subst ofs1. *)
(*   assert (f b1 = Some(b1, 0)). *)
(*     apply DOMAIN. eapply FUNCTIONS; eauto. *)
(*   rewrite H1 in H2; inv H2. *)
(*   rewrite Ptrofs.add_zero. simpl. rewrite dec_eq_true. apply function_ptr_translated; auto. *)
(* Qed. *)
Inductive match_var (e: env) (m: mem) (te: env) (tle: temp_env) (id: AST.ident) : Prop :=
  | match_var_lifted: forall b ty chunk v tv
      (ENV: e!id = Some(b, ty))
      (TENV: te!id = None)
      (MODE: access_mode ty = By_value chunk)
      (LOAD: Mem.load chunk m b 0 = Some v)
      (TLENV: tle!(id) = Some tv),
      match_var e m te tle id
  | match_var_not_lifted: forall b ty b'
      (ENV: e!id = Some(b, ty))
      (TENV: te!id = Some(b', ty)),
      match_var e m te tle id
  | match_var_not_local: forall
      (ENV: e!id = None)
      (TENV: te!id = None),
      match_var e m te tle id.

Record match_envs (e: env) (le: temp_env) (m: mem)
                  (te: env) (tle: temp_env) : Prop :=
  mk_match_envs {
    me_vars:
      forall id, match_var e m te tle id;
    me_temps:
      forall id v,
      le!id = Some v ->
      (exists tv, tle!id = Some tv);
    me_inj:
      forall id1 b1 ty1 id2 b2 ty2, e!id1 = Some(b1, ty1) -> e!id2 = Some(b2, ty2) -> id1 <> id2 -> b1 <> b2;
    me_flat:
      forall id b' ty b,
      te!id = Some(b', ty) -> e!id = Some(b, ty) ;
  }.

Lemma match_envs_set_temp:
  forall e le m te tle id v,
  match_envs e le m te tle ->
  (* Val.inject f v tv -> *)
  (* check_temp cenv id = OK x -> *)
  match_envs e (PTree.set id v le) m te (PTree.set id v tle) .
Proof.
  intros.
  inv H.
  constructor;
  intro.
  generalize (me_vars0 id); intros MV; inv MV.
  generalize (me_vars0 id0); intros MV; inv MV.
  eapply match_var_lifted; eauto. rewrite PTree.gso; eauto.
  generalize (me_inj0 id b ty id0 b0 ty0). intro.
Admitted.
(*   generalize (H ENV ENV0 _). *)

(*   (H ENV ENV0). *)
(*   eapply match_var_not_lifted; eauto. *)
(*   eapply match_var_not_local; eauto. *)
(*   intros. *)
(*   eauto. *)
(*   unfold le. *)
(*   intros. unfold check_temp in H1. *)
(*   destruct (VSet.mem id cenv) eqn:?; monadInv H1. *)
(*   destruct H. constructor; eauto; intros. *)
(* (* vars *) *)
(*   generalize (me_vars0 id0); intros MV; inv MV. *)
(*   eapply match_var_lifted; eauto. rewrite PTree.gso. eauto. congruence. *)
(*   eapply match_var_not_lifted; eauto. *)
(*   eapply match_var_not_local; eauto. *)
(* (* temps *) *)
(*   rewrite PTree.gsspec in *. destruct (peq id0 id). *)
(*   inv H. split. exists tv; auto. intros; congruence. *)
(*   eapply me_temps0; eauto. *)
(* Qed. *)


Lemma match_envs_set_opttemp:
  forall e le m te tle optid v,
  match_envs e le m te tle ->
  (* check_opttemp cenv optid = OK x -> *)
  match_envs e (CStan.set_opttemp optid v le) m te (set_opttemp optid v tle).
Proof.
  intros. unfold set_opttemp. unfold CStan.set_opttemp. destruct optid; eauto.
  eapply match_envs_set_temp; eauto.
Qed.


Lemma step_simulation:
  forall S1 t S2, CStan.stepf ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus Clight.step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1. simpl; intros; inv MS; simpl in *; try (monadInv TRS).

  - (* assign *)
    exists (Clight.State tf Clight.Sskip tk e le m').
    split.
    eapply plus_one.
    generalize (types_correct _ _ EQ); intro.
    generalize (types_correct _ _ EQ1); intro.
    rewrite H3 in *.
    rewrite H4 in *.
    unfold step1.
    eapply step_assign; eauto.
    eapply eval_lvalue_correct; eauto.
    eapply eval_expr_correct; eauto.
    inv H2.
    eapply assign_loc_value; eauto.
    eapply assign_loc_copy; try (rewrite comp_env_preserved); eauto.
    eapply match_regular_states; eauto.

  - (* set *)
    intros.
    inv MS.
    econstructor.
    (* exists (Clight.State tf Clight.Sskip tk e le m). *)
    monadInv TRS.
    split. eapply plus_one. unfold step1.
    econstructor.
    eapply eval_expr_correct; eauto.
    eapply match_regular_states; eauto.

  - (* call *)
    intros; inv MS.
    monadInv TRS.
    exploit eval_expr_correct; eauto; intro.
    exploit eval_exprlist_correct; eauto. intro tvargs.
    exploit match_cont_find_funct; eauto. intros [tfd [P Q]].
    econstructor. split. eapply plus_one. eapply step_call with (fd := tfd).
    generalize (types_correct _ _ EQ); intro TYA. rewrite<-TYA. eauto.
    eauto. eauto. eauto.
    rewrite (type_of_fundef_preserved fd); eauto.
    eapply match_call_state; eauto.
    econstructor; eauto.

  - (* builtin *)
    intros; inv MS.
    monadInv TRS.
    exists (State tf Sskip tk e (set_opttemp optid vres le) m').
    split. eapply plus_one. unfold step1.
    eapply step_builtin.
    eapply eval_exprlist_correct; eauto.
    eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
    eapply match_regular_states; eauto.
  - (* sequence seq *)
    intros.
    inv MS; monadInv TRS.
    exists (State tf x (Kseq x0 tk) e le m).
    split.
    eapply plus_one.
    unfold step1.
    eapply step_seq.
    eapply match_regular_states; eauto.
    econstructor; eauto.
  - (* skip sequence *)
    intros.
    inv MS; monadInv TRS.
    inv MCONT.
    (* econstructor. *)
    exists (State tf ts tk0 e le m).
    split.
    eapply plus_one.
    unfold step1.
    eapply step_skip_seq.
    eapply match_regular_states; eauto.
  - (* continue sequence *)
    intros; inv MS; monadInv TRS.
    inv MCONT.
    exists (State tf Scontinue tk0 e le m).
    split.
    eapply plus_one.
    unfold step1.
    eapply step_continue_seq.
    eapply match_regular_states; eauto.
  - (* break sequence *)
    intros; inv MS; monadInv TRS.
    inv MCONT.
    exists (State tf Sbreak tk0 e le m).
    split.
    eapply plus_one; unfold step1.
    eapply step_break_seq.
    eapply match_regular_states; eauto.
  - (* if then else *)
    intros; inv MS; monadInv TRS.
    econstructor.
    split.
    eapply plus_one; unfold step1.
    econstructor.
    eapply eval_expr_correct; eauto.
    generalize (types_correct _ _ EQ); intro.
    rewrite <- H1; eauto.
    eapply match_regular_states; eauto.
    destruct b; eauto.
  - (* step_loop *)
    intros; inv MS; monadInv TRS.
    exists (State tf x (Kloop1 x x0 tk) e le m).
    split.
    eapply plus_one; unfold step1.
    eapply step_loop.
    eapply match_regular_states; eauto.
    eapply match_Kloop1; eauto.
  - (* step_skip_or_continue_loop1 *)
    intros. inv MS; inv MCONT; destruct H;

    repeat (
      econstructor; split;
      try (eapply plus_one; unfold step1;
        eapply step_skip_or_continue_loop1;
        monadInv TRF; monadInv TRS; eauto);
      eapply match_regular_states; eauto; eapply match_Kloop2; eauto
    ).

  - (* step_break_loop1 *)
    intros; inv MS; monadInv TRS; inv MCONT.
    econstructor. split.
    eapply plus_one; unfold step1.
    eapply step_break_loop1; eauto.
    eapply match_regular_states; eauto.
  - (* step_skip_loop2 *)
    intros; inv MS; monadInv TRS; inv MCONT.
    exists (State tf (Sloop ts1 ts2) tk0 e le m).
    split.
    eapply plus_one; unfold step1.
    eapply step_skip_loop2.
    eapply match_regular_states; eauto.
    simpl. rewrite H2. rewrite H4. auto.

  - (* step_break_loop2 *)
    intros; inv MS; monadInv TRS; inv MCONT.
    exists (State tf Sskip tk0 e le m).
    split. eapply plus_one; unfold step1.
    eapply  step_break_loop2.
    eapply match_regular_states; eauto.

  - (* step_return_0 *)
    intros; inv MS; monadInv TRS.
    exists (Returnstate Values.Vundef (call_cont tk) m').
    split. eapply plus_one; unfold step1.
    eapply step_return_0; eauto. rewrite blocks_of_env_preserved. eauto.
    eapply match_return_state; eauto.
    eapply match_cont_call_cont; eauto.
  - (* step_return_1 *)
    intros; inv MS.
    exists (Returnstate v' (call_cont tk) m').
    monadInv TRS.
    split. eapply plus_one; unfold step1.
    econstructor; eauto.
    eapply eval_expr_correct; eauto.
    eapply transf_sem_cast_inject; eauto.
    rewrite blocks_of_env_preserved. eauto.
    eapply match_return_state; eauto.
    eapply match_cont_call_cont; eauto.

  - (* step_skip_call *)
    intros; inv MS; monadInv TRS.
    econstructor.
    split. eapply plus_one; unfold step1.
    econstructor.
    unfold CStan.is_call_cont in H.
    assert (is_call_cont tk). inv MCONT; simpl in *; auto. auto.
    rewrite blocks_of_env_preserved. eauto.
    eapply match_return_state; eauto.

  - (* step_skip_break_switch *)
    intros; inv MS. inv MCONT.
    econstructor.
    split. eapply plus_one; unfold step1.
    econstructor.
    destruct H; simpl in *.
    monadInv TRF.
    monadInv TRS.
    eauto.
    monadInv TRF.
    monadInv TRS.
    eauto.
    eapply match_regular_states; eauto.

  - (* step_continue_switch *)
    intros; inv MS; monadInv TRS; inv MCONT.
    exists (State tf Scontinue tk0 e le m).
    split. eapply plus_one; unfold step1.
    econstructor.
    eapply match_regular_states; eauto.

  - (* step_internal_function *)
    intros; inv MS.
    monadInv TRFD.
    exists (State x x.(fn_body) tk e le m1).
    split. eapply plus_one; unfold step1.
    eapply step_internal_function.
    inversion H.
    assert (tr_function f x). {
      eapply transf_implies_spec_no_statements; eauto.
    }.
    inv H4.
    econstructor; try (rewrite H7); try (rewrite H8); eauto.
    eapply alloc_variables_preserved; eauto.
    eapply bind_parameters_preserved; eauto.
    eapply create_undef_temps_preserved; eauto.
    eapply match_regular_states; eauto.
    monadInv EQ. eauto.

  - (* step_external_function *)
    intros. inv MS.
    monadInv TRFD.
    exists (Returnstate vres tk m').
    split. eapply plus_one. eapply step_external_function. eapply Events.external_call_symbols_preserved; eauto. apply senv_preserved.
    eapply match_return_state; eauto.
  - (* step_returnstate *)
    intros. inv MS.
    inv MCONT.
    exists (State tfn Sskip tk0 e (set_opttemp optid v le) m).
    split. apply plus_one. eapply step_returnstate.
    eapply match_regular_states; eauto.
Qed.

Lemma initial_states_simulation:
  forall S, CStan.initial_state prog S ->
  exists R, Clight.initial_state tprog R /\ match_states S R.
Proof.
  intros.
Admitted.

Lemma final_states_simulation:
  forall S R r,
  match_states S R -> CStan.final_state S r -> Clight.final_state R r.
Proof.
Admitted.


Theorem transf_program_correct:
  forward_simulation (CStan.semantics prog) (Clight.semantics1 tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved.
  eexact initial_states_simulation.
  eexact final_states_simulation.
  eexact step_simulation.
Qed.

End PRESERVATION.

