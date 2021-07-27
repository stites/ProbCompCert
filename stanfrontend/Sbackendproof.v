Require Import Coqlib.
Require Import Smallstep.
Require Import Sbackend.
Require Import CStan.
Require Import Clight.
Require Import Ssemantics.
Require Import Errors.
Require Import Globalenvs.
Require Import Memory.
Require Import Linking Ctypes Stypes.
Import Integers.

Section PRESERVATION.

Variable prog: CStan.program.
Variable tprog: Clight.program.
Hypothesis TRANSF: Sbackend.backend prog = OK tprog.
Let ge := CStan.globalenv prog.
Let tge := globalenv tprog.

Variable match_cont: CStan.cont -> Clight.cont -> Prop.

Inductive match_states: CStan.state -> Clight.state -> Prop :=
  | match_regular_states:
      forall f s k e le m t tf ts tk
      (TRF: transf_function f = OK tf)
      (TRS: transf_statement s = OK ts)
      (MCONT: match_cont k tk),
      match_states (CStan.State f s k e le m t)
                   (Clight.State tf ts tk e le m)
  | match_call_state:
      forall fd vargs k m t tfd tk i
      (TRFD: transf_fundef i fd = OK tfd)
      (MCONT: match_cont k tk),
      match_states (CStan.Callstate fd vargs k m t)
                   (Clight.Callstate tfd vargs tk m)
  | match_return_state:
      forall v k m t tk
      (MCONT: match_cont k tk),
      match_states (CStan.Returnstate v k m t)
                   (Clight.Returnstate v tk m).

(** ** Top-level translation *)

(** The "top-level" translation is equivalent to [tr_expr] above
  for source terms.  It brings additional flexibility in the matching
  between Csyntax values and Cminor expressions: in the case of
  [tr_expr], the Cminor expression must not depend on memory,
  while in the case of [tr_top] it can depend on the current memory
  state. *)

Section TR_TOP.

Variable e: CStan.env.
Variable le: CStan.temp_env.
Variable m: mem.

Variable ta: Floats.float. (* target *)

(* Inductive tr_expr: temp_env -> CStan.expr -> expr -> list AST.ident -> Prop := *)
(*   | tr_var: forall le id ty tmp, *)
(*       tr_expr le (CStan.Evar id ty) (Evar id ty) tmp *)
(*   | tr_deref: forall le e1 ty sl1 a1 tmp, *)
(*       tr_expr le e1 sl1 a1 tmp -> *)
(*       tr_expr le (CStan.Ederef e1 ty) *)
(*               (sl1 ++ final (Ederef' a1 ty)) (Ederef' a1 ty) tmp *)
(*   | tr_field: forall le dst e1 f ty sl1 a1 tmp, *)
(*       tr_expr le e1 sl1 a1 tmp -> *)
(*       tr_expr le (CStan.Efield e1 f ty) *)
(*               (sl1 ++ final dst (Efield a1 f ty)) (Efield a1 f ty) tmp *)
(* (*   | tr_val_effect: forall le v ty any tmp, *) *)
(* (*       tr_expr le For_effects (CStan.Eval v ty) nil any tmp *) *)
(* (*   | tr_val_value: forall le v ty a tmp, *) *)
(* (*       typeof a = ty -> *) *)
(* (*       (forall tge e le' m, *) *)
(* (*          (forall id, In id tmp -> le'!id = le!id) -> *) *)
(* (*          eval_expr tge e le' m a v) -> *) *)
(* (*       tr_expr le For_val (CStan.Eval v ty) *) *)
(* (*                            nil a tmp *) *)
(* (*   | tr_val_set: forall le sd v ty a any tmp, *) *)
(* (*       typeof a = ty -> *) *)
(* (*       (forall tge e le' m, *) *)
(* (*          (forall id, In id tmp -> le'!id = le!id) -> *) *)
(* (*          eval_expr tge e le' m a v) -> *) *)
(* (*       tr_expr le (For_set sd) (CStan.Eval v ty) *) *)
(* (*                    (do_set sd a) any tmp *) *)
(* (*   | tr_sizeof: forall le dst ty' ty tmp, *) *)
(* (*       tr_expr le dst (CStan.Esizeof ty' ty) *) *)
(* (*                    (final dst (Esizeof ty' ty)) *) *)
(* (*                    (Esizeof ty' ty) tmp *) *)
(* (*   | tr_alignof: forall le dst ty' ty tmp, *) *)
(* (*       tr_expr le dst (CStan.Ealignof ty' ty) *) *)
(* (*                    (final dst (Ealignof ty' ty)) *) *)
(* (*                    (Ealignof ty' ty) tmp *) *)
(* (*   | tr_valof: forall le dst e1 ty tmp sl1 a1 tmp1 sl2 a2 tmp2, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_rvalof (CStan.typeof e1) a1 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       tr_expr le dst (CStan.Evalof e1 ty) *) *)
(* (*                     (sl1 ++ sl2 ++ final dst a2) *) *)
(* (*                     a2 tmp *) *)
(* (*   | tr_addrof: forall le dst e1 ty tmp sl1 a1, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp -> *) *)
(* (*       tr_expr le dst (Csyntax.Eaddrof e1 ty) *) *)
(* (*                    (sl1 ++ final dst (Eaddrof' a1 ty)) *) *)
(* (*                    (Eaddrof' a1 ty) tmp *) *)
(* (*   | tr_unop: forall le dst op e1 ty tmp sl1 a1, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp -> *) *)
(* (*       tr_expr le dst (Csyntax.Eunop op e1 ty) *) *)
(* (*                    (sl1 ++ final dst (Eunop op a1 ty)) *) *)
(* (*                    (Eunop op a1 ty) tmp *) *)
(* (*   | tr_binop: forall le dst op e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le For_val e2 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       tr_expr le dst (Csyntax.Ebinop op e1 e2 ty) *) *)
(* (*                    (sl1 ++ sl2 ++ final dst (Ebinop op a1 a2 ty)) *) *)
(* (*                    (Ebinop op a1 a2 ty) tmp *) *)
(* (*   | tr_cast_effects: forall le e1 ty sl1 a1 any tmp, *) *)
(* (*       tr_expr le For_effects e1 sl1 a1 tmp -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Ecast e1 ty) *) *)
(* (*                    sl1 *) *)
(* (*                    any tmp *) *)
(* (*   | tr_cast_val: forall le dst e1 ty sl1 a1 tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp -> *) *)
(* (*       tr_expr le dst (Csyntax.Ecast e1 ty) *) *)
(* (*                    (sl1 ++ final dst (Ecast a1 ty)) *) *)
(* (*                    (Ecast a1 ty) tmp *) *)
(* (*   | tr_seqand_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> In t tmp -> *) *)
(* (*       tr_expr le For_val (Csyntax.Eseqand e1 e2 ty) *) *)
(* (*                     (sl1 ++ makeif a1 (makeseq sl2) *) *)
(* (*                                       (Sset t (Econst_int Int.zero ty)) :: nil) *) *)
(* (*                     (Etempvar t ty) tmp *) *)
(* (*   | tr_seqand_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le For_effects e2 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Eseqand e1 e2 ty) *) *)
(* (*                     (sl1 ++ makeif a1 (makeseq sl2) Sskip :: nil) *) *)
(* (*                     any tmp *) *)
(* (*   | tr_seqand_set: forall le sd e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> In (sd_temp sd) tmp -> *) *)
(* (*       tr_expr le (For_set sd) (Csyntax.Eseqand e1 e2 ty) *) *)
(* (*                     (sl1 ++ makeif a1 (makeseq sl2) *) *)
(* (*                                       (makeseq (do_set sd (Econst_int Int.zero ty))) :: nil) *) *)
(* (*                     any tmp *) *)
(* (*   | tr_seqor_val: forall le e1 e2 ty sl1 a1 tmp1 t sl2 a2 tmp2 tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le (For_set (sd_seqbool_val t ty)) e2 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> In t tmp -> *) *)
(* (*       tr_expr le For_val (Csyntax.Eseqor e1 e2 ty) *) *)
(* (*                     (sl1 ++ makeif a1 (Sset t (Econst_int Int.one ty)) *) *)
(* (*                                       (makeseq sl2) :: nil) *) *)
(* (*                     (Etempvar t ty) tmp *) *)
(* (*   | tr_seqor_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le For_effects e2 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Eseqor e1 e2 ty) *) *)
(* (*                     (sl1 ++ makeif a1 Sskip (makeseq sl2) :: nil) *) *)
(* (*                     any tmp *) *)
(* (*   | tr_seqor_set: forall le sd e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le (For_set (sd_seqbool_set ty sd)) e2 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> In (sd_temp sd) tmp -> *) *)
(* (*       tr_expr le (For_set sd) (Csyntax.Eseqor e1 e2 ty) *) *)
(* (*                     (sl1 ++ makeif a1 (makeseq (do_set sd (Econst_int Int.one ty))) *) *)
(* (*                                       (makeseq sl2) :: nil) *) *)
(* (*                     any tmp *) *)
(* (*   | tr_condition_val: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le (For_set (SDbase ty ty t)) e2 sl2 a2 tmp2 -> *) *)
(* (*       tr_expr le (For_set (SDbase ty ty t)) e3 sl3 a3 tmp3 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp3 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp ->  incl tmp3 tmp -> In t tmp -> *) *)
(* (*       tr_expr le For_val (Csyntax.Econdition e1 e2 e3 ty) *) *)
(* (*                       (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil) *) *)
(* (*                       (Etempvar t ty) tmp *) *)
(* (*   | tr_condition_effects: forall le e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le For_effects e2 sl2 a2 tmp2 -> *) *)
(* (*       tr_expr le For_effects e3 sl3 a3 tmp3 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp3 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Econdition e1 e2 e3 ty) *) *)
(* (*                        (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil) *) *)
(* (*                        any tmp *) *)
(* (*   | tr_condition_set: forall le sd t e1 e2 e3 ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le (For_set (SDcons ty ty t sd)) e2 sl2 a2 tmp2 -> *) *)
(* (*       tr_expr le (For_set (SDcons ty ty t sd)) e3 sl3 a3 tmp3 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp3 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> In t tmp -> *) *)
(* (*       tr_expr le (For_set sd) (Csyntax.Econdition e1 e2 e3 ty) *) *)
(* (*                        (sl1 ++ makeif a1 (makeseq sl2) (makeseq sl3) :: nil) *) *)
(* (*                        any tmp *) *)
(* (*   | tr_assign_effects: forall le e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le For_val e2 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Eassign e1 e2 ty) *) *)
(* (*                       (sl1 ++ sl2 ++ make_assign a1 a2 :: nil) *) *)
(* (*                       any tmp *) *)
(* (*   | tr_assign_val: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 t tmp ty1 ty2, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le For_val e2 sl2 a2 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       In t tmp -> ~In t tmp1 -> ~In t tmp2 -> *) *)
(* (*       ty1 = Csyntax.typeof e1 -> *) *)
(* (*       ty2 = Csyntax.typeof e2 -> *) *)
(* (*       tr_expr le dst (Csyntax.Eassign e1 e2 ty) *) *)
(* (*                    (sl1 ++ sl2 ++ *) *)
(* (*                     Sset t (Ecast a2 ty1) :: *) *)
(* (*                     make_assign a1 (Etempvar t ty1) :: *) *)
(* (*                     final dst (Etempvar t ty1)) *) *)
(* (*                    (Etempvar t ty1) tmp *) *)
(* (*   | tr_assignop_effects: forall le op e1 e2 tyres ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le For_val e2 sl2 a2 tmp2 -> *) *)
(* (*       ty1 = Csyntax.typeof e1 -> *) *)
(* (*       tr_rvalof ty1 a1 sl3 a3 tmp3 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Eassignop op e1 e2 tyres ty) *) *)
(* (*                       (sl1 ++ sl2 ++ sl3 ++ make_assign a1 (Ebinop op a3 a2 tyres) :: nil) *) *)
(* (*                       any tmp *) *)
(* (*   | tr_assignop_val: forall le dst op e1 e2 tyres ty sl1 a1 tmp1 sl2 a2 tmp2 sl3 a3 tmp3 t tmp ty1, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le For_val e2 sl2 a2 tmp2 -> *) *)
(* (*       tr_rvalof ty1 a1 sl3 a3 tmp3 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> list_disjoint tmp1 tmp3 -> list_disjoint tmp2 tmp3 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> incl tmp3 tmp -> *) *)
(* (*       In t tmp -> ~In t tmp1 -> ~In t tmp2 -> ~In t tmp3 -> *) *)
(* (*       ty1 = Csyntax.typeof e1 -> *) *)
(* (*       tr_expr le dst (Csyntax.Eassignop op e1 e2 tyres ty) *) *)
(* (*                    (sl1 ++ sl2 ++ sl3 ++ *) *)
(* (*                     Sset t (Ecast (Ebinop op a3 a2 tyres) ty1) :: *) *)
(* (*                     make_assign a1 (Etempvar t ty1) :: *) *)
(* (*                     final dst (Etempvar t ty1)) *) *)
(* (*                    (Etempvar t ty1) tmp *) *)
(* (*   | tr_postincr_effects: forall le id e1 ty ty1 sl1 a1 tmp1 sl2 a2 tmp2 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_rvalof ty1 a1 sl2 a2 tmp2 -> *) *)
(* (*       ty1 = Csyntax.typeof e1 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Epostincr id e1 ty) *) *)
(* (*                       (sl1 ++ sl2 ++ make_assign a1 (transl_incrdecr id a2 ty1) :: nil) *) *)
(* (*                       any tmp *) *)
(* (*   | tr_postincr_val: forall le dst id e1 ty sl1 a1 tmp1 t ty1 tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       incl tmp1 tmp -> In t tmp -> ~In t tmp1 -> *) *)
(* (*       ty1 = Csyntax.typeof e1 -> *) *)
(* (*       tr_expr le dst (Csyntax.Epostincr id e1 ty) *) *)
(* (*                    (sl1 ++ make_set t a1 :: *) *)
(* (*                     make_assign a1 (transl_incrdecr id (Etempvar t ty1) ty1) :: *) *)
(* (*                     final dst (Etempvar t ty1)) *) *)
(* (*                    (Etempvar t ty1) tmp *) *)
(* (*   | tr_comma: forall le dst e1 e2 ty sl1 a1 tmp1 sl2 a2 tmp2 tmp, *) *)
(* (*       tr_expr le For_effects e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_expr le dst e2 sl2 a2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       tr_expr le dst (Csyntax.Ecomma e1 e2 ty) (sl1 ++ sl2) a2 tmp *) *)
(* (*   | tr_call_effects: forall le e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 any tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_exprlist le el2 sl2 al2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Ecall e1 el2 ty) *) *)
(* (*                    (sl1 ++ sl2 ++ Scall None a1 al2 :: nil) *) *)
(* (*                    any tmp *) *)
(* (*   | tr_call_val: forall le dst e1 el2 ty sl1 a1 tmp1 sl2 al2 tmp2 t tmp, *) *)
(* (*       dst <> For_effects -> *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_exprlist le el2 sl2 al2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> In t tmp -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       tr_expr le dst (Csyntax.Ecall e1 el2 ty) *) *)
(* (*                    (sl1 ++ sl2 ++ Scall (Some t) a1 al2 :: final dst (Etempvar t ty)) *) *)
(* (*                    (Etempvar t ty) tmp *) *)
(* (*   | tr_builtin_effects: forall le ef tyargs el ty sl al tmp1 any tmp, *) *)
(* (*       tr_exprlist le el sl al tmp1 -> *) *)
(* (*       incl tmp1 tmp -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Ebuiltin ef tyargs el ty) *) *)
(* (*                    (sl ++ Sbuiltin None ef tyargs al :: nil) *) *)
(* (*                    any tmp *) *)
(* (*   | tr_builtin_val: forall le dst ef tyargs el ty sl al tmp1 t tmp, *) *)
(* (*       dst <> For_effects -> *) *)
(* (*       tr_exprlist le el sl al tmp1 -> *) *)
(* (*       In t tmp -> incl tmp1 tmp -> *) *)
(* (*       tr_expr le dst (Csyntax.Ebuiltin ef tyargs el ty) *) *)
(* (*                    (sl ++ Sbuiltin (Some t) ef tyargs al :: final dst (Etempvar t ty)) *) *)
(* (*                    (Etempvar t ty) tmp *) *)
(* (*   | tr_paren_val: forall le e1 tycast ty sl1 a1 t tmp, *) *)
(* (*       tr_expr le (For_set (SDbase tycast ty t)) e1 sl1 a1 tmp -> *) *)
(* (*       In t tmp -> *) *)
(* (*       tr_expr le For_val (Csyntax.Eparen e1 tycast ty) *) *)
(* (*                        sl1 *) *)
(* (*                        (Etempvar t ty) tmp *) *)
(* (*   | tr_paren_effects: forall le e1 tycast ty sl1 a1 tmp any, *) *)
(* (*       tr_expr le For_effects e1 sl1 a1 tmp -> *) *)
(* (*       tr_expr le For_effects (Csyntax.Eparen e1 tycast ty) sl1 any tmp *) *)
(* (*   | tr_paren_set: forall le t sd e1 tycast ty sl1 a1 tmp any, *) *)
(* (*       tr_expr le (For_set (SDcons tycast ty t sd)) e1 sl1 a1 tmp -> *) *)
(* (*       In t tmp -> *) *)
(* (*       tr_expr le (For_set sd) (Csyntax.Eparen e1 tycast ty) sl1 any tmp *) *)

(* (* with tr_exprlist: temp_env -> Csyntax.exprlist -> list statement -> list expr -> list ident -> Prop := *) *)
(* (*   | tr_nil: forall le tmp, *) *)
(* (*       tr_exprlist le Csyntax.Enil nil nil tmp *) *)
(* (*   | tr_cons: forall le e1 el2 sl1 a1 tmp1 sl2 al2 tmp2 tmp, *) *)
(* (*       tr_expr le For_val e1 sl1 a1 tmp1 -> *) *)
(* (*       tr_exprlist le el2 sl2 al2 tmp2 -> *) *)
(* (*       list_disjoint tmp1 tmp2 -> *) *)
(* (*       incl tmp1 tmp -> incl tmp2 tmp -> *) *)
(* (*       tr_exprlist le (Csyntax.Econs e1 el2) (sl1 ++ sl2) (a1 :: al2) tmp *) *)
(*   . *)


Inductive tr_top: CStan.expr -> list statement -> expr -> list AST.ident -> Prop :=
  | tr_top_val_int: forall i ty a tmp,
      typeof a = ty -> eval_expr tge e le m a (Values.Vint i) ->
      tr_top (CStan.Econst_int i ty) nil a tmp
   | tr_top_val_long: forall i ty a tmp,
      typeof a = ty -> eval_expr tge e le m a (Values.Vlong i) ->
      tr_top (CStan.Econst_int (Int.repr (Int64.unsigned i)) ty) nil a tmp
  (* ... more? ... *)

  | tr_top_val_float: forall f ty a tmp,
      typeof a = ty -> eval_expr tge e le m a (Values.Vfloat f) ->
      tr_top (CStan.Econst_float f ty) nil a tmp

  (* missing: *)
  (* | Vundef: val *)
  (* | Vsingle: float32 -> val *)
  (* | Vptr: block -> ptrofs -> val. *)

  (* also the recursive call: *)
  (* | tr_top_base: forall r sl a tmp, *)
  (*     tr_expr le dst r sl a tmp -> *)
  (*     tr_top r sl a tmp. *)
  .

End TR_TOP.


Lemma tr_expression: CStan.expr -> Clight.statement -> Clight.expr -> Prop.
Admitted.

Lemma tr_stmt: CStan.statement -> statement -> Prop.
Admitted.
  (* | tr_skip: *)
  (*     tr_stmt CStan.Sskip Sskip *)
  (* | tr_seq: forall s1 s2 ts1 ts2, *)
  (*     tr_stmt s1 ts1 -> tr_stmt s2 ts2 -> *)
  (*     tr_stmt (CStan.Ssequence s1 s2) (Ssequence ts1 ts2) *)
  (* | tr_ifthenelse_empty: forall r s' a, *)
  (*     tr_expression r s' a -> *)
  (*     tr_stmt (CStan.Sifthenelse r CStan.Sskip CStan.Sskip) (Ssequence s' Sskip) *)
  (* | tr_ifthenelse: forall r s1 s2 s' a ts1 ts2, *)
  (*     tr_expression r s' a -> *)
  (*     tr_stmt s1 ts1 -> tr_stmt s2 ts2 -> *)
  (*     tr_stmt (CStan.Sifthenelse r s1 s2) (Ssequence s' (Sifthenelse a ts1 ts2)) *)
  (* | tr_loop: forall r s1 s' ts1, *)
  (*     tr_if r Sskip Sbreak s' -> *)
  (*     tr_stmt s1 ts1 -> *)
  (*     tr_stmt (CStan.Swhile r s1) *)
  (*             (Sloop (Ssequence s' ts1) Sskip) *)
  (* | tr_break: *)
  (*     tr_stmt CStan.Sbreak Sbreak *)
  (* | tr_continue: *)
  (*     tr_stmt CStan.Scontinue Scontinue *)
  (* | tr_return_none: *)
  (*     tr_stmt (CStan.Sreturn None) (Sreturn None) *)
  (* | tr_return_some: forall r s' a, *)
  (*     tr_expression r s' a -> *)
  (*     tr_stmt (CStan.Sreturn (Some r)) (Ssequence s' (Sreturn (Some a))) *)
  (* . *)

Inductive tr_function: CStan.function -> Clight.function -> Prop :=
  | tr_function_intro: forall f tf,
      tr_stmt f.(CStan.fn_body) tf.(fn_body) ->
      fn_return tf = CStan.fn_return f ->
      fn_callconv tf = CStan.fn_callconv f ->
      (* fn_params tf = CStan.fn_params f -> *)
      fn_vars tf = CStan.fn_vars f ->
      tr_function f tf.


Inductive tr_fundef: CStan.fundef -> Clight.fundef -> Prop :=
  | tr_internal: forall f tf,
      tr_function f tf ->
      tr_fundef (Internal f) (Internal tf)
  | tr_external: forall ef targs tres cconv,
      tr_fundef (External ef targs tres cconv) (External ef targs tres cconv).

Lemma tr_type: CStan.type -> Ctypes.type -> Prop. Admitted.

(** ** Linking types *)
Lemma cstan_type_eq: forall (ty1 ty2: CStan.type), {ty1=ty2} + {ty1<>ty2}.
Proof.
  decide equality.
  - decide equality.
  - decide equality. Admitted.


Program Instance Linker_types : Linker CStan.type := {
  link := fun (t1:CStan.type) (t2:CStan.type) => if cstan_type_eq t1 t2 then Some t2 else None;
  linkorder := fun t1 t2 => t1 = t2
}.
Next Obligation.
  destruct (cstan_type_eq x y); inv H. auto.
Defined.

Global Opaque Linker_types.

Definition match_prog (p: CStan.program) (tp: Clight.program) :=
  match_program (fun ctx f tf => tr_fundef f tf) (fun t tt => tr_type t tt) p tp
 (* /\ prog_types tp = prog_types p. *)
  .

Hypothesis TRANSL: match_prog prog tprog.
Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSL).

Lemma eval_expr_correct:
  forall e le m a v target ta
  (TRE: transf_expression a = OK ta),
  CStan.eval_expr ge e le m target a v -> Clight.eval_expr tge e le m ta v.
Proof.
  intros e le m a v target ta.
  intros.
  Admitted.

Lemma eval_lvalue_correct:
  forall e le m a b ofs target ta
  (TRE: transf_expression a = OK ta),
  CStan.eval_lvalue ge e le m target a b ofs -> Clight.eval_lvalue tge e le m ta b ofs.
Proof.
  intros.
Admitted.

Lemma types_correct:
  forall e x, transf_expression e = OK x -> CStan.typeof e = Clight.typeof x.
Proof.
  intro e.
  induction e; intros; simpl in *; monadInv H; simpl; trivial.
Qed.

Lemma step_simulation:
  forall S1 t S2, CStan.stepf ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'), exists S2', plus Clight.step1 tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1. simpl; intros; inv MS; simpl in *; try (monadInv TRS).

  (* assign *)
  exists (Clight.State tf Clight.Sskip tk e le m').
  split.
  eapply plus_one.
  generalize (types_correct _ _ EQ); intro.
  generalize (types_correct _ _ EQ1); intro.  
  rewrite H3 in *.
  rewrite H4 in *.
  unfold step1. 
  eapply step_assign.
  eapply eval_lvalue_correct; eauto.
  eapply eval_expr_correct; eauto.
  eapply H1.
  admit.
  econstructor; eauto.
  Focus 1.
  intros.

Admitted.

Lemma initial_states_simulation:
  forall S, CStan.initial_state prog S ->
  exists R, Clight.initial_state tprog R /\ match_states S R.
Proof.
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
Admitted.

End PRESERVATION.

