(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)


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
Require Import SimplExpr.

Inductive expr : Type :=
  | Econst_int: int -> type -> expr       (**r integer literal *)       (*FIXME: I think we can remove this *)
  | Econst_float: float -> type -> expr   (**r double float literal *)
  | Econst_single: float32 -> type -> expr (**r single float literal *) (*FIXME: I think we can remove this *)
  | Econst_long: int64 -> type -> expr    (**r long integer literal *)
  | Evar: ident -> type -> expr           (**r variable *)
  | Etempvar: ident -> type -> expr       (**r temporary variable *)
  | Ederef: expr -> type -> expr          (**r pointer dereference (unary [*]) *)
  | Eunop: unary_operation -> expr -> type -> expr  (**r unary operation *)
  | Ebinop: binary_operation -> expr -> expr -> type -> expr (**r binary operation *)
  | Esizeof: type -> type -> expr         (**r size of a type *)
  | Ealignof: type -> type -> expr        (**r alignment of a type *)
  | Etarget: type -> expr.

Definition typeof (e: expr) : type :=
  match e with
  | Econst_int _ ty => ty
  | Econst_float _ ty => ty
  | Econst_single _ ty => ty
  | Econst_long _ ty => ty
  | Evar _ ty => ty
  | Etempvar _ ty => ty
  | Ederef _ ty => ty
  | Eunop _ _ ty => ty
  | Ebinop _ _ _ ty => ty
  | Esizeof _ ty => ty
  | Ealignof _ ty => ty
  | Etarget ty => ty
  end.

Definition label := ident.

Inductive statement : Type :=
  | Sskip : statement                   (**r do nothing *)
  | Sassign : expr -> expr -> statement (**r assignment [lvalue = rvalue] *)
  | Sset : ident -> expr -> statement   (**r assignment [tempvar = rvalue] *)
  | Scall: option ident -> expr -> list expr -> statement (**r function call *)
  | Sbuiltin: option ident -> external_function -> typelist -> list expr -> statement (**r builtin invocation *)
  | Ssequence : statement -> statement -> statement  (**r sequence *)
  | Sifthenelse : expr  -> statement -> statement -> statement (**r conditional *)
  | Sloop: statement -> statement -> statement (**r infinite loop *)
  | Sbreak : statement                      (**r [break] statement *)
  | Scontinue : statement                   (**r [continue] statement *)
  | Sreturn : option expr -> statement      (**r [return] statement *)
  | Starget: expr -> statement
  | Stilde: expr -> expr -> list expr -> (option expr * option expr) -> statement

with labeled_statements : Type :=            (**r cases of a [switch] *)
  | LSnil: labeled_statements
  | LScons: option Z -> statement -> labeled_statements -> labeled_statements.
                      (**r [None] is [default], [Some x] is [case x] *)

Definition Swhile (e: expr) (s: statement) :=
  Sloop (Ssequence (Sifthenelse e Sskip Sbreak) s) Sskip.

Definition Sdowhile (s: statement) (e: expr) :=
  Sloop s (Sifthenelse e Sskip Sbreak).

Definition Sfor
  (s1: statement) (* initializing statement *)
  (e2: expr) (* conditional *)
  (s3: statement) (* body *)
  (s4: statement) (* postprocessing statement *)
  := Ssequence s1 (Sloop (Ssequence (Sifthenelse e2 Sskip Sbreak) s3) s4).

Inductive constraint :=
  | Cidentity
  | Clower: expr -> constraint
  | Cupper: expr -> constraint
  | Clower_upper: expr -> expr -> constraint
  | Coffset: expr -> constraint
  | Cmultiplier: expr -> constraint
  | Coffset_multiplier: expr -> expr -> constraint
  | Cordered
  | Cpositive_ordered
  | Csimplex
  | Cunit_vector
  | Ccholesky_corr
  | Ccholesky_cov
  | Ccorrelation
  | Ccovariance.

Record type := mkvariable {
  vd_type: Ctypes.type;
  vd_constraint: constraint;
  vd_init: option expr;
  vd_global: bool
}.

Inductive blocktype := BTModel | BTOther.

Record function := mkfunction {
  fn_return: Ctypes.type; 
  fn_params: list (ident * Ctypes.type);
  fn_body: statement;
  fn_blocktype: blocktype;
  fn_generator: SimplExpr.generator;
  fn_callconv: calling_convention;
  fn_temps: list (ident * Ctypes.type);
  fn_vars: list (ident * Ctypes.type);
}.

Definition var_names (vars: list(ident * Ctypes.type)) : list ident :=
  List.map (@fst ident Ctypes.type) vars.

Definition fundef := Ctypes.fundef function.

Definition type_of_function (f: function) : Ctypes.type :=
  Tfunction (type_of_params (fn_params f)) (fn_return f) (fn_callconv f).

Definition type_of_fundef (f: fundef) : Ctypes.type :=
  match f with
  | Internal fd => type_of_function fd
  | External id args res cc => Tfunction args res cc
  end.

Inductive math_func := MFLog | MFExp | MFLogit | MFExpit.
Definition math_func_eq_dec : forall (x y : math_func), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.


Inductive dist_func := DBern | DUnif.
Definition dist_func_eq_dec : forall (x y : dist_func), { x = y } + { x <> y }.
Proof.
decide equality.
Defined.



Record program : Type := {
  prog_defs: list (ident * globdef fundef type);
  prog_public: list ident;
  prog_main: ident;
  prog_model: ident;
  prog_parameters: ident;
  prog_parameters_vars: list ident;
  prog_parameters_struct: ident * ident;
  prog_transformed_parameters: ident;
  prog_data: ident;
  prog_data_vars: list ident;
  prog_transformed_data: ident;
  prog_generated_quantities: ident;
  prog_comp_env: composite_env;
  prog_math_functions: list (math_func * ident * Ctypes.type);
  prog_dist_functions: list (dist_func * ident);
}.

Definition program_of_program (p: program) : AST.program fundef type :=
  {| AST.prog_defs := p.(prog_defs);
     AST.prog_public := p.(prog_public);
     AST.prog_main := p.(prog_model) |}.

Coercion program_of_program: program >-> AST.program.

Record genv := { genv_genv :> Genv.t fundef type; genv_cenv :> composite_env }.

Definition globalenv (p: program) :=
  {| genv_genv := Genv.globalenv p; genv_cenv := p.(prog_comp_env) |}.

Definition env := PTree.t (block * Ctypes.type). (* map variable -> location & type *)

Definition empty_env: env := (PTree.empty (block * Ctypes.type)).

(** The temporary environment maps local temporaries to values. *)

Definition temp_env := PTree.t val.

Inductive deref_loc (ty: Ctypes.type) (m: mem) (b: block) (ofs: ptrofs) : val -> Prop :=
  | deref_loc_value: forall chunk v,
      access_mode ty = By_value chunk ->
      Mem.loadv chunk m (Vptr b ofs) = Some v ->
      deref_loc ty m b ofs v
  | deref_loc_reference:
      access_mode ty = By_reference ->
      deref_loc ty m b ofs (Vptr b ofs)
  | deref_loc_copy:
      access_mode ty = By_copy ->
      deref_loc ty m b ofs (Vptr b ofs).

Inductive assign_loc (ce: composite_env) (ty: Ctypes.type) (m: mem) (b: block) (ofs: ptrofs):
                                            val -> mem -> Prop :=
  | assign_loc_value: forall v chunk m',
      access_mode ty = By_value chunk ->
      Mem.storev chunk m (Vptr b ofs) v = Some m' ->
      assign_loc ce ty m b ofs v m'
  | assign_loc_copy: forall b' ofs' bytes m',
      access_mode ty = By_copy ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs')) ->
      (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
      b' <> b \/ Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs' + sizeof ce ty <= Ptrofs.unsigned ofs
              \/ Ptrofs.unsigned ofs + sizeof ce ty <= Ptrofs.unsigned ofs' ->
      Mem.loadbytes m b' (Ptrofs.unsigned ofs') (sizeof ce ty) = Some bytes ->
      Mem.storebytes m b (Ptrofs.unsigned ofs) bytes = Some m' ->
      assign_loc ce ty m b ofs (Vptr b' ofs') m'.

Section SEMANTICS.

Variable ge: genv.

Inductive alloc_variables: env -> mem ->
                           list (ident * Ctypes.type) ->
                           env -> mem -> Prop :=
  | alloc_variables_nil:
      forall e m,
      alloc_variables e m nil e m
  | alloc_variables_cons:
      forall e m id ty vars m1 b1 m2 e2,
      Mem.alloc m 0 (sizeof ge ty) = (m1, b1) ->
      alloc_variables (PTree.set id (b1, ty) e) m1 vars e2 m2 ->
      alloc_variables e m ((id, ty) :: vars) e2 m2.

Inductive bind_parameters (e: env):
                           mem -> list (ident * Ctypes.type) -> list val ->
                           mem -> Prop :=
  | bind_parameters_nil:
      forall m,
      bind_parameters e m nil nil m
  | bind_parameters_cons:
      forall m id ty params v1 vl b m1 m2,
      PTree.get id e = Some(b, ty) ->
      assign_loc ge ty m b Ptrofs.zero v1 m1 ->
      bind_parameters e m1 params vl m2 ->
      bind_parameters e m ((id, ty) :: params) (v1 :: vl) m2.

Fixpoint create_undef_temps (temps: list (ident * Ctypes.type)) : temp_env :=
  match temps with
  | nil => PTree.empty val
  | (id, t) :: temps' => PTree.set id Vundef (create_undef_temps temps')
 end.

Fixpoint bind_parameter_temps (formals: list (ident * Ctypes.type)) (args: list val)
                              (le: temp_env) : option temp_env :=
 match formals, args with
 | nil, nil => Some le
 | (id, t) :: xl, v :: vl => bind_parameter_temps xl vl (PTree.set id v le)
 | _, _ => None
 end.

Definition block_of_binding (id_b_ty: ident * (block * Ctypes.type)) :=
  match id_b_ty with (id, (b, ty)) => (b, 0, sizeof ge ty) end.

Definition blocks_of_env (e: env) : list (block * Z * Z) :=
  List.map block_of_binding (PTree.elements e).

Definition set_opttemp (optid: option ident) (v: val) (le: temp_env) :=
  match optid with
  | None => le
  | Some id => PTree.set id v le
  end.

Fixpoint select_switch_default (sl: labeled_statements): labeled_statements :=
  match sl with
  | LSnil => sl
  | LScons None s sl' => sl
  | LScons (Some i) s sl' => select_switch_default sl'
  end.

Fixpoint select_switch_case (n: Z) (sl: labeled_statements): option labeled_statements :=
  match sl with
  | LSnil => None
  | LScons None s sl' => select_switch_case n sl'
  | LScons (Some c) s sl' => if zeq c n then Some sl else select_switch_case n sl'
  end.

Definition select_switch (n: Z) (sl: labeled_statements): labeled_statements :=
  match select_switch_case n sl with
  | Some sl' => sl'
  | None => select_switch_default sl
  end.

(** Turn a labeled statement into a sequence *)

Fixpoint seq_of_labeled_statement (sl: labeled_statements) : statement :=
  match sl with
  | LSnil => Sskip
  | LScons _ s sl' => Ssequence s (seq_of_labeled_statement sl')
  end.

(** ** Evaluation of expressions *)

Section EXPR.

Variable e: env.
Variable le: temp_env.
Variable m: mem.
Variable ta: float.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Econst_int:   forall i ty,
      eval_expr (Econst_int i ty) (Vint i)
  | eval_Econst_float:   forall f ty,
      eval_expr (Econst_float f ty) (Vfloat f)
  | eval_Econst_single:   forall f ty,
      eval_expr (Econst_single f ty) (Vsingle f)
  | eval_Econst_long:   forall i ty,
      eval_expr (Econst_long i ty) (Vlong i)
  | eval_Etempvar:  forall id ty v,
      le!id = Some v ->
      eval_expr (Etempvar id ty) v
  | eval_Eunop:  forall op a ty v1 v,
      eval_expr a v1 ->
      sem_unary_operation op v1 (typeof a) m = Some v ->
      eval_expr (Eunop op a ty) v
  | eval_Ebinop: forall op a1 a2 ty v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      sem_binary_operation ge op v1 (typeof a1) v2 (typeof a2) m = Some v ->
      eval_expr (Ebinop op a1 a2 ty) v
  | eval_Esizeof: forall ty1 ty,
      eval_expr (Esizeof ty1 ty) (Vptrofs (Ptrofs.repr (sizeof ge ty1)))
  | eval_Ealignof: forall ty1 ty,
      eval_expr (Ealignof ty1 ty) (Vptrofs (Ptrofs.repr (alignof ge ty1)))
  | eval_Elvalue: forall a loc ofs v,
      eval_lvalue a loc ofs ->
      deref_loc (typeof a) m loc ofs v ->
      eval_expr a v
  | eval_Etarget: forall ty,
      eval_expr (Etarget ty) (Vfloat ta)
with eval_lvalue: expr -> block -> ptrofs -> Prop :=
  | eval_Evar_local:   forall id l ty,
      e!id = Some(l, ty) ->
      eval_lvalue (Evar id ty) l Ptrofs.zero
  | eval_Evar_global: forall id l ty,
      e!id = None ->
      Genv.find_symbol ge id = Some l ->
      eval_lvalue (Evar id ty) l Ptrofs.zero.

Scheme eval_expr_ind2 := Minimality for eval_expr Sort Prop
  with eval_lvalue_ind2 := Minimality for eval_lvalue Sort Prop.
(*
Combined Scheme eval_expr_lvalue_ind from eval_expr_ind2, eval_lvalue_ind2.
*)

Inductive eval_exprlist: list expr -> typelist -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil Tnil nil
  | eval_Econs:   forall a bl ty tyl v1 v2 vl,
      eval_expr a v1 ->
      sem_cast v1 (typeof a) ty m = Some v2 ->
      eval_exprlist bl tyl vl ->
      eval_exprlist (a :: bl) (Tcons ty tyl) (v2 :: vl).

End EXPR.

(** ** Transition semantics for statements and functions *)

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

Inductive state: Type :=
  | State
      (f: function)
      (s: statement)
      (k: cont)
      (e: env)
      (le: temp_env)
      (m: mem) 
      (ta: float) : state
  | Callstate
      (fd: fundef)
      (args: list val)
      (k: cont)
      (m: mem) 
      (ta: float): state
  | Returnstate
      (res: val)
      (k: cont)
      (m: mem) 
      (ta: float): state.

(** Find the statement and manufacture the continuation
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: statement) (k: cont)
                    {struct s}: option (statement * cont) :=
  match s with
  | Ssequence s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 s2 =>
      match find_label lbl s1 (Kloop1 s1 s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 (Kloop2 s1 s2 k)
      end
  | _ => None
  end

with find_label_ls (lbl: label) (sl: labeled_statements) (k: cont)
                    {struct sl}: option (statement * cont) :=
  match sl with
  | LSnil => None
  | LScons _ s sl' =>
      match find_label lbl s (Kseq (seq_of_labeled_statement sl') k) with
      | Some sk => Some sk
      | None => find_label_ls lbl sl' k
      end
  end.

Variable function_entry: function -> list val -> mem -> env -> temp_env -> mem -> Prop.

Inductive step: state -> trace -> state -> Prop :=
  | step_assign:   forall f a1 a2 k e le m ta loc ofs v2 v m',
      eval_lvalue e le m ta a1 loc ofs ->
      eval_expr e le m ta a2 v2 ->
      sem_cast v2 (typeof a2) (typeof a1) m = Some v ->
      assign_loc ge (typeof a1) m loc ofs v m' ->
      step (State f (Sassign a1 a2) k e le m ta)
        E0 (State f Sskip k e le m' ta)
  | step_set:   forall f id a k e le m ta v,
      eval_expr e le m ta a v ->
      step (State f (Sset id a) k e le m ta)
        E0 (State f Sskip k e (PTree.set id v le) m ta)
  | step_call:   forall f optid a al k e le m ta tyargs tyres cconv vf vargs fd,
      classify_fun (typeof a) = fun_case_f tyargs tyres cconv ->
      eval_expr e le m ta a vf ->
      eval_exprlist e le m ta al tyargs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction tyargs tyres cconv ->
      step (State f (Scall optid a al) k e le m ta)
        E0 (Callstate fd vargs (Kcall optid f e le k) m ta)
  | step_builtin:   forall f optid ef tyargs al k e le m ta vargs t vres m',
      eval_exprlist e le m ta al tyargs vargs ->
      external_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef tyargs al) k e le m ta)
         t (State f Sskip k e (set_opttemp optid vres le) m' ta)
  | step_seq:  forall f s1 s2 k e le m ta,
      step (State f (Ssequence s1 s2) k e le m ta)
        E0 (State f s1 (Kseq s2 k) e le m ta)
  | step_skip_seq: forall f s k e le m ta,
      step (State f Sskip (Kseq s k) e le m ta)
        E0 (State f s k e le m ta)
  | step_continue_seq: forall f s k e le m ta,
      step (State f Scontinue (Kseq s k) e le m ta)
        E0 (State f Scontinue k e le m ta)
  | step_break_seq: forall f s k e le m ta,
      step (State f Sbreak (Kseq s k) e le m ta)
        E0 (State f Sbreak k e le m ta)
  | step_ifthenelse:  forall f a s1 s2 k e le m ta v1 b,
      eval_expr e le m ta a v1 ->
      bool_val v1 (typeof a) m = Some b ->
      step (State f (Sifthenelse a s1 s2) k e le m ta)
        E0 (State f (if b then s1 else s2) k e le m ta)
  | step_loop: forall f s1 s2 k e le m ta,
      step (State f (Sloop s1 s2) k e le m ta)
        E0 (State f s1 (Kloop1 s1 s2 k) e le m ta)
  | step_skip_or_continue_loop1:  forall f s1 s2 k e le m ta x,
      x = Sskip \/ x = Scontinue ->
      step (State f x (Kloop1 s1 s2 k) e le m ta)
        E0 (State f s2 (Kloop2 s1 s2 k) e le m ta)
  | step_break_loop1:  forall f s1 s2 k e le m ta,
      step (State f Sbreak (Kloop1 s1 s2 k) e le m ta)
        E0 (State f Sskip k e le m ta)
  | step_skip_loop2: forall f s1 s2 k e le m ta,
      step (State f Sskip (Kloop2 s1 s2 k) e le m ta)
        E0 (State f (Sloop s1 s2) k e le m ta)
  | step_break_loop2: forall f s1 s2 k e le m ta,
      step (State f Sbreak (Kloop2 s1 s2 k) e le m ta)
        E0 (State f Sskip k e le m ta)
  | step_return_0: forall f k e le m ta m',
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn None) k e le m ta)
        E0 (Returnstate Vundef (call_cont k) m' ta)
  | step_return_1: forall f a k e le m ta v v' m',
      eval_expr e le m ta a v ->
      sem_cast v (typeof a) f.(fn_return) m = Some v' ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f (Sreturn (Some a)) k e le m ta)
        E0 (Returnstate v' (call_cont k) m' ta)
  | step_skip_call: forall f k e le m ta m',
      is_call_cont k ->
      Mem.free_list m (blocks_of_env e) = Some m' ->
      step (State f Sskip k e le m ta)
        E0 (Returnstate Vundef k m' ta)
  | step_skip_break_switch: forall f x k e le m ta,
      x = Sskip \/ x = Sbreak ->
      step (State f x (Kswitch k) e le m ta)
        E0 (State f Sskip k e le m ta)
  | step_continue_switch: forall f k e le m ta,
      step (State f Scontinue (Kswitch k) e le m ta)
        E0 (State f Scontinue k e le m ta)
  | step_internal_function: forall f vargs k m ta e le m1,
      function_entry f vargs m e le m1 ->
      step (Callstate (Internal f) vargs k m ta)
        E0 (State f f.(fn_body) k e le m1 ta)
  | step_external_function: forall ef targs tres cconv vargs k m ta vres t m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef targs tres cconv) vargs k m ta)
         t (Returnstate vres k m' ta)
  | step_returnstate: forall v optid f e le k m ta,
      step (Returnstate v (Kcall optid f e le k) m ta)
        E0 (State f Sskip k e (set_opttemp optid v le) m ta)
  | step_target: forall f a k e le m ta v ta',
      eval_expr e le m ta a v ->
      v = Vfloat ta' ->
      step (State f (Starget a) k e le m ta) 
        E0 (State f Sskip k e le m ta').

End SEMANTICS.
  
Inductive function_entry (ge: genv) (f: function) (vargs: list val) (m: mem) (e: env) (le: temp_env) (m': mem) : Prop :=
  | function_entry_intro: forall m1,
      list_norepet (var_names f.(fn_params) ++ var_names f.(fn_vars)) ->
      alloc_variables ge empty_env m (f.(fn_params) ++ f.(fn_vars)) e m1 ->
      bind_parameters ge e m1 f.(fn_params) vargs m' ->
      le = create_undef_temps f.(fn_temps) ->
      function_entry ge f vargs m e le m'.

Definition stepf (ge: genv) := step ge (function_entry ge).

Parameter zero: float.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_data_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      type_of_fundef f = Tfunction Tnil Tvoid cc_default ->
      initial_state p (Callstate f nil Kstop m0 zero).

Inductive final_state: state -> int -> Prop :=
  | final_state_data_intro: forall r m ta,
      final_state (Returnstate (Vint r) Kstop m ta) r.

Definition semantics (p: program) :=
  let ge := globalenv p in
  Semantics_gen stepf (initial_state p) final_state ge ge.





