Require Import List.
Require Import StanE.
Require Import Ctypes.
Require CStan.
Require Import Errors.
Require Import String.
Open Scope string_scope.
Require Import Coqlib.
Require Import Sops.
Require Import Cop.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.

Definition TCInt := Tint I32 Signed noattr.
Definition TCFloat := Tfloat F64 noattr.

Definition transf_operator (o: Sops.operator): res Cop.binary_operation :=
  match o with
  | Sops.Plus => OK Cop.Oadd
  | Sops.Minus => OK Cop.Osub
  | Sops.Times => OK Cop.Omul
  | Sops.Divide => OK Cop.Odiv
  | Sops.Modulo => OK Cop.Omod
  | Sops.Or => OK Cop.Oor
  | Sops.And => OK Cop.Oand
  | Sops.Equals => OK Cop.Oeq
  | Sops.NEquals => OK Cop.One
  | Sops.Less => OK Cop.Olt
  | Sops.Leq => OK Cop.Ole
  | Sops.Greater => OK Cop.Ogt
  | Sops.Geq =>	OK Cop.Oge		    
  | _ => Error (msg "Denumpyification.transf_program: operator")
  end.

Definition transf_unary_operator (o: Sops.operator): res Cop.unary_operation :=
  match o with
  | Sops.PNot => Error (msg "Sops.PNot")
  | Sops.EltTimes => Error (msg "Sops.EltTimes")
  | Sops.EltDivide => Error (msg "Sops.EltDivide")
  | Sops.Pow => Error (msg "Sops.Pow")
  | Sops.EltPow => Error (msg "Sops.EltPow")
  | Sops.Transpose => Error (msg "Sops.Transpose.")

  | Sops.Plus => Error (msg "Sops.Plus")
  | Sops.Minus => Error (msg "Sops.Minus")
  | Sops.Times => Error (msg "Sops.Times")
  | Sops.Divide => Error (msg "Sops.Divide")
  | Sops.Modulo => Error (msg "Sops.Modulo")
  | Sops.Or => Error (msg "Sops.Or")
  | Sops.And => Error (msg "Sops.And")
  | Sops.Equals => Error (msg "Sops.Equals")
  | Sops.NEquals => Error (msg "Sops.NEquals")
  | Sops.Less => Error (msg "Sops.Less")
  | Sops.Leq => Error (msg "Sops.Leq")
  | Sops.Greater => Error (msg "Sops.Greater")
  | Sops.Geq =>	Error (msg "Sops.Geq")
  | _ => Error (msg "Denumpyification.transf_program: operator")
  end.

  (* | Onotbool : unary_operation          (**r boolean negation ([!] in C) *) *)
  (* | Onotint : unary_operation           (**r integer complement ([~] in C) *) *)
  (* | Oneg : unary_operation              (**r opposite (unary [-]) *) *)
  (* | Oabsfloat : unary_operation.        (**r floating-point absolute value *) *)



Fixpoint transf_expression (e: StanE.expr) {struct e}: res CStan.expr :=
  match e with
  | Econst_int i => OK (CStan.Econst_int i TCInt)
  | Econst_float f => OK (CStan.Econst_float f TCFloat)
  | Evar i => OK (CStan.Evar i Tvoid)
  | Eunop o e =>
    do o <- transf_unary_operator o;
    do e <- transf_expression e;
    OK (CStan.Eunop o e Tvoid)
  | Ebinop e1 o e2 =>
    do o <- transf_operator o;
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    OK (CStan.Ebinop o e1 e2 Tvoid)
  | Ecall i el => Error (msg "Denumpyification.transf_expression: call expression should have been removed already")
  | Econdition e1 e2 e3 => Error (msg "Denumpyification.transf_expression (NYI): Econdition")
  | Earray el => Error (msg "Denumpyification.transf_expression (NYI): Earray")
  | Erow el => Error (msg "Denumpyification.transf_expression (NYI): Erow")
  | Eindexed e nil =>
    Error (msg "Denumpyification.transf_expression: Eindexed cannot be passed an empty list")
  | Eindexed e (cons i nil) =>
    do e <- transf_expression e;
    do i <- transf_index i;
    (*FIXME how do i get the expression's address and turn it into a pointer*)
    (*FIXME *)
    Error (msg "Denumpyification.transf_expression (NYI): Eindexed")
  | Eindexed e (cons i l) =>
    Error (msg "Denumpyification.transf_expression (NYI): Eindexed")
  | Edist i el => Error (msg "Denumpyification.transf_expression (NYI): Edist")
  | Etarget => OK (CStan.Etarget Tvoid)
  end

with transf_index (i: StanE.index) {struct i}: res CStan.expr :=
  match i with
  | Iall => Error (msg "Denumpyification.transf_index (NYI): Iall")
  | Isingle e => do e <- transf_expression e; OK e
  | Iupfrom e =>
    do e <- transf_expression e;
    Error (msg "Denumpyification.transf_index (NYI): Iupfrom")
  | Idownfrom e =>
    do e <- transf_expression e;
    Error (msg "Denumpyification.transf_index (NYI): Idownfrom")
  | Ibetween e1 e2 =>
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    Error (msg "Denumpyification.transf_index (NYI): Ibetween")
  end.


Fixpoint transf_expression_list (l: list (StanE.expr)) {struct l}: res (list CStan.expr) :=
  match l with
  | nil => OK (nil)
  | cons e l =>
    do e <- (transf_expression e);
    do l <- (transf_expression_list l);
    OK (cons e l)
  end.

Definition option_mmap {X Y:Type} (f: X -> res Y) (ox: option X) : res (option Y) :=
  match ox with
  | None => OK None
  | Some x => do x <- f x; OK (Some x)
  end.

Fixpoint transf_statement (s: StanE.statement) {struct s}: res CStan.statement :=
  match s with
  | Sskip => OK CStan.Sskip
  | Sassign e1 None e2 => (* v = x *)
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    OK (CStan.Sassign e1 e2)
  | Sassign e1 (Some o) e2 => (* v ?= x *)
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    do o <- transf_operator o;
    Error (msg "Denumpyification.transf_statement (NYI): Sassign")
    (* OK (CStan.Sassign e1 (CStan.Ebinop o e1 e2 Tvoid)) TODO(stites): Tvoid seems wrong and I need to doublecheck. *)
  | Ssequence s1 s2 =>
    do s1 <- (transf_statement s1);
    do s2 <- (transf_statement s2);
    OK (CStan.Ssequence s1 s2)
  | Sifthenelse e s1 s2 =>
    do e <- (transf_expression e); 
    do s1 <- (transf_statement s1);
    do s2 <- (transf_statement s2);
    OK (CStan.Sifthenelse e s1 s2)
  | Swhile e s =>
    do e <- (transf_expression e);
    do s <- (transf_statement s);
    OK (CStan.Swhile e s)
  | Sfor i e1 e2 s =>
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    do body <- transf_statement s;

    (* set i to first pointer in array *)
    let init := CStan.Sset i e1 in

    (* break condition of e1 == e2 *)
    let cond := CStan.Ebinop Oeq (CStan.Evar i (CStan.typeof e1)) e2 type_bool in

    (* FIXME: "increment pointer i" but this pointer arithmetic is probably wrong *)
    let Eincr := CStan.Ebinop Oadd (CStan.Evar i (CStan.typeof e1)) (CStan.Esizeof type_int32s type_int32s) type_int32s in

    let incr := CStan.Sset i Eincr in
    OK (CStan.Sfor init cond body incr)
  | Sbreak => OK CStan.Sbreak
  | Scontinue => OK CStan.Scontinue
  | Sreturn None => OK (CStan.Sreturn None)
  | Sreturn (Some e) =>
    do e <- transf_expression e;
    OK (CStan.Sreturn (Some e))
  | Svar v =>
    (*OK (CStan.Sset i (CStan.Evar i ...))*)
    Error (msg "Denumpyification.transf_statement (NYI): Svar")
  | Scall i el =>
    do el <- transf_expression_list el;
    (*OK (CStan.Scall (Some i) Tvoid el)*)
    Error (msg "Denumpyification.transf_statement (NYI): Scall")
  | Sruntime _ _ => Error (msg "Denumpyification.transf_statement (NYI): Sruntime")
  | Sforeach i e s =>
    Error (msg "Denumpyification.transf_statement (NYI): Sforeach")
  | Starget e =>
    do e <- transf_expression e;
    OK (CStan.Starget e)

  | Stilde e i el (oe1, oe2) =>
    do e <- transf_expression e;
    do el <- transf_expression_list el;
    do oe1 <- option_mmap transf_expression oe1;
    do oe2 <- option_mmap transf_expression oe2;
    OK (CStan.Stilde e i el (oe1, oe2))
end.


(** The syntax of type expressions.  Some points to note:
- Array types [Tarray n] carry the size [n] of the array.
  Arrays with unknown sizes are represented by pointer types.
- Function types [Tfunction targs tres] specify the number and types
  of the function arguments (list [targs]), and the type of the
  function result ([tres]).  Variadic functions and old-style unprototyped
  functions are not supported.

Inductive type : Type :=
  | Tvoid: type                                    (**r the [void] type *)
  | Tint: intsize -> signedness -> attr -> type    (**r integer types *)
  | Tlong: signedness -> attr -> type              (**r 64-bit integer types *)
  | Tfloat: floatsize -> attr -> type              (**r floating-point types *)
  | Tpointer: type -> attr -> type                 (**r pointer types ([*ty]) *)
  | Tarray: type -> Z -> attr -> type              (**r array types ([ty[len]]) *)
  | Tfunction: typelist -> type -> calling_convention -> type    (**r function types *)
  | Tstruct: ident -> attr -> type                 (**r struct types *)
  | Tunion: ident -> attr -> type                  (**r union types *)
with typelist : Type :=
  | Tnil: typelist
  | Tcons: type -> typelist -> typelist.
*)

Definition transf_basic (b: StanE.basic): res Ctypes.type :=
  match b with
  | Bint => OK TCInt
  | Breal => OK TCFloat
  | Bvector e =>
    Error (msg "Denumpyification.transf_basic (NYI): Bvector")
    (* do e <- transf_expression e; *)
    (* (let Econst_int i := e in *)
    (* OK (Tarray TCFloat i noattr)) *)
  | Brow e =>
    Error (msg "Denumpyification.transf_basic (NYI): Brow")
    (* do e <- transf_expression e; *)
    (* match e with *)
    (* | Econst_int i => OK (Tarray TCFloat i noattr) *)
    (* | _ => Error (msg "Denumpyification.transf_basic: expected an int") *)
    (* end *)
  | Bmatrix _ _ => Error (msg "Denumpyification.transf_basic (NYI): Bmatrix")
  end.

Definition transf_variable (_: AST.ident) (v: StanE.variable): res CStan.type :=
  do ty <- transf_basic (StanE.vd_type v);
  do oe <- option_mmap transf_expression (StanE.vd_init v);
  OK {|
    CStan.vd_type := ty;
    CStan.vd_constraint := StanE.vd_constraint v;
    CStan.vd_init := oe;
    CStan.vd_global := StanE.vd_global v;
  |}.

Definition transf_function (f: StanE.function): res CStan.function :=
  do body <- transf_statement f.(StanE.fn_body);
  OK {|
      CStan.fn_return := Tvoid;
      CStan.fn_params := nil;
      CStan.fn_body := body;
      CStan.fn_callconv := f.(StanE.fn_callconv);
      CStan.fn_temps := nil;
      CStan.fn_vars := nil;
     |}.

Definition transf_fundef (id: AST.ident) (fd: StanE.fundef) : res CStan.fundef :=
  match fd with
  | Internal f =>
      do tf <- transf_function f; OK (Internal tf)
  | External ef targs tres cc =>
      OK (External ef targs tres cc)
  end.

Definition transf_program(p: StanE.program): res CStan.program :=
  do p1 <- AST.transform_partial_program2 transf_fundef transf_variable p;
  OK {| 
      CStan.prog_defs := AST.prog_defs p1;
      CStan.prog_public:=p.(StanE.pr_public);
      CStan.prog_model:=p.(StanE.pr_model);
      CStan.prog_data:=p.(StanE.pr_data);
      CStan.prog_transformed_data:=p.(StanE.pr_parameters);
      CStan.prog_parameters:= p.(StanE.pr_parameters);
      CStan.prog_transformed_parameters:=p.(StanE.pr_transformed_parameters);   
      CStan.prog_generated_quantities:=p.(StanE.pr_generated);
      CStan.prog_comp_env:=Maps.PTree.empty _;
    |}.

