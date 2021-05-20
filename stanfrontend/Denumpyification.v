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

Fixpoint transf_expression (e: StanE.expr) {struct e}: res CStan.expr :=
  match e with
  | Econst_int i => OK (CStan.Econst_int i (Tint I32 Signed noattr))
  | Econst_float f => OK (CStan.Econst_float f (Tfloat F64 noattr))
  | Evar i => OK (CStan.Evar i Tvoid)
  | Eunop o e => Error (msg "Denumpyification.transf_expression (NYI): Eunop")
  | Ebinop e1 o e2 =>
    do o <- transf_operator o;
    do e1 <- transf_expression e1;
    do e2 <- transf_expression e2;
    OK (CStan.Ebinop o e1 e2 Tvoid)
  | Ecall i el => Error (msg "Denumpyification.transf_expression: call expression should have been removed already")
  | Econdition e1 e2 e3 => Error (msg "Denumpyification.transf_expression (NYI): Econdition")
  | Earray el => Error (msg "Denumpyification.transf_expression (NYI): Earray")
  | Erow el => Error (msg "Denumpyification.transf_expression (NYI): Erow")
  | Eindexed e il => Error (msg "Denumpyification.transf_expression (NYI): Eindexed")
  | Edist i el => Error (msg "Denumpyification.transf_expression (NYI): Edist")
  | Etarget => OK (CStan.Etarget Tvoid)
  end

with transf_index (i: StanE.index) {struct i}: res CStan.expr :=
  match i with
  | Iall => Error (msg "Denumpyification.transf_index (NYI): Iall")
  | Isingle e => Error (msg "Denumpyification.transf_index (NYI): Isingle")
  | Iupfrom e => Error (msg "Denumpyification.transf_index (NYI): Iupfrom")
  | Idownfrom e => Error (msg "Denumpyification.transf_index (NYI): Idownfrom")
  | Ibetween e1 e2 => Error (msg "Denumpyification.transf_index (NYI): Ibetween")
  end.
   
Fixpoint transf_expression_list (l: list (StanE.expr)) {struct l}: res (list CStan.expr) :=
  match l with
  | nil => OK (nil)
  | cons e l =>
    do e <- (transf_expression e);
    do l <- (transf_expression_list l);
    OK (cons e l)
  end.

Fixpoint option_mmap {X Y:Type} (f: X -> res Y) (ox: option X) : res (option Y) :=
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


Definition transf_basic (b: StanE.basic): res Ctypes.type :=
  match b with
  | Bint => Error (msg "Denumpyification.transf_basic (NYI): Bint")
  | Breal => Error (msg "Denumpyification.transf_basic (NYI): Breal")
  | Bvector _ => Error (msg "Denumpyification.transf_basic (NYI): Bvector")
  | Brow _ => Error (msg "Denumpyification.transf_basic (NYI): Brow")
  | Bmatrix _ _ => Error (msg "Denumpyification.transf_basic (NYI): Bmatrix")
  end.

Definition transf_variable (id: AST.ident) (v: StanE.variable): res CStan.type :=
  Error (msg "Denumpyification.transf_variable: NIY").

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
