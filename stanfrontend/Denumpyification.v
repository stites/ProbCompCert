Require Import List.
Require Import StanE.
Require Import Ctypes.
Require CStan.
Require Import Errors.
Require Import String.
Open Scope string_scope.
Require Import Coqlib.

Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : gensym_monad_scope.

Local Open Scope gensym_monad_scope.
  
Fixpoint transf_expression (e: StanE.expr) {struct e}: res CStan.expr :=
  match e with
  | Econst_int _ => Error (msg "Denumpyification.transf_program: NIY")
  | Econst_float _ => Error (msg "Denumpyification.transf_program: NIY")
  | Evar _ => Error (msg "Denumpyification.transf_program: NIY")
  | Eunop _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Ebinop _ _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Ecall _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Econdition _ _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Earray _ => Error (msg "Denumpyification.transf_program: NIY")
  | Erow _ => Error (msg "Denumpyification.transf_program: NIY")
  | Eindexed _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Edist _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Etarget => Error (msg "Denumpyification.transf_program: NIY")
  end

with transf_index (i: StanE.index) {struct i}: res CStan.expr :=
  match i with
  | Iall => Error (msg "Denumpyification.transf_program: NIY")
  | Isingle _ => Error (msg "Denumpyification.transf_program: NIY")
  | Iupfrom _ => Error (msg "Denumpyification.transf_program: NIY")
  | Idownfrom _ => Error (msg "Denumpyification.transf_program: NIY")
  | Ibetween _ _ => Error (msg "Denumpyification.transf_program: NIY")
  end.
                  
Fixpoint transf_statement (s: StanE.statement) {struct s}: res CStan.statement :=
  match s with
  | Sskip => Error (msg "Denumpyification.transf_program: NIY")
  | Sassign _ _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Sblock sl => Error (msg "Denumpyification.transf_program: NIY")
  | Sifthenelse _ _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Swhile _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Sfor _ _ _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Sbreak => Error (msg "Denumpyification.transf_program: NIY")
  | Scontinue => Error (msg "Denumpyification.transf_program: NIY")
  | Sreturn _ => Error (msg "Denumpyification.transf_program: NIY")
  | Svar _ => Error (msg "Denumpyification.transf_program: NIY")
  | Scall _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Sruntime _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Sforeach _ _ _ => Error (msg "Denumpyification.transf_program: NIY")
  | Starget _ => Error (msg "Denumpyification.transf_program: NIY")
  | Stilde _ _ _ _ => Error (msg "Denumpyification.transf_program: NIY")
  end.
				    
Definition transf_basic (b: StanE.basic): res Ctypes.type :=
  match b with
  | Bint => Error (msg "Denumpyification.transf_program: NIY")
  | Breal => Error (msg "Denumpyification.transf_program: NIY")
  | Bvector _ => Error (msg "Denumpyification.transf_program: NIY")
  | Brow _ => Error (msg "Denumpyification.transf_program: NIY")
  | Bmatrix _ _ => Error (msg "Denumpyification.transf_program: NIY")
  end. 

Definition transf_variable (id: AST.ident) (v: StanE.variable): res CStan.type :=
  Error (msg "Denumpyification.transf_variable: NIY").								     
	
Definition transf_function (v: StanE.function): res CStan.function :=
  Error (msg "Denumpyification.transf_function: NIY").

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
								 
