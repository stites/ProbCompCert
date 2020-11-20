Require Import Globalenvs.
Require Import Events.
Require Import Integers.

Parameter string : Type.

Parameter literal_T : string.
Parameter literal_lpdf : string (* "_lpdf" *).
Parameter literal_lpmf : string (* "_lpmf" *).

Parameter is_suffix: string -> string -> bool.

Definition identifier := string.

Inductive operator :=
  | Plus
  | Vector_Plus
  | PPlus
  | Minus
  | PMinus
  | Times
  | Divide
  | IntDivide
  | Modulo
  | LDivide
  | EltTimes
  | EltDivide
  | Pow
  | EltPow
  | Or
  | And
  | Equals
  | NEquals
  | Less
  | Leq
  | Greater
  | Geq
  | PNot
  | Transpose
                                                                                       
 with expression :=
  | TernaryIf: expression * expression * expression -> expression
  | BinOp: expression * operator * expression -> expression
  | PrefixOp: operator * expression -> expression
  | PostfixOp: expression * operator -> expression
  | Var: identifier -> expression
  | IntNumeral: string -> expression
  | RealNumeral: string -> expression
  | FunApp: identifier * (list expression) -> expression
  | CondDistApp: identifier * (list expression) -> expression
  (* GetLP is deprecated *)
  | GetLP
  | GetTarget
  | ArrayExpr: (list expression) -> expression
  | RowVectorExpr: (list expression) -> expression
  | Indexed: expression * (list index) -> expression

with index :=
  | All
  | Single: expression -> index
  | Upfrom: expression -> index
  | Downfrom: expression -> index
  | Between: expression * expression -> index. 

Inductive transformation :=
  | Identity
  | Lower: expression -> transformation
  | Upper: expression -> transformation
  | LowerUpper: expression * expression -> transformation
  | Offset: expression -> transformation
  | Multiplier: expression -> transformation
  | OffsetMultiplier: expression * expression -> transformation
  | Ordered
  | PositiveOrdered
  | Simplex
  | UnitVector
  | CholeskyCorr
  | CholeskyCov
  | Correlation
  | Covariance.

Inductive sizedtype :=
  | SInt
  | SReal
  | SVector: expression -> sizedtype
  | SRowVector: expression -> sizedtype
  | SMatrix: expression * expression -> sizedtype
  | SArray: sizedtype * expression -> sizedtype.

Inductive unsizedtype :=
  | UInt
  | UReal
  | UVector
  | URowVector
  | UMatrix
  | UArray: unsizedtype -> unsizedtype
  | UFun: (list (autodifftype * unsizedtype)) * returntype -> unsizedtype
  | UMathLibraryFunction

with autodifftype := DataOnly | AutoDiffable

with returntype := Void | ReturnType: unsizedtype -> returntype.

Inductive stantype := Sized: sizedtype -> stantype | Unsized: unsizedtype -> stantype .

Inductive assignmentoperator :=
  | Assign
  (* ArrowAssign is deprecated *)
  | ArrowAssign
  | OperatorAssign: operator -> assignmentoperator.

Inductive truncation :=
  | NoTruncate
  | TruncateUpFrom: expression -> truncation
  | TruncateDownFrom: expression -> truncation
  | TruncateBetween: expression * expression -> truncation.

Inductive printable := PString: string -> printable | PExpr: expression -> printable.

(*
Inductive lvalue :=
  | LVariable: identifier -> lvalue
  | LIndexed: lvalue * (list index) -> lvalue.
*)

Record vardecl := mkVarDecl {
    decl_transform : transformation;
    decl_type : stantype;
    decl_identifier : identifier;
    initial_value: option expression;
    is_global : bool
  }.

Record assign_record := { assign_lhs : expression; (* CHANGE - why? *)
                          assign_op : assignmentoperator;
                          assign_rhs : expression }.

Record tilde_record := {
  tilde_arg : expression;
  tilde_distribution : identifier;
  tilde_args : list expression;
  tilde_truncation : truncation
}.

Record for_record := {
  loop_variable: identifier;
  lower_bound: expression;
  upper_bound: expression;
}.

Inductive statement :=
  | Assignment : assign_record -> statement
  | TargetPE : expression -> statement
  | Tilde : tilde_record -> statement
  | IfThenElse :  expression * statement * option statement -> statement
  | For (FR: for_record) (loop_body: statement) : statement
  | Block : list statement -> statement
  | VarDecl : vardecl -> statement
  | NRFunApp: identifier * (list expression)  -> statement
  (* IncrementLogProb is deprecated *)
  | IncrementLogProb: expression -> statement
  | Break
  | Continue
  | Return: expression -> statement
  | ReturnVoid
  | PrintStmt: list printable -> statement
  | Reject: list printable -> statement
  | Skip
  | While: expression * statement -> statement
  | ForEach: identifier * expression * statement -> statement.


Record fundecl := { 
      funreturntype : returntype; 
      funname : identifier; 
      arguments : (list (autodifftype * unsizedtype * identifier));
      body: statement 
}.


Record program := {
  functionblock: option (list fundecl);
  datablock : option (list vardecl);
  transformeddatablock: option (list statement);
  parametersblock : option (list vardecl);
  transformedparametersblock: option (list statement);
  modelblock : option (list statement);
  generatedquantitiesblock: option (list statement)
}.

Require Import Smallstep.

Parameter semantics: program -> semantics.
