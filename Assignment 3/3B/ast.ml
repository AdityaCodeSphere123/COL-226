(* Aditya Anand : 2023CS50284 *)

type dsl_type =
  | UnitType
  | BoolType
  | IntType
  | FloatType
  | VectorTypeInt of int
  | VectorTypeFloat of int
  | MatrixTypeInt of int * int
  | MatrixTypeFloat of int * int

type binop_Ad =
  | PlusFloat | MinusFloat | TimesFloat | DivideFloat
  | PlusInt | MinusInt | TimesInt | DivideInt
  | AddVector | ScalarMultiply
  | AddMatrix | ScalarMatrixMultiply | MatrixMultiply
  | Modulus | Power
  | Equal | NotEqual | Less | LessEqual | Greater | GreaterEqual
  | And | Or
  | DotProduct

type unop_Ad =
  | Not
  | Transpose
  | InverseVector 
  | InverseMatrix 
  | Inverse
  | Determinant
  | Magnitude
  | AbsFloat 
  | AbsInt
  | DimensionVector 
  | DimensionMatrix

type express =
  | Bool_Ad of bool
  | Int_Ad of int
  | Float_Ad of float
  | VectorInt_Ad of int * int list
  | VectorFloat_Ad of int * float list
  | MatrixInt_Ad of int * int * int array array 
  | MatrixFloat_Ad of int * int * float array array  
  | Var_Ad of string
  | BinOp_Ad of binop_Ad * express * express
  | UnOp_Ad of unop_Ad * express
  | Angle of express * express
  | NullExpr
  |File_Ad of string

type statement =
  | Assign of string * express
  | IfElse of express * statement * statement 
  | For of string * express * express * statement
  | While of express * statement
  | Block of statement list
  | ExprStmt of express
  | InputStmt of string
  | Input  
  | PrintStmt of string 

type program = statement list


