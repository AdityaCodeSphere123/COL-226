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

type type_t =
  | Type_Bool
  | Type_Integer
  | Type_Scalar
  | Type_VectorInt
  | Type_VectorFloat
  | Type_MatrixInt
  | Type_MatrixFloat

type binop_Ad =
  | PlusFloat | MinusFloat | TimesFloat | DivideFloat
  | PlusInt | MinusInt | TimesInt | DivideInt
  | AddVector | ScalarMultiply
  | AddMatrix | ScalarMatrixMultiply | MatrixMultiply | VectorMultiply
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
  | SquareRoot

type express =
  | Bool_Ad of bool
  | Int_Ad of int
  | Float_Ad of float
  | VectorInt_Ad of int * int list
  | VectorFloat_Ad of int * float list
  | MatrixInt_Ad of int * int * int array array 
  | MatrixFloat_Ad of int * int * float array array  
  | Var_Ad of string
  | Assign of string * express
  | AssignVec of string * express * express
  | AssignMat of string * express * express * express
  | BinOp_Ad of binop_Ad * express * express
  | UnOp_Ad of unop_Ad * express
  | Angle of express * express
  | Minor of express * int * int
  | NullExpr
  | File_Ad of string
  | IndexVec of string * express  
  | IndexMat of string * express * express  
  | Input_File of string * string
  | Input of string
  | Create_bool of string
  | Create_int of string
  | Create_float of string
  | Create_vecint of string * int
  | Create_vecfloat of string * int
  | Create_matint of string * int * int
  | Create_matfloat of string * int * int


type statement =
  | IfElse of express * statement list * statement list
  | For of string * express * express * statement list
  | While of express * statement list
  | Block of statement list
  | ExprStmt of express
  | Print of string
  | Error

type program = statement list


