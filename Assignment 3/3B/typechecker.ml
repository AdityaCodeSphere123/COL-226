(* Aditya Anand : 2023CS50284*)
open Ast

exception TypeError of string

type types =
  | BoolType
  | IntType
  | FloatType
  | VectorTypeInt of int
  | VectorTypeFloat of int  
  | MatrixTypeInt of int * int
  | MatrixTypeFloat of int * int  
  | UnitType 

  type table_variable = (string, types) Hashtbl.t


  let rec string_of_type t = match t with
    | BoolType -> "BoolType"
    | IntType -> "IntType"
    | FloatType -> "FloatType"
    | VectorTypeInt dim -> Printf.sprintf "VectorTypeInt(%d)" dim
    | VectorTypeFloat dim -> Printf.sprintf "VectorTypeFloat(%d)" dim
    | MatrixTypeInt (rows, cols) -> Printf.sprintf "MatrixTypeInt(%d, %d)" rows cols
    | MatrixTypeFloat (rows, cols) -> Printf.sprintf "MatrixTypeFloat(%d, %d)" rows cols
    | UnitType -> "UnitType" 


    let string_of_unop = function
    | Not -> "Not"
    | Transpose -> "Transpose"
    | InverseVector -> "InverseVector"
    | InverseMatrix -> "InverseMatrix"
    | Inverse -> "Inverse"
    | Determinant -> "Determinant"
    | Magnitude -> "Magnitude"
    | AbsFloat -> "AbsFloat"
    | AbsInt -> "AbsInt"
    | DimensionVector -> "DimensionVector"
    | DimensionMatrix -> "DimensionMatrix"

let string_of_binop = function
  | PlusFloat -> "PlusFloat"
  | MinusFloat -> "MinusFloat"
  | TimesFloat -> "TimesFloat"
  | DivideFloat -> "DivideFloat"
  | PlusInt -> "PlusInt"
  | MinusInt -> "MinusInt"
  | TimesInt -> "TimesInt"
  | DivideInt -> "DivideInt"
  | Modulus -> "Modulus"
  | Power -> "Power"
  | AddVector -> "AddVector"
  | ScalarMultiply -> "ScalarMultiply"
  | AddMatrix -> "AddMatrix"
  | ScalarMatrixMultiply -> "ScalarMatrixMultiply"
  | MatrixMultiply -> "MatrixMultiply"
  | Equal -> "Equal"
  | NotEqual -> "NotEqual"
  | Less -> "Less"
  | Greater -> "Greater"
  | LessEqual -> "LessEqual"
  | GreaterEqual -> "GreaterEqual"
  | And -> "And"
  | Or -> "Or"
  | DotProduct -> "DotProduct"


let rec type_of env expr = match expr with
  | Bool_Ad _ -> BoolType
  | Int_Ad _ -> IntType
  | Float_Ad _ -> FloatType
  | VectorInt_Ad (dim, _) -> VectorTypeInt dim
  | VectorFloat_Ad (dim, _) -> VectorTypeFloat dim
  | MatrixInt_Ad (row, col, _) -> MatrixTypeInt (row, col)
  | MatrixFloat_Ad (row, col, _) -> MatrixTypeFloat (row, col) 
  | File_Ad _ -> UnitType
  | Var_Ad (x) -> (try Hashtbl.find env x
                 with Not_found -> 
                 raise (TypeError (Printf.sprintf "Undefined variable: %s" x)))
 
  | BinOp_Ad (sign, e1, e2) ->
      let first = type_of env e1 in
      let second = type_of env e2 in
      (match sign with
    | PlusFloat ->
        if first = FloatType && second = FloatType then FloatType
        else raise (TypeError "PlusFloat operation needs float operands")

    | MinusFloat ->
        if first = FloatType && second = FloatType then FloatType
        else raise (TypeError "MinusFloat operation needs float operands")

    | TimesFloat ->
        if first = FloatType && second = FloatType then FloatType
        else raise (TypeError "TimesFloat operation needs float operands")

    | DivideFloat ->
        if first = FloatType && second = FloatType then FloatType
        else raise (TypeError "DivideFloat operation needs float operands")
           
    | PlusInt ->
        if first = IntType && second = IntType then IntType
        else raise (TypeError "PlusInt operation needs integer operands")

    | MinusInt ->
        if first = IntType && second = IntType then IntType
        else raise (TypeError "MinusInt operation needs integer operands")

    | TimesInt ->
        if first = IntType && second = IntType then IntType
        else raise (TypeError "TimesInt operation needs integer operands")

    | DivideInt ->
        if first = IntType && second = IntType then IntType
        else raise (TypeError "DivideInt operation needs integer operands")

    | Modulus ->
        if first = IntType && second = IntType then IntType
        else raise (TypeError "Modulus operation needs integer operands")

       | Power ->
           (match first, second with
            | IntType, IntType -> IntType
            | FloatType, FloatType -> FloatType
            | FloatType, IntType -> FloatType
            | _, _ -> raise (TypeError "Power operation type mismatch"))
           
       | AddVector ->
           (match first, second with
            | VectorTypeInt n1, VectorTypeInt n2 when n1 = n2 -> VectorTypeInt n1
            | VectorTypeFloat n1, VectorTypeFloat n2 when n1 = n2 -> VectorTypeFloat n1
            | _ -> raise (TypeError "Vector addition requires vectors of the same dimension"))
           
       | ScalarMultiply ->
           (match first, second with
            | FloatType, VectorTypeFloat n -> VectorTypeFloat n
            | VectorTypeFloat n, FloatType -> VectorTypeFloat n
            | IntType, VectorTypeInt n -> VectorTypeInt n
            | VectorTypeInt n, IntType -> VectorTypeInt n
            | _, _ -> raise (TypeError "Scalar multiplication requires a scalar and a vector"))
           
       | AddMatrix ->
           (match first, second with
            | MatrixTypeInt (r1, c1), MatrixTypeInt (r2, c2) when r1 = r2 && c1 = c2 -> 
                MatrixTypeInt (r1, c1)
            | MatrixTypeFloat (r1, c1), MatrixTypeFloat (r2, c2) when r1 = r2 && c1 = c2 ->
                MatrixTypeFloat (r1, c1)
            | _ -> raise (TypeError "Matrix addition requires matrices of the same dimensions"))
           
       | ScalarMatrixMultiply ->
           (match first, second with
            | FloatType, MatrixTypeFloat (row, column) -> MatrixTypeFloat (row, column)
            | MatrixTypeFloat (row, column), FloatType -> MatrixTypeFloat (row, column)
            | IntType, MatrixTypeInt (row, column) -> MatrixTypeInt (row, column)
            | MatrixTypeInt (row, column), IntType -> MatrixTypeInt (row, column)
            | _, _ -> raise (TypeError "Scalar-matrix multiplication requires a scalar and a matrix"))
           
       | MatrixMultiply ->
           (match first, second with
            | MatrixTypeInt (r1, c1), MatrixTypeInt (r2, c2) when c1 = r2 -> 
                MatrixTypeInt (r1, c2)
            | MatrixTypeFloat (r1, c1), MatrixTypeFloat (r2, c2) when c1 = r2 ->
                MatrixTypeFloat (r1, c2)
            | _ -> raise (TypeError "Matrix multiplication requires compatible matrix dimensions"))
           
    | DotProduct ->
        (match first, second with
         | VectorTypeInt n1, VectorTypeInt n2 when n1 = n2 -> IntType
         | VectorTypeFloat n1, VectorTypeFloat n2 when n1 = n2 -> FloatType
         | _ -> raise (TypeError "Dot product requires vectors of the same type and dimension"))
    | Equal | NotEqual ->
        if first = second then BoolType
        else raise (TypeError "Equality operations require operands of the same type")

    | Less ->
        if (first = IntType && second = IntType) || (first = FloatType && second = FloatType) then BoolType
        else raise (TypeError "Less operation requires numeric operands of the same type")

    | Greater ->
        if (first = IntType && second = IntType) || (first = FloatType && second = FloatType) then BoolType
        else raise (TypeError "Greater operation requires numeric operands of the same type")

    | LessEqual ->
        if (first = IntType && second = IntType) || (first = FloatType && second = FloatType) then BoolType
        else raise (TypeError "LessEqual operation requires numeric operands of the same type")

    | GreaterEqual ->
        if (first = IntType && second = IntType) || (first = FloatType && second = FloatType) then BoolType
        else raise (TypeError "GreaterEqual operation requires numeric operands of the same type")

    | And ->
        if first = BoolType && second = BoolType then BoolType
        else raise (TypeError "And operation requires boolean operands")

    | Or ->
        if first = BoolType && second = BoolType then BoolType
        else raise (TypeError "Or operation requires boolean operands"))

  | UnOp_Ad (sign, e) ->
      let first = type_of env e in
      (match sign with
       | Not -> 
           if first = BoolType then BoolType
           else raise (TypeError "Not operation should be a boolean operand")
           
       | Transpose ->
           (match first with
            | MatrixTypeInt (row, column) -> MatrixTypeInt (column, row)
            | MatrixTypeFloat (row, column) -> MatrixTypeFloat (column, row)
            | _ -> raise (TypeError "Transpose operation should be a matrix"))
           
       | Inverse ->
           (match first with
            | FloatType -> FloatType
            | IntType -> IntType
            | _ -> raise (TypeError "Inverse operation should be a scalar or an integer"))
           
       | InverseVector ->
           (match first with
            | VectorTypeInt n -> VectorTypeInt n
            | VectorTypeFloat n -> VectorTypeFloat n
            | _ -> raise (TypeError "Vector inverse operation should be a vector"))
           
       | InverseMatrix -> (match first with
            | MatrixTypeInt (row, column) when row = column -> MatrixTypeInt (row, column)
            | MatrixTypeFloat (row, column) when row = column -> MatrixTypeFloat (row, column)
            | _ -> raise (TypeError "Matrix inverse operation needs a square matrix"))
           
       | Determinant -> (match first with
            | MatrixTypeInt (row, column) when row = column -> IntType
            | MatrixTypeFloat (row, column) when row = column -> FloatType
            | _ -> raise (TypeError "Determinant operation needs a square matrix"))
           
       | Magnitude -> (match first with
            | VectorTypeInt _ -> FloatType
            | VectorTypeFloat _ -> FloatType
            | _ -> raise (TypeError "Magnitude operation should be a vector"))
           
       | AbsFloat ->
           if first = FloatType then FloatType
           else raise (TypeError "Absolute value operation should be a scalar")
           
       | AbsInt ->
           if first = IntType then IntType
           else raise (TypeError "Absolute value operation should be an integer")
           
       | DimensionVector -> (match first with
            | VectorTypeInt _ -> IntType
            | VectorTypeFloat _ -> IntType
            | _ -> raise (TypeError "Vector dimension operation should be a vector"))
           
       | DimensionMatrix -> (match first with
            | MatrixTypeInt _ -> IntType
            | MatrixTypeFloat _ -> IntType  
            | _ -> raise (TypeError "Matrix dimension operation should be a matrix")))
           
  | Angle (v1, v2) ->
      let first = type_of env v1 in
      let second = type_of env v2 in
      (match first, second with
       | VectorTypeInt n1, VectorTypeInt n2 when n1 = n2 -> FloatType
       | VectorTypeFloat n1, VectorTypeFloat n2 when n1 = n2 -> FloatType
       | _, _ -> raise (TypeError "Angle function requires two vectors of the same dimension"))
  
  | NullExpr -> UnitType

and check_line env lines =
    let rec check_list current_env = function
      | [] -> current_env
      | s :: rest -> 
          let env' = check_stmt current_env s in
          check_list env' rest
    in
    check_list env lines
  
    and check_stmt env = function
  | Assign (var_name, expr) ->
      let expr_type = type_of env expr in
      if expr_type <> UnitType then Hashtbl.replace env var_name expr_type;
      env
  
  | IfElse (cond, then_stmt, else_stmt) ->
      let cond_type = type_of env cond in
      if cond_type <> BoolType then
        raise (TypeError "Condition in if-else must be boolean");
      let _ = check_stmt env then_stmt in
      let _ = check_stmt env else_stmt in
      env
      
  | For (var, start, stop, body) ->
      let start_type = type_of env start in
      let stop_type = type_of env stop in
      if start_type <> IntType || stop_type <> IntType then
        raise (TypeError "For loop bounds must be integers");
        
      let loop_env = type_of env start in
      if loop_env <> UnitType then Hashtbl.replace env var loop_env;
        env
      
  | While (cond, body) ->
      let cond_type = type_of env cond in
      if cond_type <> BoolType then
        raise (TypeError "Condition in while loop must be boolean");
      let _ = check_stmt env body in
      env
      
  | Block lines ->
      check_line env lines
      
  | ExprStmt expr ->
      let _ = type_of env expr in
      env
      
  | InputStmt _ -> env 

  | Input -> env
         
   | PrintStmt var ->
        if Hashtbl.mem env var then env
        else raise (TypeError (Printf.sprintf "Undefined variable in Print: %s" var))
    

let check_program (program: program) : unit =
  let env = Hashtbl.create 100 in
  let _ = check_line env program in
  ()


