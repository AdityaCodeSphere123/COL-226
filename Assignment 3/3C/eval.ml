(* Aditya Anand: 2023CS50284 *)

open Ast
open Typechecker

exception DimensionError of string
exception DivisionError of string
exception TypeError of string
exception RuntimeError of string

(* Value types corresponding to your AST types *)
type value =
  | BoolVal of bool
  | IntVal of int
  | ScalarVal of float
  | VectorVal_Int of int list
  | MatrixVal_Int of int list list
  | VectorVal_Float of float list
  | MatrixVal_Float of float list list

(* Environment for variable storage *)
module Env = struct
  type t = (string, value) Hashtbl.t
  let create () = Hashtbl.create 100
  let find x env =
    try Hashtbl.find env x
    with Not_found -> raise (RuntimeError ("Unbound variable: " ^ x))
  let add x v env = Hashtbl.replace env x v
end

(* Custom implementation of split_on_string *)
let split_on_string sep str =
  let rec aux acc start =
    try
      let idx = String.index_from str start (String.get sep 0) in
      if String.sub str idx (String.length sep) = sep then
        aux (String.sub str start (idx - start) :: acc) (idx + String.length sep)
      else
        aux acc (idx + 1)
    with Not_found ->
      List.rev (String.sub str start (String.length str - start) :: acc)
  in
  aux [] 0

(* Vector operations for float vectors *)
module Vectors = struct
  type vector = float list 
  
  let create n x =
    if n < 1 then raise (DimensionError ("Vector dimension must be positive, got " ^ (string_of_int n)))
    else List.init n (fun _ -> x)
  
  let dim v = List.length v
  
  let scale c v = List.map (( *. ) c) v
  
  let addv v1 v2 =
    if dim v1 = dim v2 then List.map2 ( +. ) v1 v2
    else raise (DimensionError ("Vectors must have the same dimension for addition, got " ^ (string_of_int (dim v1)) ^ " and " ^ (string_of_int (dim v2))))
 
  let dot_prod v1 v2 =
    if dim v1 = dim v2 then List.fold_left2 (fun acc x y -> acc +. (x *. y)) 0.0 v1 v2
    else raise (DimensionError ("Vectors must have the same dimension for dot product, got " ^ (string_of_int (dim v1)) ^ " and " ^ (string_of_int (dim v2))))
  
  let inv v = scale (-1.0) v
  
  let length v = sqrt (List.fold_left (fun acc x -> acc +. (x *. x)) 0.0 v)
  
  let angle v1 v2 =
    let dot = dot_prod v1 v2 in
    let len1, len2 = length v1, length v2 in
    if len1 = 0.0 || len2 = 0.0 then raise (DivisionError "Cannot calculate angle with a zero-length vector")
    else acos (max (-1.0) (min 1.0 (dot /. (len1 *. len2))))
end
(* Vector operations for int vectors *)
module Vectors_Int = struct
  let addv v1 v2 =
    if List.length v1 = List.length v2 then
      List.map2 ( + ) v1 v2
    else
      raise (DimensionError ("Cannot add vectors of different dimensions. Expected vectors of same length, but got " ^ string_of_int (List.length v1) ^ " and " ^ string_of_int (List.length v2)))

  let dot_prod v1 v2 =
    if List.length v1 = List.length v2 then
      List.fold_left2 (fun acc a b -> acc + a * b) 0 v1 v2
    else
      raise (DimensionError ("Cannot compute dot product of vectors with different dimensions. Expected vectors of same length, but got " ^ string_of_int (List.length v1) ^ " and " ^ string_of_int (List.length v2)))

  let scale s v = List.map (fun x -> s * x) v

  let inv v = List.map (fun x -> -x) v

  let length v =
    let sum_of_squares = List.fold_left (fun acc x -> acc + x * x) 0 v in
    sqrt (float_of_int sum_of_squares)

  let angle v1 v2 =
    let dot = float_of_int (dot_prod v1 v2) in
    let len1 = length v1 in
    let len2 = length v2 in
    if len1 = 0.0 || len2 = 0.0 then
      raise (DivisionError "Cannot compute angle with a zero-length vector.")
    else
      acos (max (-1.0) (min 1.0 (dot /. (len1 *. len2))))
end

(* Matrix operations for float matrices *)
module Matrices = struct
  type matrix = float list list
  
  let create rows cols x =
    if rows < 1 || cols < 1 then
      raise (DimensionError ("Matrix dimensions must be positive. Rows: " ^ string_of_int rows ^ ", Cols: " ^ string_of_int cols))
    else
      List.init rows (fun _ -> List.init cols (fun _ -> x))
  
  let dim m =
    (List.length m, if m = [] then 0 else List.length (List.hd m))
  
  let addm m1 m2 =
    if dim m1 = dim m2 then
      List.map2 (fun r1 r2 -> List.map2 ( +. ) r1 r2) m1 m2
    else
      raise (DimensionError ("Cannot add matrices with different dimensions."))
  let scalarmul c m =
    List.map (List.map (( *. ) c)) m
  
  let transpose m =
    if m = [] then
      []
    else
      List.init (snd (dim m)) (fun i -> List.map (fun row -> List.nth row i) m)
  
  let matmul m1 m2 =
    let (r1, c1) = dim m1 in
    let (r2, c2) = dim m2 in
    if c1 <> r2 then
      raise (DimensionError ("Cannot multiply matrices. Incompatible dimensions: " ^ string_of_int c1 ^ " (columns of first matrix) and " ^ string_of_int r2 ^ " (rows of second matrix)."))
    else
      List.init r1 (fun i ->
        List.init c2 (fun j ->
          List.fold_left2 (fun acc x y -> acc +. (x *. y))
            0.0 (List.nth m1 i)
            (List.map (fun row -> List.nth row j) m2)
        ))
      
  let det m =
          let rec det_recursive mat =
            let rows = List.length mat in
            if rows = 1 then 
              List.hd (List.hd mat) (* Determinant of 1x1 matrix *)
            else if rows = 2 then
              (* Optimize for 2x2 case: ad - bc *)
              let a = List.hd (List.hd mat) in
              let b = List.nth (List.hd mat) 1 in
              let c = List.hd (List.nth mat 1) in
              let d = List.nth (List.nth mat 1) 1 in
              a *. d -. b *. c
            else
              let first_row = List.hd mat in
              let minor_cofactor col_index =
                let submatrix =
                  List.tl mat
                  |> List.map (fun row ->
                       List.filteri (fun i _ -> i <> col_index) row)
                in
                let element = List.nth first_row col_index in
                let sign = if col_index mod 2 = 0 then 1.0 else -1.0 in
                sign *. element *. det_recursive submatrix
              in
              let indices = List.init (List.length first_row) (fun i -> i) in
              List.fold_left (fun acc col -> acc +. minor_cofactor col) 0.0 indices
          in
          
          let rows = List.length m in
          let cols = match m with
            | [] -> 0
            | first_row -> List.length first_row
          in
          
          if rows <> cols then
            raise (Invalid_argument "Determinant can only be calculated for square matrices.")
          else if rows = 0 then
            0.0 (* More conventional for an empty matrix *)
          else if rows = 1 then
            List.hd (List.hd m) (* Handle 1x1 matrix directly *)
          else
            det_recursive m
        
  (* Simple matrix inversion for 2x2 matrices *)
  let inverse m =
    let (rows, cols) = dim m in
    if rows <> cols then
      raise (DimensionError "Cannot invert non-square matrix.")
    else
      match rows with
      | 1 -> 
          let a = List.hd (List.hd m) in
          if a = 0.0 then
            raise (DivisionError "Cannot invert a 1x1 matrix with zero determinant.")
          else
            [[1.0 /. a]]
      | 2 ->
          let a = List.nth (List.nth m 0) 0 in
          let b = List.nth (List.nth m 0) 1 in
          let c = List.nth (List.nth m 1) 0 in
          let d = List.nth (List.nth m 1) 1 in
          let det = a *. d -. b *. c in
          if det = 0.0 then
            raise (DivisionError "Cannot invert a matrix with zero determinant.")
          else
            let inv_det = 1.0 /. det in
            [[d *. inv_det; -. b *. inv_det]; 
             [-. c *. inv_det; a *. inv_det]]
      | _ ->
          raise (RuntimeError "Only Implemented Matrix inversion for matrices up to 2x2.")
end
(* Matrix operations for integer matrices *)
module Matrices_Int = struct

  (* Add two integer matrices. Matrices must have the same dimensions. *)
  let addm m1 m2 =
    let dim1 = (List.length m1, if m1 = [] then 0 else List.length (List.hd m1)) in
    let dim2 = (List.length m2, if m2 = [] then 0 else List.length (List.hd m2)) in
    if dim1 <> dim2 then
      raise (DimensionError "Matrices must have the same dimensions to be added.")
    else
      List.map2 (fun row1 row2 -> List.map2 ( + ) row1 row2) m1 m2

  (* Multiply an integer matrix by a scalar. *)
  let scalarmul s m =
    List.map (fun row -> List.map (fun x -> s * x) row) m

  (* Get the dimensions (rows, columns) of an integer matrix. *)
  let dim m =
    let rows = List.length m in
    let cols = if rows = 0 then 0 else List.length (List.hd m) in
    (rows, cols)

  (* Transpose an integer matrix. *)
  let transpose m =
    if m = [] then
      []
    else
      let (_, cols) = dim m in
      List.init cols (fun j -> List.map (fun row -> List.nth row j) m)

  (* Multiply two integer matrices. The number of columns in the first matrix 
     must equal the number of rows in the second matrix. *)
  let matmul m1 m2 =
    let (rows1, cols1) = dim m1 in
    let (rows2, cols2) = dim m2 in
    if cols1 <> rows2 then
      raise (DimensionError "Matrices cannot be multiplied due to incompatible dimensions.")
    else
      List.init rows1 (fun i ->
        List.init cols2 (fun j ->
          let row = List.nth m1 i in
          let col = List.map (fun row -> List.nth row j) m2 in
          List.fold_left2 (fun acc a b -> acc + a * b) 0 row col
        ))

  (* Calculate the determinant of an integer matrix (2x2 and 3x3 only). *)
  let det m =
    let rec det_recursive mat =
      let rows = List.length mat in
      if rows = 1 then 
        List.hd (List.hd mat) (* Determinant of 1x1 matrix *)
      else if rows = 2 then
        (* Optimize for 2x2 case: ad - bc *)
        let a = List.hd (List.hd mat) in
        let b = List.nth (List.hd mat) 1 in
        let c = List.hd (List.nth mat 1) in
        let d = List.nth (List.nth mat 1) 1 in
        a * d - b * c
      else
        let first_row = List.hd mat in
        let minor_cofactor col_index =
          let submatrix =
            List.tl mat
            |> List.map (fun row ->
                 List.filteri (fun i _ -> i <> col_index) row)
          in
          let element = List.nth first_row col_index in
          let sign = if col_index mod 2 = 0 then 1 else -1 in
          sign * element * det_recursive submatrix
        in
        let indices = List.init (List.length first_row) (fun i -> i) in
        List.fold_left (fun acc col -> acc + minor_cofactor col) 0 indices
    in
    
    let rows = List.length m in
    let cols = match m with
      | [] -> 0
      | first_row -> List.length first_row
    in
    
    if rows <> cols then
      raise (Invalid_argument "Determinant can only be calculated for square matrices.")
    else if rows = 0 then
      0 (* More conventional for an empty matrix *)
    else if rows = 1 then
      List.hd (List.hd m) (* Handle 1x1 matrix directly *)
    else
      det_recursive m
  
  let inverse m =
    let (rows, cols) = dim m in
    if rows <> cols then
      raise (DimensionError "Inverse can only be calculated for square matrices.")
    else
      match rows with
      | 1 ->
          let a = float_of_int (List.hd (List.hd m)) in
          if a = 0.0 then
            raise (DivisionError "Cannot invert a 1x1 matrix with a zero element.")
          else
            [[1.0 /. a]]
      | 2 ->
          let a = float_of_int (List.nth (List.nth m 0) 0) in
          let b = float_of_int (List.nth (List.nth m 0) 1) in
          let c = float_of_int (List.nth (List.nth m 1) 0) in
          let d = float_of_int (List.nth (List.nth m 1) 1) in
          let det = (a *. d) -. (b *. c) in
          if det = 0.0 then
            raise (DivisionError "Cannot invert a matrix with a zero determinant.")
          else
            let inv_det = 1.0 /. det in
            [[d *. inv_det; -. b *. inv_det];
             [-. c *. inv_det; a *. inv_det]]
      | _ ->
        raise (RuntimeError "Only Implemented Matrix inversion for matrices up to 2x2.")

end

(* Expression evaluation: for expressions of type Ast.express *)
let rec eval_expr (env : Env.t) (e : Ast.express) : value =
  match e with
  | Bool_Ad b -> BoolVal b
  | Int_Ad n -> IntVal n
  | Float_Ad f -> ScalarVal f
  | VectorInt_Ad (dim, lst) ->  
    if List.length lst = dim then VectorVal_Int lst  
    else raise (DimensionError "Vector dimension mismatch")  

  | VectorFloat_Ad (dim, lst) ->  
    if List.length lst = dim then VectorVal_Float lst  
    else raise (DimensionError "Vector dimension mismatch")  

  | MatrixInt_Ad (rows, cols, m) ->  
    let m_list = Array.to_list m |> List.map Array.to_list in  
    if List.length m_list = rows && not (List.exists (fun row -> List.length row <> cols) m_list) then  
      MatrixVal_Int m_list  
    else raise (DimensionError "Matrix dimension mismatch")  

  | MatrixFloat_Ad (rows, cols, m) ->  
    let m_list = Array.to_list m |> List.map Array.to_list in  
    if List.length m_list = rows && not (List.exists (fun row -> List.length row <> cols) m_list) then  
      MatrixVal_Float m_list  
    else raise (DimensionError "Matrix dimension mismatch")  
  | Var_Ad x -> Env.find x env 
  | Assign (x, e) ->
    let v = eval_expr env e in
    Env.add x v env;
    v

  | Create_bool var_name ->
      if Hashtbl.mem env var_name then
        raise (RuntimeError (Printf.sprintf "Variable '%s' is already defined" var_name))
      else (
        Env.add var_name (BoolVal true) env;  (* Default value: true *)
        BoolVal true
      )
  
  | Create_int var_name ->
      if Hashtbl.mem env var_name then
        raise (RuntimeError (Printf.sprintf "Variable '%s' is already defined" var_name))
      else (
        Env.add var_name (IntVal 0) env;  (* Default value: 0 *)
        IntVal 0
      )
  
  | Create_float var_name ->
      if Hashtbl.mem env var_name then
        raise (RuntimeError (Printf.sprintf "Variable '%s' is already defined" var_name))
      else (
        Env.add var_name (ScalarVal 0.0) env;  (* Default value: 0.0 *)
        ScalarVal 0.0
      )
  
  | Create_vecint (var_name, size) ->
      if Hashtbl.mem env var_name then
        raise (RuntimeError (Printf.sprintf "Variable '%s' is already defined" var_name))
      else if size <= 0 then
        raise (RuntimeError "Vector size must be greater than 0")
      else (
        let default_vector = List.init size (fun _ -> 0) in  (* Default values: [0, 0, ..., 0] *)
        Env.add var_name (VectorVal_Int default_vector) env;
        VectorVal_Int default_vector
      )
  | Create_vecfloat (var_name, size) ->
      if Hashtbl.mem env var_name then
        raise (RuntimeError (Printf.sprintf "Variable '%s' is already defined" var_name))
      else if size <= 0 then
        raise (RuntimeError "Vector size must be greater than 0")
      else (
        let default_vector = List.init size (fun _ -> 0.0) in  (* Default values: [0.0, 0.0, ..., 0.0] *)
        Env.add var_name (VectorVal_Float default_vector) env;
        VectorVal_Float default_vector
      )
  
  | Create_matint (var_name, rows, cols) ->
      if Hashtbl.mem env var_name then
        raise (RuntimeError (Printf.sprintf "Variable '%s' is already defined" var_name))
      else if rows <= 0 || cols <= 0 then
        raise (RuntimeError "Matrix dimensions must be greater than 0")
      else (
        let default_matrix = List.init rows (fun _ -> List.init cols (fun _ -> 0)) in  (* Default values: 0 *)
        Env.add var_name (MatrixVal_Int default_matrix) env;
        MatrixVal_Int default_matrix
      )
  
  | Create_matfloat (var_name, rows, cols) ->
      if Hashtbl.mem env var_name then
        raise (RuntimeError (Printf.sprintf "Variable '%s' is already defined" var_name))
      else if rows <= 0 || cols <= 0 then
        raise (RuntimeError "Matrix dimensions must be greater than 0")
      else (
        let default_matrix = List.init rows (fun _ -> List.init cols (fun _ -> 0.0)) in  (* Default values: 0.0 *)
        Env.add var_name (MatrixVal_Float default_matrix) env;
        MatrixVal_Float default_matrix
      )
  | BinOp_Ad (op, e1, e2) ->
      (match op, eval_expr env e1, eval_expr env e2 with
       (* Integer arithmetic *)
       | PlusInt, IntVal i1, IntVal i2 -> IntVal (i1 + i2)
       | MinusInt, IntVal i1, IntVal i2 -> IntVal (i1 - i2)
       | TimesInt, IntVal i1, IntVal i2 -> IntVal (i1 * i2)
       | DivideInt, IntVal i1, IntVal i2 ->  
        if i2 = 0 then raise (DivisionError "Division by zero")  
        else IntVal (i1 / i2)  
    
       | Modulus, IntVal i1, IntVal i2 ->  
            if i2 = 0 then raise (DivisionError "Modulo by zero")  
            else IntVal (i1 mod i2)  
        
       | Power, IntVal i1, IntVal i2 ->  
            if i2 < 0 then raise (DivisionError "Negative exponent in integer power operation")  
            else IntVal (int_of_float ((float_of_int i1) ** (float_of_int i2)))  
        
    
    
       (* Floating point arithmetic *)
       | PlusFloat, ScalarVal f1, ScalarVal f2 -> ScalarVal (f1 +. f2)
       | MinusFloat, ScalarVal f1, ScalarVal f2 -> ScalarVal (f1 -. f2)
       | TimesFloat, ScalarVal f1, ScalarVal f2 -> ScalarVal (f1 *. f2)
       | DivideFloat, ScalarVal f1, ScalarVal f2 ->  
        if f2 = 0.0 then raise (DivisionError "Division by zero")  
        else ScalarVal (f1 /. f2)  
       (* Vector addition *)
       | AddVector, VectorVal_Int v1, VectorVal_Int v2 ->
           VectorVal_Int (Vectors_Int.addv v1 v2)
       | AddVector, VectorVal_Float v1, VectorVal_Float v2 ->
           VectorVal_Float (Vectors.addv v1 v2)
       (* Scalar multiplication with vectors *)
       | ScalarMultiply, IntVal i, VectorVal_Int v ->
           VectorVal_Int (Vectors_Int.scale i v)
       | ScalarMultiply, VectorVal_Int v, IntVal i ->
           VectorVal_Int (Vectors_Int.scale i v)
       | ScalarMultiply, ScalarVal f, VectorVal_Float v ->
           VectorVal_Float (Vectors.scale f v)
       | ScalarMultiply, VectorVal_Float v, ScalarVal f ->
           VectorVal_Float (Vectors.scale f v)
       (* Matrix addition *)
       | AddMatrix, MatrixVal_Int m1, MatrixVal_Int m2 ->
           MatrixVal_Int (Matrices_Int.addm m1 m2)
       | AddMatrix, MatrixVal_Float m1, MatrixVal_Float m2 ->
           MatrixVal_Float (Matrices.addm m1 m2)
       (* Scalar multiplication with matrices *)
       | ScalarMatrixMultiply, IntVal i, MatrixVal_Int m ->
           MatrixVal_Int (Matrices_Int.scalarmul i m)
       | ScalarMatrixMultiply, MatrixVal_Int m, IntVal i ->
           MatrixVal_Int (Matrices_Int.scalarmul i m)
       | ScalarMatrixMultiply, ScalarVal f, MatrixVal_Float m ->
           MatrixVal_Float (Matrices.scalarmul f m)
       | ScalarMatrixMultiply, MatrixVal_Float m, ScalarVal f ->
           MatrixVal_Float (Matrices.scalarmul f m)
       (* Matrix multiplication *)
       | MatrixMultiply, MatrixVal_Int m1, MatrixVal_Int m2 ->
           MatrixVal_Int (Matrices_Int.matmul m1 m2)
       | MatrixMultiply, MatrixVal_Float m1, MatrixVal_Float m2 ->
           MatrixVal_Float (Matrices.matmul m1 m2)
            (* Case 1: Vector (1 x n) multiplied by Matrix (n x m) *)
       | VectorMultiply, VectorVal_Int vec, MatrixVal_Int mat ->
                if List.length vec <> List.length mat then
                  raise (RuntimeError "Vector and matrix dimensions are incompatible for multiplication")
                else
                  let result = List.map (fun col ->
               List.fold_left2 (fun acc v m -> acc + (v * m)) 0 vec col
                  ) (Matrices_Int.transpose mat) in
                  VectorVal_Int result

       | VectorMultiply, VectorVal_Float vec, MatrixVal_Float mat ->
                if List.length vec <> List.length mat then
                  raise (RuntimeError "Vector and matrix dimensions are incompatible for multiplication")
                else
                  let result = List.map (fun col ->
               List.fold_left2 (fun acc v m -> acc +. (v *. m)) 0.0 vec col
                  ) (Matrices.transpose mat) in
                  VectorVal_Float result

            (* Case 2: Matrix (n x m) multiplied by Vector (1 x m) *)
       | VectorMultiply, MatrixVal_Int mat, VectorVal_Int vec ->
                if List.length (List.hd mat) <> List.length vec then
                  raise (RuntimeError "Matrix and vector dimensions are incompatible for multiplication")
                else
                  let result = List.map (fun row ->
               List.fold_left2 (fun acc m v -> acc + (m * v)) 0 row vec
                  ) mat in
                  VectorVal_Int result

       | VectorMultiply, MatrixVal_Float mat, VectorVal_Float vec ->
                if List.length (List.hd mat) <> List.length vec then
                  raise (RuntimeError "Matrix and vector dimensions are incompatible for multiplication")
                else
                  let result = List.map (fun row ->
               List.fold_left2 (fun acc m v -> acc +. (m *. v)) 0.0 row vec
                  ) mat in
                  VectorVal_Float result
       (* Dot product *)
       | DotProduct, VectorVal_Int v1, VectorVal_Int v2 ->
           IntVal (Vectors_Int.dot_prod v1 v2)
       | DotProduct, VectorVal_Float v1, VectorVal_Float v2 ->
           ScalarVal (Vectors.dot_prod v1 v2)
       (* Equality and inequality *)
       | Equal, v1, v2 -> BoolVal (v1 = v2)
       | NotEqual, v1, v2 -> BoolVal (v1 <> v2)
       (* Less than, greater than, etc. *)
       | Less, IntVal i1, IntVal i2 -> BoolVal (i1 < i2)
       | LessEqual, IntVal i1, IntVal i2 -> BoolVal (i1 <= i2)
       | Greater, IntVal i1, IntVal i2 -> BoolVal (i1 > i2)
       | GreaterEqual, IntVal i1, IntVal i2 -> BoolVal (i1 >= i2)
       | Less, ScalarVal f1, ScalarVal f2 -> BoolVal (f1 < f2)
       | LessEqual, ScalarVal f1, ScalarVal f2 -> BoolVal (f1 <= f2)
       | Greater, ScalarVal f1, ScalarVal f2 -> BoolVal (f1 > f2)
       | GreaterEqual, ScalarVal f1, ScalarVal f2 -> BoolVal (f1 >= f2)
       (* Logical operators *)
       | And, BoolVal b1, BoolVal b2 -> BoolVal (b1 && b2)
       | Or, BoolVal b1, BoolVal b2 -> BoolVal (b1 || b2)
       | _ -> raise (TypeError "Invalid operation: Type mismatch in expression")
 
  )
  | UnOp_Ad (op, e1) ->
      (match op, eval_expr env e1 with
       | Not, BoolVal b -> BoolVal (not b)
       | Transpose, MatrixVal_Int m ->
           MatrixVal_Int (Matrices_Int.transpose m)
       | Transpose, MatrixVal_Float m ->
           MatrixVal_Float (Matrices.transpose m)
       | SquareRoot, ScalarVal f ->
           if f < 0.0 then raise (RuntimeError "Square root of negative number")
           else ScalarVal (sqrt f)
       | SquareRoot, IntVal i ->
           if i < 0 then raise (RuntimeError "Square root of negative number")
           else ScalarVal (sqrt (float_of_int i))
       | Inverse, IntVal i ->
           IntVal (-i)
       | Inverse, ScalarVal f ->
           ScalarVal (-.f)
       | InverseVector, VectorVal_Int v -> VectorVal_Int (Vectors_Int.inv v)
       | InverseVector, VectorVal_Float v -> VectorVal_Float (Vectors.inv v)
       | InverseMatrix, MatrixVal_Int m -> MatrixVal_Float (Matrices_Int.inverse m)
       | InverseMatrix, MatrixVal_Float m ->
           MatrixVal_Float (Matrices.inverse m)
       | Determinant, MatrixVal_Int m ->
           IntVal (Matrices_Int.det m)
       | Determinant, MatrixVal_Float m ->
           ScalarVal (Matrices.det m)
       | Magnitude, VectorVal_Int v ->
           ScalarVal (Vectors_Int.length v)
       | Magnitude, VectorVal_Float v ->
           ScalarVal (Vectors.length v)
       | AbsFloat, ScalarVal f -> ScalarVal (abs_float f)
       | AbsInt, IntVal i -> IntVal (abs i)
       | DimensionVector, VectorVal_Int v -> IntVal (List.length v)
       | DimensionVector, VectorVal_Float v -> IntVal (List.length v)
       | DimensionMatrix, MatrixVal_Int m ->
        let rows = List.length m in
        let cols = if m = [] then 0 else List.length (List.hd m) in
        VectorVal_Int [rows; cols]
       | DimensionMatrix, MatrixVal_Float m ->
        let rows = List.length m in
        let cols = if m = [] then 0 else List.length (List.hd m) in
        VectorVal_Int [rows; cols]
        | _ -> raise (TypeError "Invalid operation: Type mismatch in expression")
       
  )

  | Angle (e1, e2) ->
      (match eval_expr env e1, eval_expr env e2 with
       | VectorVal_Int v1, VectorVal_Int v2 ->
           ScalarVal (Vectors_Int.angle v1 v2)
       | VectorVal_Float v1, VectorVal_Float v2 ->
           ScalarVal (Vectors.angle v1 v2)
           | _ -> raise (TypeError "Angle operation requires two vectors of the same type (integer or float)")
        )
  | IndexVec (var, index_expr) -> (
        match eval_expr env index_expr with
        | IntVal idx -> (
            match Env.find var env with
            | VectorVal_Int lst -> 
                if idx < 0 || idx >= List.length lst then 
                  raise (RuntimeError "Vector index out of bounds: Ensure index is within valid range")
                else IntVal (List.nth lst idx)
            | VectorVal_Float lst -> 
                if idx < 0 || idx >= List.length lst then 
                  raise (RuntimeError "Vector index out of bounds: Ensure index is within valid range")
                else ScalarVal (List.nth lst idx)
                | _ -> raise (RuntimeError "Invalid operation: Cannot index a non-vector variable"))
        | _ -> raise (RuntimeError "Vector index must be an integer value"))
      
  | IndexMat (var, row_expr, col_expr) -> (
        match eval_expr env row_expr, eval_expr env col_expr with
        | IntVal row, IntVal col -> (
            match Env.find var env with
            | MatrixVal_Int mat -> 
                if row < 0 || row >= List.length mat || 
                   col < 0 || col >= (if mat = [] then 0 else List.length (List.hd mat)) then
                  raise (RuntimeError "Matrix indices out of bounds: Ensure row and column indices are within valid range")
                else IntVal (List.nth (List.nth mat row) col)
            | MatrixVal_Float mat -> 
                if row < 0 || row >= List.length mat || 
                   col < 0 || col >= (if mat = [] then 0 else List.length (List.hd mat)) then
                  raise (RuntimeError "Matrix indices out of bounds: Ensure row and column indices are within valid range")
                else ScalarVal (List.nth (List.nth mat row) col)
                | _ -> raise (RuntimeError "Invalid operation: Cannot index a non-matrix variable"))
                | _ -> raise (RuntimeError "Matrix index must be an integer value"))
  | AssignVec (var, index_expr, value_expr) -> (
                  match eval_expr env index_expr with
                  | IntVal idx -> (
                      match Env.find var env with
                      | VectorVal_Int lst -> (
                          if idx < 0 || idx >= List.length lst then
                            raise (RuntimeError "Vector index out of bounds: Ensure index is within valid range")
                          else
                            match eval_expr env value_expr with
                            | IntVal v -> 
                                Env.add var (VectorVal_Int (List.mapi (fun i x -> if i = idx then v else x) lst)) env;
                                IntVal v
                            | _ -> raise (RuntimeError "Type mismatch: Cannot assign non-integer value to integer vector"))
                      | VectorVal_Float lst -> (
                          if idx < 0 || idx >= List.length lst then
                            raise (RuntimeError "Vector index out of bounds: Ensure index is within valid range")
                          else
                            match eval_expr env value_expr with
                            | ScalarVal v -> 
                                Env.add var (VectorVal_Float (List.mapi (fun i x -> if i = idx then v else x) lst)) env;
                                ScalarVal v
                            | IntVal v ->
                                let v_float = float_of_int v in
                                Env.add var (VectorVal_Float (List.mapi (fun i x -> if i = idx then v_float else x) lst)) env;
                                ScalarVal v_float
                            | _ -> raise (RuntimeError "Type mismatch: Cannot assign non-numeric value to float vector"))
                      | _ -> raise (RuntimeError "Invalid operation: Cannot assign to a non-vector variable"))
                  | _ -> raise (RuntimeError "Vector index must be an integer value"))
  | AssignMat (var, row_expr, col_expr, value_expr) -> (
                    match eval_expr env row_expr, eval_expr env col_expr with
                    | IntVal row, IntVal col -> (
                        match Env.find var env with
                        | MatrixVal_Int mat -> (
                            if row < 0 || row >= List.length mat || col < 0 || col >= List.length (List.hd mat) then
                              raise (RuntimeError "Matrix indices out of bounds: Ensure row and column indices are within valid range")
                            else
                              match eval_expr env value_expr with
                              | IntVal v -> 
                                  Env.add var (MatrixVal_Int (List.mapi (fun i r -> 
                                    if i = row then List.mapi (fun j x -> if j = col then v else x) r 
                                    else r) mat)) env;
                                  IntVal v
                              | _ -> raise (RuntimeError "Type mismatch: Cannot assign non-integer value to integer matrix"))
                        | MatrixVal_Float mat -> (
                            if row < 0 || row >= List.length mat || col < 0 || col >= List.length (List.hd mat) then
                              raise (RuntimeError "Matrix indices out of bounds: Ensure row and column indices are within valid range")
                            else
                              match eval_expr env value_expr with
                              | ScalarVal v -> 
                                  Env.add var (MatrixVal_Float (List.mapi (fun i r -> 
                                    if i = row then List.mapi (fun j x -> if j = col then v else x) r 
                                    else r) mat)) env;
                                  ScalarVal v
                              | IntVal v ->
                                  let v_float = float_of_int v in
                                  Env.add var (MatrixVal_Float (List.mapi (fun i r -> 
                                    if i = row then List.mapi (fun j x -> if j = col then v_float else x) r 
                                    else r) mat)) env;
                                  ScalarVal v_float
                              | _ -> raise (RuntimeError "Type mismatch: Cannot assign non-numeric value to float matrix"))
                        | _ -> raise (RuntimeError "Invalid operation: Cannot assign to a non-matrix variable"))
                    | _ -> raise (RuntimeError "Matrix index must be an integer value"))
      
  | NullExpr -> raise (RuntimeError "Cannot evaluate a null expression")

  | Minor (matrix_expr, row, col) ->
    let matrix_val = eval_expr env matrix_expr in
    (match matrix_val with
     | MatrixVal_Int mat ->
         if row < 0 || row >= List.length mat || col < 0 || col >= List.length (List.hd mat) then
           raise (RuntimeError "Row or column index out of bounds")
         else
           let minor_matrix =
             List.mapi (fun i row_list ->
               if i = row then None
               else Some (List.mapi (fun j elem -> if j = col then None else Some elem) row_list
                          |> List.filter_map Fun.id))
               mat
             |> List.filter_map Fun.id
           in
           MatrixVal_Int minor_matrix

     | MatrixVal_Float mat ->
         if row < 0 || row >= List.length mat || col < 0 || col >= List.length (List.hd mat) then
           raise (RuntimeError "Row or column index out of bounds")
         else
           let minor_matrix =
             List.mapi (fun i row_list ->
               if i = row then None
               else Some (List.mapi (fun j elem -> if j = col then None else Some elem) row_list
                          |> List.filter_map Fun.id))
               mat
             |> List.filter_map Fun.id
           in
           MatrixVal_Float minor_matrix

     | _ ->
         raise (RuntimeError "Minor operation requires a matrix and two integer indices"))
  | File_Ad filename -> (
    try
      let file = open_in (String.trim filename) in
      try
        let rec read_lines acc =
          match input_line file with
          | line -> read_lines (line :: acc)
          | exception End_of_file -> List.rev acc
        in
        let lines = read_lines [] in
        close_in file;
        
        match lines with
        | [] -> raise (RuntimeError "File is empty or contains no valid data")
        | _ -> VectorVal_Float (List.map float_of_string lines)
      with
      | Failure _ -> (close_in_noerr file; raise (RuntimeError "File contains non-numeric data"))
      | e -> (close_in_noerr file; raise e)
    with
    | Sys_error msg -> raise (RuntimeError ("File error: " ^ msg))
 )

 | Input(var) ->
    (* Prompt for first line *)
    print_string "Enter the input: ";
    flush stdout;
    let line1 = read_line () in
    (* Prompt for second line *)
    print_string " ";
    flush stdout;
    let line2 = read_line () in
    if String.trim line2 = "" then
      (* Single value input: try int, then float, then bool *)
      (try
        let v = int_of_string (String.trim line1) in
        Env.add var (IntVal v) env;
        IntVal v
      with Failure _ ->
        try
          let v = float_of_string (String.trim line1) in
          Env.add var (ScalarVal v) env;
          ScalarVal v
        with Failure _ ->
          if String.trim line1 = "true" then
            (Env.add var (BoolVal true) env;
              BoolVal true)
          else if String.trim line1 = "false" then
            (Env.add var (BoolVal false) env;
              BoolVal false)
          else
            raise (RuntimeError "Invalid scalar input. Expected an integer, floating-point number, or boolean ('true'/'false')."))
    else
      (* Vector/Matrix input: second line must be enclosed in [[ ]] for matrices and [ ] for vectors *)
      let trimmed = String.trim line2 in
      let starts_with_double_bracket =
        String.length trimmed > 1 && String.sub trimmed 0 2 = "[[" in
      let ends_with_double_bracket =
        String.length trimmed > 1 && String.sub trimmed (String.length trimmed - 2) 2 = "]]" in
      let starts_with_bracket =
        String.length trimmed > 0 && trimmed.[0] = '[' in
      let ends_with_bracket =
        String.length trimmed > 0 && trimmed.[String.length trimmed - 1] = ']' in
      if starts_with_double_bracket && ends_with_double_bracket then
        (* Matrix input: remove outer brackets and split rows by "],[" *)
        let content = String.sub trimmed 2 (String.length trimmed - 4) |> String.trim in
        let row_strs = split_on_string "],[" content in
        let parsed_rows = List.map (fun row_str ->
          let row = String.trim row_str in
          let elems = String.split_on_char ',' row |> List.map String.trim in
          List.map (fun el ->
            try IntVal (int_of_string el)
            with Failure _ ->
              try ScalarVal (float_of_string el)
              with Failure _ -> raise (RuntimeError ("Invalid matrix element: '" ^ el ^ "'. Matrices must contain only integers or floating-point numbers."))
          ) elems
        ) row_strs in
        (* Check all rows have the same length *)
        let first_row_len =
          if parsed_rows = [] then 0
          else List.length (List.hd parsed_rows) in
        if not (List.for_all (fun row -> List.length row = first_row_len) parsed_rows) then
          raise (RuntimeError "Matrix dimensions mismatch: All rows must have the same number of elements.")
        else
          (* Determine whether all elements are ints *)
          let all_int =
            List.for_all (fun row ->
              List.for_all (function IntVal _ -> true | _ -> false) row
            ) parsed_rows in
          if all_int then
            let int_matrix = List.map (fun row ->
              List.map (function IntVal i -> i | _ -> failwith "impossible") row
            ) parsed_rows in
            (Env.add var (MatrixVal_Int int_matrix) env;
            MatrixVal_Int int_matrix)
          else
            let float_matrix = List.map (fun row ->
              List.map (function
                  | IntVal i -> float_of_int i
                  | ScalarVal f -> f
                  | _ -> failwith "impossible"
                ) row
            ) parsed_rows in
            (Env.add var (MatrixVal_Float float_matrix) env;
            MatrixVal_Float float_matrix)
      else if starts_with_bracket && ends_with_bracket then
        (* Vector input: remove outer brackets and split by commas *)
        let content = String.sub trimmed 1 (String.length trimmed - 2) |> String.trim in
        let elems = String.split_on_char ',' content |> List.map String.trim in
        let parsed_elems = List.map (fun el ->
          try IntVal (int_of_string el)
          with Failure _ ->
            try ScalarVal (float_of_string el)
            with Failure _ -> raise (RuntimeError ("Invalid vector element: '" ^ el ^ "'. Vectors must contain only integers or floating-point numbers."))
        ) elems in
        let all_int = List.for_all (function IntVal _ -> true | _ -> false) parsed_elems in
        if all_int then
          let int_vec = List.map (function IntVal i -> i | _ -> failwith "impossible") parsed_elems in
          (Env.add var (VectorVal_Int int_vec) env;
          VectorVal_Int int_vec)
        else
          let float_vec = List.map (function
              | IntVal i -> float_of_int i
              | ScalarVal f -> f
              | _ -> failwith "impossible"
            ) parsed_elems in
          (Env.add var (VectorVal_Float float_vec) env;
          VectorVal_Float float_vec)
      else
        raise (RuntimeError "Invalid input format. Matrices must be enclosed in double square brackets ([[...]]), and vectors must be enclosed in single square brackets ([...]).")
 | Input_File(var, f) ->
          let filename = f in
          try
            let file = open_in filename in
            let content = ref [] in
            (try
               while true do
                 content := input_line file :: !content
               done
             with End_of_file -> ());
            close_in file;
            let lines = List.rev !content in
            match lines with
            | [] ->
                raise (RuntimeError "Error: The input file is empty. Please provide a valid file with content.")
            | [line] ->
                (* Single-line file: try int, then float, then bool *)
                let trimmed_line = String.trim line in
                (try
                   let v = int_of_string trimmed_line in
                   Env.add var (IntVal v) env;
                   IntVal v
                 with Failure _ ->
                   try
                     let v = float_of_string trimmed_line in
                     Env.add var (ScalarVal v) env;
                     ScalarVal v
                   with Failure _ ->
                     if trimmed_line = "true" then
                       (Env.add var (BoolVal true) env;
                        BoolVal true)
                     else if trimmed_line = "false" then
                       (Env.add var (BoolVal false) env;
                        BoolVal false)
                     else
                       raise (RuntimeError "File contains unsupported values. Expected integer, float, or boolean data only."))
            | [dim_line; content_line] ->
                (* Two-line file: first line contains dimensions, second line the content *)
                let dims_tokens =
                  String.split_on_char ' ' (String.trim dim_line)
                  |> List.filter (fun s -> s <> "")
                in
                (match dims_tokens with
                 | [dim_str] ->
                     (* Vector input *)
                     let expected_dim = int_of_string dim_str in
                     let trimmed = String.trim content_line in
                     if not (String.length trimmed >= 2 &&
                             trimmed.[0] = '[' &&
                             trimmed.[String.length trimmed - 1] = ']') then
                       raise (RuntimeError "Invalid input format. Vectors must be enclosed in [ ]. Ensure correct syntax.")
                     else
                       let inner = String.sub trimmed 1 (String.length trimmed - 2)
                                   |> String.trim in
                       let elems = String.split_on_char ',' inner |> List.map String.trim in
                       if List.length elems <> expected_dim then
                         raise (RuntimeError "Mismatch between declared vector size and actual number of elements. Ensure correct dimensions.")
                       else
                         let parsed_elems = List.map (fun s ->
                           try IntVal (int_of_string s)
                           with Failure _ ->
                             try ScalarVal (float_of_string s)
                             with Failure _ -> raise (RuntimeError ("Vector contains a non-numeric or improperly formatted value: '" ^ s ^ "'. Please check input."))
                         ) elems in
                         let all_int = List.for_all (function IntVal _ -> true | _ -> false) parsed_elems in
                         if all_int then
                           let int_vec = List.map (function IntVal i -> i | _ -> failwith "impossible") parsed_elems in
                           let res = VectorVal_Int int_vec in
                           (Env.add var res env; res)
                         else
                           let float_vec = List.map (function
                               | IntVal i -> float_of_int i
                               | ScalarVal f -> f
                               | _ -> failwith "impossible"
                             ) parsed_elems in
                           let res = VectorVal_Float float_vec in
                           (Env.add var res env; res)
                 | [rows_str; cols_str] ->
                     (* Matrix input *)
                     let expected_rows = int_of_string rows_str in
                     let expected_cols = int_of_string cols_str in
                     let trimmed = String.trim content_line in
                     if not (String.length trimmed >= 4 &&
                             String.sub trimmed 0 2 = "[[" &&
                             String.sub trimmed (String.length trimmed - 2) 2 = "]]") then
                       raise (RuntimeError "Invalid input format. Matrices must be enclosed in [[ ]]. Ensure correct syntax.")
                     else
                       let inner = String.sub trimmed 2 (String.length trimmed - 4)
                                   |> String.trim in
                       let row_strs = Str.split (Str.regexp_string "],[") inner in
                       if List.length row_strs <> expected_rows then
                         raise (RuntimeError "Declared matrix row count does not match actual rows in input. Check dimension specification.")
                       else
                         let parsed_rows = List.map (fun row_str ->
                           let row = String.trim row_str in
                           let elems = String.split_on_char ',' row |> List.map String.trim in
                           if List.length elems <> expected_cols then
                             raise (RuntimeError "Declared matrix column count does not match actual columns in input. Verify dimensions and content.")
                           else
                             List.map (fun s ->
                               try IntVal (int_of_string s)
                               with Failure _ ->
                                 try ScalarVal (float_of_string s)
                                 with Failure _ -> raise (RuntimeError ("Matrix contains a non-numeric or improperly formatted value: '" ^ s ^ "'. Please check input."))
                             ) elems
                         ) row_strs in
                         let all_int =
                           List.for_all (fun row ->
                             List.for_all (function IntVal _ -> true | _ -> false) row
                           ) parsed_rows in
                         if all_int then
                           let int_matrix = List.map (fun row ->
                             List.map (function IntVal i -> i | _ -> failwith "impossible") row
                           ) parsed_rows in
                           let res = MatrixVal_Int int_matrix in
                           (Env.add var res env; res)
                         else
                           let float_matrix = List.map (fun row ->
                             List.map (function
                                 | IntVal i -> float_of_int i
                                 | ScalarVal f -> f
                                 | _ -> failwith "impossible"
                               ) row
                           ) parsed_rows in
                           let res = MatrixVal_Float float_matrix in
                           (Env.add var res env; res)
                 | _ ->
                     raise (RuntimeError "Invalid dimension specification. Expected format: 'size' for vectors or 'rows cols' for matrices."))
            | _ ->
                (* Fallback: If more than two lines, treat each as a scalar vector *)
                let parsed_vals = List.concat (List.map (fun line ->
                  let trimmed_line = String.trim line in
                  if trimmed_line = "" then [] else [trimmed_line]
                ) lines) in
                let values = List.map (fun s ->
                  try IntVal (int_of_string s)
                  with Failure _ ->
                    try ScalarVal (float_of_string s)
                    with Failure _ -> raise (RuntimeError ("File contains unsupported values: '" ^ s ^ "'. Expected integers or floats."))
                ) parsed_vals in
                let all_int = List.for_all (function IntVal _ -> true | _ -> false) values in
                if all_int then
                  let int_vals = List.map (function IntVal i -> i | _ -> failwith "impossible") values in
                  let res = VectorVal_Int int_vals in
                  (Env.add var res env; res)
                else
                  let float_vals = List.map (function
                    | IntVal i -> float_of_int i
                    | ScalarVal f -> f
                    | _ -> failwith "impossible"
                  ) values in
                  let res = VectorVal_Float float_vals in
                  (Env.add var res env; res)
          with Sys_error msg ->
            raise (RuntimeError ("Unable to open file: " ^ filename ^ ". Ensure the file exists and has correct permissions. Error: " ^ msg))
      
(* Statement evaluation: for statements of type Ast.statement *)
let rec eval_stmt (env : Env.t) (s : Ast.statement) : Env.t =
  match s with
  | IfElse (cond, s_then, s_else) ->
      (match eval_expr env cond with
       | BoolVal true -> 
           List.fold_left (fun env stmt -> eval_stmt env stmt) env s_then
       | BoolVal false -> 
           List.fold_left (fun env stmt -> eval_stmt env stmt) env s_else
       | _ -> 
           raise (RuntimeError "Error: If-Else condition must evaluate to a boolean (true/false). Ensure the condition expression is correct."))

  | For (x, e_start, e_stop, body) ->
      (match eval_expr env e_start, eval_expr env e_stop with
       | IntVal i_start, IntVal i_stop ->
           if i_start > i_stop then 
             raise (RuntimeError "Error: The start value of the for-loop must be less than or equal to the stop value. Ensure correct loop bounds.")
           else
             let local_env = Hashtbl.copy env in
             for i = i_start to i_stop do
               Env.add x (IntVal i) local_env;
               ignore (List.fold_left (fun env stmt -> eval_stmt env stmt) local_env body)
             done;
             (* Copy only the variable x back to the original environment *)
             (try
               let final_val = Env.find x local_env in
               Env.add x final_val env
             with Not_found -> ());
             env

       | ScalarVal f_start, ScalarVal f_stop ->
           let start_i = int_of_float f_start in
           let stop_i = int_of_float f_stop in
           if start_i > stop_i then 
             raise (RuntimeError "Error: The start value of the for-loop must be less than or equal to the stop value. Ensure correct loop bounds.")
           else
             let local_env = Hashtbl.copy env in
             for i = start_i to stop_i do
               Env.add x (ScalarVal (float_of_int i)) local_env;
               ignore (List.fold_left (fun env stmt -> eval_stmt env stmt) local_env body)
             done;
             (* Copy only the variable x back to the original environment *)
             (try
               let final_val = Env.find x local_env in
               Env.add x final_val env
             with Not_found -> ());
             env
       
       | _ -> 
           raise (RuntimeError "Error: Both bounds of a for-loop must be either integers or scalars (floating-point numbers). Ensure correct data types."))

  | While (cond, body) ->
      let rec loop () =
        match eval_expr env cond with
        | BoolVal true ->
            ignore (List.fold_left (fun env stmt -> eval_stmt env stmt) env body);
            loop ()
        | BoolVal false -> ()
        | _ -> 
            raise (RuntimeError "Error: While-loop condition must evaluate to a boolean (true/false). Check the condition expression.")
      in
      loop ();
      env

  | Block stmts ->
      List.fold_left (fun env s -> eval_stmt env s) env stmts

  | ExprStmt e ->
      ignore (eval_expr env e);
      env
      | Error ->
        Printf.printf "Error: An error occurred during evaluation.\n";
        raise (RuntimeError "Error encountered during evaluation")

  | Print x ->
      (try
        let v = Env.find x env in
        print_endline (
          match v with
          | IntVal i -> "Output: " ^ string_of_int i
          | ScalarVal f -> "Output: " ^ string_of_float f
          | BoolVal b -> "Output: " ^ string_of_bool b
          | VectorVal_Int v -> 
              "Output: [ " ^ String.concat ", " (List.map string_of_int v) ^ " ]"
          | MatrixVal_Int m -> 
              "Output:\n[\n" ^ String.concat "\n" (List.map (fun row -> 
                  "  [ " ^ String.concat ", " (List.map string_of_int row) ^ " ]") m) ^ "\n]"
          | VectorVal_Float v -> 
              "Output: [ " ^ String.concat ", " (List.map string_of_float v) ^ " ]"
          | MatrixVal_Float m -> 
              "Output:\n[\n" ^ String.concat "\n" (List.map (fun row -> 
                  "  [ " ^ String.concat ", " (List.map string_of_float row) ^ " ]") m) ^ "\n]"
        )
      with Not_found ->
        raise (RuntimeError ("Error: Attempting to print an undeclared variable '" ^ x ^ "'. Ensure the variable is defined before printing.")));
      env


(* Evaluate an entire program (list of statements) *)
let eval_program (stmts : Ast.program) : unit =
  let env = Env.create () in
  (* Apply eval_stmt for each statement in the program *)
  let _ = List.fold_left (fun env stmt -> eval_stmt env stmt) env stmts in
  (* No need to return anything, since it's a unit function *)
  ()


  