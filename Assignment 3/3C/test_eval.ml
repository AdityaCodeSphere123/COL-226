(* Aditya Anand : 2023CS50284*)

open Lexing
open Parser
open Ast
open Typechecker (* Your typechecker module *)

let array_to_list_matrix arr =
  Array.to_list (Array.map Array.to_list arr)

(* Helper functions to print the AST (for debugging purposes) *)
(* Helper functions to print the AST (for debugging purposes) *)
let rec print_expr e =
  match e with
  | NullExpr -> "NullExpr" 
  | Bool_Ad b -> Printf.sprintf "Bool_Ad(%b)" b
  | Int_Ad i -> Printf.sprintf "Int_Ad(%d)" i
  | Float_Ad f -> Printf.sprintf "Float_Ad(%f)" f
  | Var_Ad v -> Printf.sprintf "Var_Ad(%s)" v
  | VectorInt_Ad (size, els) -> 
      Printf.sprintf "VectorInt_Ad(size: %d, [%s])" size (String.concat "; " (List.map string_of_int els))
  | VectorFloat_Ad (size, els) -> 
      Printf.sprintf "VectorFloat_Ad(size: %d, [%s])" size (String.concat "; " (List.map string_of_float els))
  | MatrixInt_Ad (rows, cols, mat) -> 
      let list_mat = array_to_list_matrix mat in
      Printf.sprintf "MatrixInt_Ad(%d, %d, [\n%s\n])" rows cols
        (String.concat ";\n" 
          (List.map 
            (fun row -> "[" ^ String.concat ", " (List.map string_of_int row) ^ "]") 
            list_mat
          )
        )    
  | MatrixFloat_Ad (rows, cols, mat) -> 
      let list_mat = array_to_list_matrix mat in
      Printf.sprintf "MatrixFloat_Ad(%d, %d, [\n%s\n])" rows cols
        (String.concat ";\n" 
          (List.map 
            (fun row -> "[" ^ String.concat ", " (List.map string_of_float row) ^ "]") 
            list_mat
          )
        )
  | IndexVec (v, idx) -> Printf.sprintf "IndexVec(%s, %s)" v (print_expr idx)
  | IndexMat (v, row, col) -> Printf.sprintf "IndexMat(%s, %s, %s)" v (print_expr row) (print_expr col)
  | AssignVec (v, idx, expr) -> Printf.sprintf "AssignVec(%s, %s, %s)" v (print_expr idx) (print_expr expr)
  | AssignMat (v, row, col, expr) -> Printf.sprintf "AssignMat(%s, %s, %s, %s)" v (print_expr row) (print_expr col) (print_expr expr)
  | UnOp_Ad (op, e1) -> Printf.sprintf "UnOp_Ad(%s, %s)" (string_of_unop op) (print_expr e1)
  | BinOp_Ad (op, e1, e2) -> Printf.sprintf "BinOp_Ad(%s, %s, %s)" (print_expr e1) (string_of_binop op) (print_expr e2)
  | Angle (e1, e2) -> Printf.sprintf "Angle(%s, %s)" (print_expr e1) (print_expr e2)
  | File_Ad f -> Printf.sprintf "File_Ad(%s)" f
  | Input var -> Printf.sprintf "%s := Input(stdin)" var
  | Input_File (var, f) -> Printf.sprintf "%s := Input_File(%s)" var f
  | Assign (v, expr) -> Printf.sprintf "Assign(%s, %s)" v (print_expr expr)
  | Create_bool var_name -> Printf.sprintf "Create_bool(%s)" var_name
  | Create_int var_name -> Printf.sprintf "Create_int(%s)" var_name
  | Create_float var_name -> Printf.sprintf "Create_float(%s)" var_name
  | Create_vecint (var_name, size) -> Printf.sprintf "Create_vecint(%s, %d)" var_name size
  | Create_vecfloat (var_name, size) -> Printf.sprintf "Create_vecfloat(%s, %d)" var_name size
  | Create_matint (var_name, rows, cols) -> Printf.sprintf "Create_matint(%s, %d, %d)" var_name rows cols
  | Create_matfloat (var_name, rows, cols) -> Printf.sprintf "Create_matfloat(%s, %d, %d)" var_name rows cols
  | Minor (matrix_expr, row, col) -> Printf.sprintf "Minor(%s, %d, %d)"(print_expr matrix_expr) row col

let rec print_stmt s =
    match s with
    | ExprStmt e -> Printf.sprintf "ExprStmt(%s)" (print_expr e)
    | Print var -> Printf.sprintf "Print(%s)" var
    | Error -> "Error Raised"
    | IfElse (cond, then_branch, else_branch) ->
      Printf.sprintf "If(%s, [%s], [%s])" 
        (print_expr cond)
        (String.concat "; " (List.map print_stmt then_branch))
        (String.concat "; " (List.map print_stmt else_branch))
    | While (cond, body) ->
        Printf.sprintf "While(%s, [%s])" 
          (print_expr cond) 
          (String.concat "; " (List.map print_stmt body))
    | For (v, start_expr, end_expr, body) ->
        Printf.sprintf "For(%s, %s, %s, [%s])" 
          v 
          (print_expr start_expr) 
          (print_expr end_expr) 
          (String.concat "; " (List.map print_stmt body))
    | Block stmts -> 
        Printf.sprintf "Block([\n    %s\n  ])" (String.concat ";\n    " (List.map print_stmt stmts))
    (* Add other statement types based on your AST definitions *)
let print_program p =
  Printf.sprintf "Program([\n  %s\n])" (String.concat ";\n  " (List.map print_stmt p))

let typecheck_program program =
  let env = Hashtbl.create 100 in
  List.iter (fun stmt ->
    match stmt with
    | ExprStmt express -> 
        (try
          let expr_type = type_of env express in
          Printf.printf "Expression Type: %s\n" (string_of_type expr_type)
        with TypeError msg -> 
          Printf.printf "Type Error in expression: %s\n" msg)
    | Print var ->
        (match Hashtbl.find_opt env var with
        | Some _ -> Printf.printf "Printing variable %s\n" var
        | None -> Printf.printf "Type Error: Variable '%s' is not defined.\n" var)
    | _ -> ()
  ) program

(* Function to read all input from the terminal until EOF *)
let rec read_all () =
  try
    let line = read_line () in
    line ^ "\n" ^ read_all ()
  with End_of_file -> ""

let () =
  Printf.printf "Enter your program input (finish with Ctrl-D on Unix/Mac or Ctrl-Z on Windows):\n";
  let test_input = read_all () in
  (* Remove carriage return characters if any *)
  let test_input = String.map (fun c -> if c = '\r' then ' ' else c) test_input in

  (* Lexing and Parsing *)
  let lexbuf = from_string test_input in
  let program = Parser.program Lexer.token lexbuf in

  (* For debugging, print the AST *)
  print_endline (print_program program);

  (* Typechecking *)  
  print_endline "Starting Type Checking...";
  typecheck_program program;
  print_endline "End Type Checking...";

  (* Evaluation *)
  print_endline "Starting Evaluation...";
  Eval.eval_program program;
  print_endline "End Evaluation...";

  (* Typechecking *)  
  print_endline "Starting Type Checking...";
  typecheck_program program;
  print_endline "End Type Checking...";
