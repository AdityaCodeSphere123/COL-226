(* Aditya Anand : 2023CS50284*)

open Lexing
open Parser
open Ast
open Typechecker  

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
      Printf.sprintf "MatrixInt_Ad(%d, %d, [\n%s\n])" rows cols
        (String.concat ";\n" 
          (Array.to_list 
            (Array.map 
              (fun row -> 
                "[" ^ (String.concat ", " 
                  (Array.to_list (Array.map string_of_int row))) ^ "]"
              ) mat
            )
          )
        )    
  | MatrixFloat_Ad (rows, cols, mat) -> 
      Printf.sprintf "MatrixFloat_Ad(%d, %d, [\n%s\n])" rows cols
        (String.concat ";\n" 
          (Array.to_list 
            (Array.map 
              (fun row -> 
                "[" ^ (String.concat ", " 
                  (Array.to_list (Array.map string_of_float row))) ^ "]"
              ) mat
            )
          )
        )        
        | UnOp_Ad (op, e1) -> Printf.sprintf "UnOp_Ad(%s, %s)" (string_of_unop op) (print_expr e1)
        | BinOp_Ad (op,e1,e2) -> Printf.sprintf "BinOp_Ad(%s, %s, %s)" (print_expr e1) (string_of_binop op) (print_expr e2)
        | Angle (e1, e2) -> Printf.sprintf "Angle(%s, %s)" (print_expr e1) (print_expr e2)
        | File_Ad f -> Printf.sprintf "File_Ad(%s)" f

let rec print_stmt s =
  match s with
  | Assign (v, e) -> Printf.sprintf "Assign(%s, %s)" v (print_expr e)
  | IfElse (cond, thn, els) ->
    Printf.sprintf "IfElse(%s, %s, %s)" (print_expr cond) (print_stmt thn) (print_stmt els)
  | For (v, start, stop, body) -> Printf.sprintf "For(%s, %s, %s, %s)" v (print_expr start) (print_expr stop) (print_stmt body)
  | While (cond, body) -> Printf.sprintf "While(%s, %s)" (print_expr cond) (print_stmt body)
  | Block stmts -> Printf.sprintf "Block([\n  %s\n])" (String.concat ";\n  " (List.map print_stmt stmts))
  | PrintStmt v -> Printf.sprintf "PrintStmt(%s)" v
  | Input -> "Input(StdIn)"
  | InputStmt (file) -> Printf.sprintf "InputStmt(Some(%s))" file
  | ExprStmt e -> Printf.sprintf "ExprStmt(%s)" (print_expr e)

let print_program p =
  Printf.sprintf "Program([\n  %s\n])" (String.concat ";\n  " (List.map print_stmt p))

  let typecheck_program program =
    let env = Hashtbl.create 100 in
    List.iter (fun stmt ->
      match stmt with
      | Assign (v, express) -> 
          (try
            let expr_type = type_of env express in
            Hashtbl.replace env v expr_type;
            Printf.printf "Type of %s: %s\n" v (string_of_type expr_type)
          with TypeError msg -> 
            Printf.printf "Type Error in assignment to %s: %s\n" v msg)
      | ExprStmt express -> 
          (try
            let expr_type = type_of env express in
            Printf.printf "Expression Type: %s\n" (string_of_type expr_type)
          with TypeError msg -> 
            Printf.printf "Type Error in expression: %s\n" msg)
      | _ -> ()
    ) program
  

let testcases = 
"
## Arithmetic Operations
MatrixInt x := 2 2\n[[1,2],[3,4]];
a := 2e3;
x := 5 +i 3;
y := 10 -i 2;
z := 4 *i 2;
w := 8 /i 2;
mod_result := 9 % 2;
power_result := 2 ^ 3;

## Floating Point Arithmetic
a := 3.5 +f 2.1;
b := 6.2 -f 1.2;
c := 2.5 *f 4.0;
d := 10.0 /f 2.5;
e := 10.9 % 3;
f := 2.0 ^ 3.0;

## Boolean Expressions
b1 := true && false;
b2 := true || false;
b3 := !(false);
b4 := 5 == 5;

## Vector Operations
VectorInt v1 := 3\n[1,2,3] ;
VectorInt v2 := 3\n[4,5,6] ;
VectorInt v3 := 3\n[1.1,2.2,5.5];
VectorInt v4 := 4\n[1.1,2.2,5.5,6.6] +v 4\n[1.1,2.2,5.5,6.6];
VectorInt v5 := 3\n[1.1,2.2,5.5] *v 3.5;
VectorFloat v6 := 3\n[1.1,2.2,5.5] *v 2.1;
VectorInt v7 := 3\n[2.2,5.5,6.6] +v 4\n[1.1,2.2,5.5,6.6];
v8 := 4\n[1,2,5,6] +v 4\n[1.1,2.2,5.5,6.6];
v9 := 3\n[1.1,2.2,5.5] *v 3\n[1.1,2.2,5.5];

m1 := 2 2\n[[1,2],[3,4]] +m 2 2\n[[1,2],[3,4]];
m2:= 3 3\n[[1.,2.,3.],[4.,5.,6.],[7.,8.,9.]] +m 3 3\n[[1.,2.,3.],[4.,5.,6.],[7.,8.,9.]];
m3 := 2 2\n[[1,2],[3,4]] *m 3;

if (true) then {x := 5} else {x := 10} ;
while (x <= 10) do {x := x +i 1} ;
for (x := 1 to 10) do {y := x +i 1} ;

## Unary Operators
determ := det (2 2\n[[1,2],[3,4]]);
mag_n := mag (2\n[1.2,3.5]);
abs_n := absf (3.5);
abs_i := absi (-3);
dim_v := dim_vector (3\n[1,2,3]);
dim_m := dim_matrix (2 2\n[[1,2],[3,4]]);
inverse_v := inverse_vector (3\n[1,2,3]);
inverse_m := inverse_matrix (2 2\n[[1,2],[3,4]]);
inverse_2 := inverse_matrix (1 3\n[[1,2,3]]);
new := inverse_m;
new;
mag_n;
t := mag_n;

"

let clean_testcases = String.map (fun c -> if c = '\r' then ' ' else c) testcases

let () =
  print_endline "Starting Lexical Analysis...";
  let lexbuf = Lexing.from_string clean_testcases in

  let rec print_chars pos =
    if pos < String.length clean_testcases then (
      Printf.printf "Char[%d]: %C (ASCII: %d)\n" pos clean_testcases.[pos] (Char.code clean_testcases.[pos]);
      print_chars (pos + 1)
    )
  in
  print_chars 0;

  try
    
    let program = Parser.program Lexer.token lexbuf in

    
    print_endline (print_program program);

    
    print_endline "Starting Type Checking...";
    typecheck_program program;

  with
  | Lexer.LexingError msg -> Printf.eprintf "Lexing error: %s\n" msg
  | Parsing.Parse_error -> Printf.eprintf "Parsing error at position %d\n" (lexbuf.lex_curr_p.pos_cnum)
