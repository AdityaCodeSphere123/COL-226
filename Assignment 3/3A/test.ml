(* Aditya Anand : 2023CS50284 *)

open Lexer
open Lexing

let string_of_token (t : token) : string = match x with
  | BOOL_TRUE -> "BOOL_TRUE"
  | BOOL_FALSE -> "BOOL_FALSE"
  | INT i -> Printf.sprintf "INT(%d)" i
  | FLOAT f -> Printf.sprintf "FLOAT(%f)" f
  | STRING s -> Printf.sprintf "STRING(\"%s\")" s
  | FILENAME s -> Printf.sprintf "FILENAME(%s)" s
  | MATRIX_INT (rows, cols, m) -> 
    Printf.sprintf "MATRIX_INT(%d, %d, %s)" rows cols m
  | MATRIX_FLOAT (rows, cols, m) -> 
    Printf.sprintf "MATRIX_FLOAT(%d, %d, %s)" rows cols m
  | VECTOR_INT v -> Printf.sprintf "VECTOR_INT(%s)" (String.concat ", " (List.map string_of_int v))
  | VECTOR_FLOAT v -> Printf.sprintf "VECTOR_FLOAT(%s)" (String.concat ", " (List.map string_of_float v))
  | TYPE_BOOL -> "TYPE_BOOL"
  | TYPE_INTEGER -> "TYPE_INTEGER"
  | TYPE_SCALAR -> "TYPE_SCALAR"
  | TYPE_VECTOR -> "TYPE_VECTOR"
  | TYPE_MATRIX -> "TYPE_MATRIX"
  | PLUS_FLOAT -> "PLUS_FLOAT"
  | MINUS_FLOAT -> "MINUS_FLOAT"
  | TIMES_FLOAT -> "TIMES_FLOAT"
  | DIVIDE_FLOAT -> "DIVIDE_FLOAT"
  | PLUS_INTEGER -> "PLUS_INTEGER"
  | MINUS_INTEGER -> "MINUS_INTEGER"
  | TIME_INTEGER -> "TIME_INTEGER"
  | DIVIDE_INTEGER -> "DIVIDE_INTEGER"
  | ADD_VECTOR -> "ADD_VECTOR"
  | SCALAR_MULTIPLY -> "SCALAR_MULTIPLY"
  | ADD_MATRIX -> "ADD_MATRIX"
  | SCALAR_MATRIX_MULTIPLY -> "SCALAR_MATRIX_MULTIPLY"
  | INVERSE_VECTOR -> "INVERSE_VECTOR"
  | INVERSE_MATRIX -> "INVERSE_MATRIX"
  | MATRIX_MULTIPLY -> "MATRIX_MULTIPLY"
  | ABS_FLOAT -> "ABS_FLOAT"
  | ABS_INTEGER -> "ABS_INTEGER"
  | MODULUS -> "MODULUS"
  | POWER -> "POWER"
  | INPUT f -> Printf.sprintf "INPUT(%s)" f
  | PRINT var -> Printf.sprintf "PRINT(%s)" var
  | IF -> "IF"
  | THEN -> "THEN"
  | ELSE -> "ELSE"
  | FOR -> "FOR"
  | TO -> "TO"
  | DO -> "DO"
  | WHILE -> "WHILE"
  | END -> "END"
  | INVERSE -> "INVERSE"
  | DETERMINANT -> "DETERMINANT"
  | TRANSPOSE -> "TRANSPOSE"
  | DIMENSION_VECTOR -> "DIMENSION_VECTOR"
  | DIMENSION_MATRIX -> "DIMENSION_MATRIX"
  | MAG -> "MAG"
  | ANGLE -> "ANGLE"
  | DOT_PRODUCT -> "DOT_PRODUCT"
  | ASSIGN -> "ASSIGN"
  | EQUALTO -> "EQUALTO"
  | NOTEQUAL -> "NOTEQUAL"
  | LESS_EQ -> "LESS_EQ"
  | GREAT_EQ -> "GREAT_EQ"
  | LESSTHAN -> "LESSTHAN"
  | GREATERTHAN -> "GREATERTHAN"
  | AND -> "AND"
  | OR -> "OR"
  | NOT -> "NOT"
  | LEFT_PAREN -> "LEFT_PAREN"
  | RIGHT_PAREN -> "RIGHT_PAREN"
  | LEFT_BRACKET -> "LEFT_BRACKET"
  | RIGHT_BRACKET -> "RIGHT_BRACKET"
  | LEFT_BRACE -> "LEFT_BRACE"
  | RIGHT_BRACE -> "RIGHT_BRACE"
  | COMMA -> "COMMA"
  | SEMICOLON -> "SEMICOLON"
  | VAR v -> Printf.sprintf "VAR(%s)" v
  | EOF -> "EOF"

let tokenize_and_print input =
  let lexbuf = Lexing.from_string input in
  let rec print_tokens () =
    match Lexer.token lexbuf with
    | EOF -> print_endline "EOF"
    | token ->
      print_endline (string_of_token token);
      print_tokens ()
  in
  Printf.printf "\nTesting: \"%s\"\n" input;
  print_tokens ()

  let test_boolean_numeric = [
    "true";  
    "false";  
    "42";  
    "-15";  
    "3.14";  
    "-0.001";  
    "5e3";  
    "-2.5e-2";  
    "3.5E+4";  
    "0";  
    "999999";  
    "3.14159";  
    "0.0001";  
    "1e6";  
    "2E-5";
    "2E-1+f5.0";
    "4.0-f5.0/f(3.6*f2.9)";
    "4*i5+i(7-i6/i(2+i4))";
    "3\n[1,2,3]+v3\n[4,5,6]";
    "2 2\n[[1.,2.6],[3.5,4.8]]+m 2 2\n[[5.3,6.5],[7.5,8.4]]";
    "3\n[1.,2.,3.6]*v3.5";
    "angle 3\n[1.,2.,3.6] 3\n[1.,2.,3.6]";
    "2 2\n[[1,2],[3,4]]*m7";
    "5%-3";
    "2^-3";
  ]

  let test_strings_identifiers = [
  "\"hello world\"";  
  "sample_file.txt";  
  "\"A string with spaces\"";  
  "\"123456\"";  
  "file_name.txt";  
  "file_name.log";  
  "data.json";  
  "abc";  
  "var_1";  
  "X";  
  "veryLongVariableName";  
  "num123";  
  "matrix_data";  
]

let test_keywords_control = [
  "if";  
  "then";  
  "else";  
  "for";  
  "to";  
  "do";  
  "while";  
  "end";  
  "while (a:=4)";  
  "if x == 5 then x:=6 else x:=7";  
  "while x < 10 do x:=x+i1";  
  "for x:=1 to 10 do y:=x+i1"; 
  "Bool x := true";
  "Int y := 5";
  "Scalar z := 3.14";
  "Vector v := 3\n[1,2,3]";
  "Matrix m := 2 2\n[[1,2],[3,4]]";
  "if x == true then y:=5 else y:=6";
  "while x == true do y:=y*i2";
  "for x:=2 to 10 do y:=y+f3.5";
]

let test_operators = [
  "==";  
  "!=";  
  "<=";  
  ">=";  
  "<";  
  ">";  
  "&&";  
  "||";  
  "!";  
  ":=";  
  "+f";  
  "-f";  
  "*f";  
  "/f";  
  "+i";  
  "-i";  
  "*i";  
  "/i";  
  "+v";  
  "*v";  
  "+m";  
  "*m";  
  "%";  
  "^";  
]

let test_brackets_delimiters = [
  "(";  
  ")";  
  "{";  
  "}";  
  "[";  
  "]";  
  ",";  
  ";";  
  "( ) { } [ ] , ;";  
]

let test_matrix_vector = [
  "inverse_vector";  
  "inverse_matrix";  
  "inverse";  
  "matrix_mult";  
  "det";  
  "transpose";  
  "mag";  
  "angle";  
  "dot";  
  "dim_vector";  
  "dim_matrix";  
  "Matrix X := [[1,2],[3,4]]";  
  "Matrix Y := 3 3\n[[1,2,3],[4,5,6],[7,8,9]]";  
  "Matrix Z := 2 3\n[[1,2],[3,4],[5,6]]";  
  "Vector V := [1,2,3]";  
  "Vector V := 3\n[1,2,3]";  
  "2\n[1,2]";  
  "3\n[5,7,9]";  
  "1 2\n[[3,5]]";  
  "2 2\n[[1,2],[3,4]]";  
]

let test_cases = [
  "3\n[1,3,5]";
  "3\n[1.,3.,5.0]";  
  "0\n[]"; 
  "0 0\n[[]]";  
  "2 2\n[[1.,2.],[3.,4.]]";  
  "1 2\n[[3,5,7]]";  
  "x := 2\n[3,5]";  
  "2\n[3,5]";  
  "1\n[3]";  
  "";   
  "   ";   
  "## This is a comment";  
  "(* Block comment start * This should be ignored *)";  
  "(* I am Aditya Anand *)";  
  "Int x := (* comment *) 5"; 
  "Input(file.txt)";          
  "Input(data.json)";        
  "Input(my_file.log)";       
  "Input(results.csv)";     
  "Input ( data.txt )";      
  "Input(file name.txt)";    
  "Input()";                 
  "Input(123)";              
  "Input(my_file)";          
  "Input(my file.txt)";       
  "Input(\"file.txt\")";     
  "Print(x)";            
  "Print(5)";            
  "Print(\"hello\")";    
  "Print(file.txt)";     
  "Print(var_1)";       
  "Print(num123)";       
  "Print()";             

]


let () =
  List.iter tokenize_and_print test_boolean_numeric
