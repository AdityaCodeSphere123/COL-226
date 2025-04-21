(* ADITYA ANAND: 2023CS50284 *)

{
  open Lexing
  open Parser  
  
  exception LexingError of string
  
  let parse_float f =
    try float_of_string f
    with Failure _ -> raise (LexingError ("Invalid Float: " ^ f))

  let parse_int x =
    try int_of_string x
    with Failure _ -> raise (LexingError ("Invalid Integer: " ^ x))

}

let sign = ['+' '-']
let digit = ['0'-'9']
let integer = sign?digit+
let float = sign?digit+ ('.' digit+)? (['e' 'E'] sign? digit+)?   
let vector_int_dim = digit+ 
let vector_int = vector_int_dim '\n' '[' (integer (',' integer)*)? ']'
let vector_float_dim = digit+
let vector_float = vector_float_dim '\n' '[' (float (',' float)*)? ']'
let letter = ['a'-'z' 'A'-'Z']
let var = letter ['a'-'z' 'A'-'Z' '0'-'9' '\'' '_']*
let filename = (letter | digit | '_' )+ ('.' (letter | digit | '_' )+)? 
let spaces = [' ' '\t']+
let newline = '\n' 
let string = '"' [^ '"']* '"'

rule token = parse
  | spaces                      { token lexbuf }                 
  | newline                     { token lexbuf }  
  | "##" [^'\n']* ('\n' | eof)  { () ; token lexbuf }                     
  | "(*"                        { comment lexbuf }              
  | "true"           { BOOL_TRUE }
  | "false"          { BOOL_FALSE }
  | integer as x     { INT (parse_int x) }
  | float as f       { FLOAT (parse_float f) }
  | string as s      { STRING (String.sub s 1 (String.length s - 2)) }
  | "Input"          { INPUT }  
  | "Print"          { PRINT }
  | (digit+ as dim) '\n' '[' (integer (',' integer)* as v) ']'
  {
    let dimension = int_of_string dim in
    let vector_present = 
      v 
      |> String.split_on_char ',' 
      |> List.map (fun x -> int_of_string (String.trim x))
    in
    
    if List.length vector_present = dimension then
      VECTOR_INT (int_of_string dim, vector_present)
    else
      raise (LexingError (Printf.sprintf 
        "Vector Dimension Mismatch. Expected %d, Got %d" 
        dimension 
        (List.length vector_present)))
  }
  | (digit+ as dim) '\n' '[' (float (',' float)* as v) ']'
  {
    let dimension = int_of_string dim in
    let vector_present = 
      v 
      |> String.split_on_char ',' 
      |> List.map (fun x -> float_of_string (String.trim x))
    in
    
    if List.length vector_present = dimension then
      VECTOR_FLOAT (int_of_string dim, vector_present)
    else
      raise (LexingError (Printf.sprintf 
        "Vector Dimension Mismatch. Expected %d, Got %d" 
        dimension 
        (List.length vector_present)))
  }

  | (digit+ as rows) spaces (digit+ as cols) newline 
  (('[' '[' [^']']* '.' [^']']* ']' ([','] '[' [^']']* '.' [^']']* ']')* ']') as mat)
  {
    MATRIX_FLOAT (int_of_string rows, int_of_string cols, String.trim mat)
  }

  | (digit+ as rows) spaces (digit+ as cols) newline 
  (('[' '[' [^']']* ']' ([','] '[' [^']']* ']')* ']') as mat)
  {
    MATRIX_INT (int_of_string rows, int_of_string cols, String.trim mat)
  }

  | "Bool"           { TYPE_BOOL }
  | "Int"            { TYPE_INTEGER }
  | "Scalar"         { TYPE_SCALAR }
  | "VectorInt"      { TYPE_VECTORINT }
  | "VectorFloat"    { TYPE_VECTORFLOAT }
  | "MatrixInt"      { TYPE_MATRIXINT }
  | "MatrixFloat"    { TYPE_MATRIXFLOAT } 
  | ","              { COMMA }
  | ";"              { SEMICOLON }
  | "("              { LEFT_PAREN }
  | ")"              { RIGHT_PAREN }
  | "*f"             { TIMES_FLOAT }
  | "/f"             { DIVIDE_FLOAT }
  | "+f"             { PLUS_FLOAT }
  | "-f"             { MINUS_FLOAT }
  | "+i"             { PLUS_INTEGER }
  | "-i"             { MINUS_INTEGER }
  | "*i"             { TIMES_INTEGER }
  | "/i"             { DIVIDE_INTEGER } 
  | "+v"             { ADD_VECTOR }
  | "*v"             { SCALAR_MULTIPLY }
  | "+m"             { ADD_MATRIX }
  | "*m"             { SCALAR_MATRIX_MULTIPLY }
  | "%"              { MODULUS }
  | "^"              { POWER }   
  | ":="             { ASSIGN }
  | "=="             { EQUALTO }
  | "!="             { NOTEQUAL }
  | "<="             { LESS_EQ }
  | ">="             { GREAT_EQ }
  | "<"              { LESSTHAN }
  | ">"              { GREATERTHAN }
  | "&&"             { AND }
  | "||"             { OR }
  | "!"              { NOT }           
  | "["              { LEFT_BRACKET }
  | "]"              { RIGHT_BRACKET }
  | "{"              { LEFT_BRACE }
  | "}"              { RIGHT_BRACE } 
  | "if"             { IF }
  | "then"           { THEN }
  | "else"           { ELSE }
  | "for"            { FOR }
  | "to"             { TO }
  | "do"             { DO }
  | "while"          { WHILE }
  | "end"            { END }
  | "null"           { NULL }
  | "inverse_vector" { INVERSE_VECTOR }
  | "inverse_matrix" { INVERSE_MATRIX }
  | "inverse"        { INVERSE }
  | "matrix_mult"    { MATRIX_MULTIPLY } 
  | "vec_mat_multiply"    { VECTOR_MULTIPLY }
  | "minor"          { MINOR } 
  | "det"            { DETERMINANT }             
  | "transpose"      { TRANSPOSE }       
  | "mag"            { MAG }             
  | "angle"          { ANGLE }          
  | "dot"            { DOT_PRODUCT }         
  | "dim_vector"     { DIMENSION_VECTOR } 
  | "dim_matrix"     { DIMENSION_MATRIX }   
  | "absf"           { ABS_FLOAT }         
  | "absi"           { ABS_INTEGER }
  | "square_root"    { SQUARE_ROOT } 
  | "raise Error"    { ERROR }
  | var as v         { VAR(v) }
  | filename as f    { FILENAME (f) } 
  | eof              { EOF }
  | _ as x { raise (LexingError ("Unexpected Character Present: " ^ (String.make 1 x))) }

and comment = parse
  | "*)"     { token lexbuf } 
  | eof      { raise (LexingError "Not Terminated Comment") }
  | _        { comment lexbuf }