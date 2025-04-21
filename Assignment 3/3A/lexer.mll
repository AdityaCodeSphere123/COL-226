(* ADITYA ANAND: 2023CS50284 *)

{
  open Lexing
  
  exception LexingError of string

  type token =
  | BOOL_TRUE
  | BOOL_FALSE
  | INT of int
  | FLOAT of float
  | STRING of string
  | FILENAME of string
  | MATRIX_INT of int * int * string
  | MATRIX_FLOAT of int * int * string
  | VECTOR_INT of int list
  | VECTOR_FLOAT of float list
  | TYPE_BOOL
  | TYPE_INTEGER
  | TYPE_SCALAR
  | TYPE_VECTOR
  | TYPE_MATRIX
  | PLUS_FLOAT
  | MINUS_FLOAT
  | TIMES_FLOAT
  | DIVIDE_FLOAT
  | PLUS_INTEGER
  | MINUS_INTEGER
  | TIME_INTEGER
  | DIVIDE_INTEGER
  | ADD_VECTOR
  | SCALAR_MULTIPLY
  | ADD_MATRIX
  | SCALAR_MATRIX_MULTIPLY
  | INVERSE_VECTOR
  | INVERSE_MATRIX
  | MATRIX_MULTIPLY
  | ABS_FLOAT
  | ABS_INTEGER
  | MODULUS
  | POWER
  | INPUT of string
  | PRINT of string
  | IF
  | THEN
  | ELSE
  | FOR
  | TO
  | DO
  | WHILE
  | END
  | INVERSE
  | DETERMINANT
  | TRANSPOSE
  | DIMENSION_VECTOR
  | DIMENSION_MATRIX
  | MAG
  | ANGLE
  | DOT_PRODUCT
  | ASSIGN
  | EQUALTO
  | NOTEQUAL
  | LESS_EQ
  | GREAT_EQ
  | LESSTHAN
  | GREATERTHAN
  | AND
  | OR
  | NOT
  | LEFT_PAREN
  | RIGHT_PAREN
  | LEFT_BRACKET
  | RIGHT_BRACKET
  | LEFT_BRACE
  | RIGHT_BRACE
  | COMMA
  | SEMICOLON
  | VAR of string
  | EOF
  
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
let float = sign?(digit+ '.' digit* (['e' 'E'] sign? digit+)? 
          | digit* '.' digit+ (['e' 'E'] sign? digit+)? 
          | digit+ ['e' 'E'] sign? digit+)    
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
  
  | "Input" "(" (filename as n ")")  { INPUT (n) }
  | "Input" "("  ")"                 { INPUT "" }
  | "Print" "(" (var as v) ")"       { PRINT (v) }
  | (digit+ as dim) '\n' '[' (integer (',' integer)* as v) ']'
  {
    let dimension = int_of_string dim in
    let vector_present = 
      v 
      |> String.split_on_char ',' 
      |> List.map (fun x -> int_of_string (String.trim x))
    in
    
    if List.length vector_present = dimension then
      VECTOR_INT vector_present
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
      VECTOR_FLOAT vector_present
    else
      raise (LexingError (Printf.sprintf 
        "Vector Dimension Mismatch. Expected %d, Got %d" 
        dimension 
        (List.length vector_present)))
  }

  | (digit+ as rows) spaces (digit+ as cols) newline 
  ('[' '[' [^']']* '.' [^']']* ']' ([','] '[' [^']']* '.' [^']']* ']')* ']') as mat
  {
    let row = int_of_string rows in
    let columns = int_of_string cols in
    
    MATRIX_FLOAT (row, columns, mat)
  }

  | (digit+ as rows) spaces (digit+ as cols) newline 
    ('[' '[' [^']']* ']' ([','] '[' [^']']* ']')* ']') as mat
  {
    let row = int_of_string rows in
    let columns = int_of_string cols in
    
    MATRIX_INT (row, columns, mat)
  }

  | "Bool"           { TYPE_BOOL }
  | "Int"            { TYPE_INTEGER }
  | "Scalar"         { TYPE_SCALAR }
  | "Vector"         { TYPE_VECTOR }
  | "Matrix"         { TYPE_MATRIX } 
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
  | "*i"             { TIME_INTEGER }
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
  | "inverse_vector" { INVERSE_VECTOR }
  | "inverse_matrix" { INVERSE_MATRIX }
  | "inverse"        { INVERSE }
  | "matrix_mult"    { MATRIX_MULTIPLY }            
  | "det"            { DETERMINANT }             
  | "transpose"      { TRANSPOSE }       
  | "mag"            { MAG }             
  | "angle"          { ANGLE }          
  | "dot"            { DOT_PRODUCT }         
  | "dim_vector"     { DIMENSION_VECTOR } 
  | "dim_matrix"     { DIMENSION_MATRIX }   
  | "absf"            { ABS_FLOAT }         
  | "absi"            { ABS_INTEGER }            
  | var as v         { VAR(v) }
  | filename as f    { FILENAME f } 
  | eof              { EOF }
  | _ as x { raise (LexingError ("Unexpected Character Present: " ^ (String.make 1 x))) }

and comment = parse
  | "*)"     { token lexbuf } 
  | eof      { raise (LexingError "Not Terminated Comment") }
  | _        { comment lexbuf }