%{
open Ast

exception ParseError of string

let parse_error err = raise (ParseError err)

let parse_matrix_int rows column mat_str =
  let clear_string = String.sub mat_str 2 (String.length mat_str - 4) in 
  let row_strings = Str.split (Str.regexp_string "],[") clear_string in
  if List.length row_strings <> rows then 
    failwith "Row not equal";
  let parse_row row_str =
    let elements = String.split_on_char ',' row_str |> List.map int_of_string |> Array.of_list in
    if Array.length elements <> column then 
      failwith "Column not equal";
    elements
  in
  Array.of_list (List.map parse_row row_strings)

let parse_matrix_float rows column mat_str =
  let clear_string = String.sub mat_str 2 (String.length mat_str - 4) in 
  let row_strings = Str.split (Str.regexp_string "],[") clear_string in
  if List.length row_strings <> rows then 
    failwith "Row not equal";
  let parse_row row_str =
    let elements = String.split_on_char ',' row_str |> List.map float_of_string |> Array.of_list in
    if Array.length elements <> column then 
      failwith "Column not equal";
    elements
  in
  Array.of_list (List.map parse_row row_strings)


%}

%token BOOL_TRUE BOOL_FALSE
%token <int> INT
%token <float> FLOAT
%token <string> STRING 
%token <string> FILENAME
%token <string> VAR
%token <int * int * string> MATRIX_INT
%token <int * int * string> MATRIX_FLOAT
%token <int * int list> VECTOR_INT
%token <int * float list> VECTOR_FLOAT
%token TYPE_BOOL TYPE_INTEGER TYPE_SCALAR TYPE_VECTORINT TYPE_VECTORFLOAT TYPE_MATRIXINT TYPE_MATRIXFLOAT
%token PLUS_FLOAT MINUS_FLOAT TIMES_FLOAT DIVIDE_FLOAT
%token PLUS_INTEGER MINUS_INTEGER TIMES_INTEGER DIVIDE_INTEGER
%token ADD_VECTOR SCALAR_MULTIPLY ADD_MATRIX SCALAR_MATRIX_MULTIPLY MATRIX_MULTIPLY
%token ABS_FLOAT ABS_INTEGER
%token MODULUS POWER
%token INPUT 
%token <string> INPUT_FILE
%token <string> PRINT
%token IF THEN ELSE FOR TO DO WHILE END
%token INVERSE INVERSE_VECTOR INVERSE_MATRIX DETERMINANT TRANSPOSE
%token DIMENSION_VECTOR DIMENSION_MATRIX MAG ANGLE DOT_PRODUCT
%token ASSIGN EQUALTO NOTEQUAL LESS_EQ GREAT_EQ LESSTHAN GREATERTHAN
%token AND OR NOT
%token LEFT_PAREN RIGHT_PAREN LEFT_BRACKET RIGHT_BRACKET LEFT_BRACE RIGHT_BRACE
%token COMMA SEMICOLON
%token NULL
%token EOF

%nonassoc ELSE
%right ASSIGN
%left OR
%left AND
%left EQUALTO NOTEQUAL
%left LESSTHAN GREATERTHAN LESS_EQ GREAT_EQ
%left PLUS_FLOAT MINUS_FLOAT PLUS_INTEGER MINUS_INTEGER ADD_VECTOR ADD_MATRIX
%left TIMES_FLOAT DIVIDE_FLOAT 
%left TIMES_INTEGER DIVIDE_INTEGER 
%left SCALAR_MULTIPLY SCALAR_MATRIX_MULTIPLY 
%left MATRIX_MULTIPLY DOT_PRODUCT 
%left MODULUS
%right POWER
%right NOT
%right INVERSE TRANSPOSE
%left LEFT_PAREN
%left LEFT_BRACE
%left SEMICOLON

%start program
%type <Ast.program> program

%%

program:
  | lines EOF { $1 }
;

lines:
  | statement { [$1] }  
  | lines SEMICOLON statement { $1 @ [$3] }
  | lines SEMICOLON { $1 }  
;


statement:
  | input_print { $1 }
  | assignment { $1 }
  | if_stmt { $1 }
  | loops { $1 }
  | LEFT_BRACE lines RIGHT_BRACE { Block ($2) } 
  | express { ExprStmt $1 }
  | error SEMICOLON { Printf.eprintf "Syntax error\n"; Block [] }
;

loops: 
  | FOR LEFT_PAREN VAR ASSIGN express TO express RIGHT_PAREN DO LEFT_BRACE statement RIGHT_BRACE { For($3, $5, $7, $11) }
  | WHILE express DO LEFT_BRACE statement RIGHT_BRACE { While($2, $5) } 

input_print:
  | PRINT LEFT_PAREN VAR RIGHT_PAREN { PrintStmt ($3) } 
  | INPUT_FILE LEFT_PAREN FILENAME RIGHT_PAREN { InputStmt ($3) }
  | INPUT LEFT_PAREN RIGHT_PAREN { Input }
  | LEFT_BRACE statement RIGHT_BRACE { $2 }
;

if_stmt:
  | IF LEFT_PAREN express RIGHT_PAREN THEN LEFT_BRACE statement RIGHT_BRACE ELSE LEFT_BRACE statement RIGHT_BRACE { IfElse ($3, $7, $11) }

assignment:
  | VAR ASSIGN express { Assign($1, $3) }
  | TYPE_BOOL VAR ASSIGN express { Assign($2, $4) }
  | TYPE_INTEGER VAR ASSIGN express { Assign($2, $4) }
  | TYPE_SCALAR VAR ASSIGN express { Assign($2, $4) }
  | TYPE_VECTORFLOAT VAR ASSIGN express { Assign($2, $4) }
  | TYPE_MATRIXINT VAR ASSIGN express { Assign($2, $4) }
  | TYPE_VECTORINT VAR ASSIGN express { Assign($2, $4) }
  | TYPE_MATRIXFLOAT VAR ASSIGN express { Assign($2, $4) }
;

express:
  | types { $1 }
  | LEFT_PAREN express RIGHT_PAREN { $2 }
  | float_oper { $1 }
  | integer_oper { $1 }
  | vector_oper { $1 }
  | matrix_oper { $1 }
  | comparison { $1 }
  | bool_oper { $1 }  
  | INVERSE LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(Inverse, $3) }
  | DETERMINANT LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(Determinant, $3) }
  | MAG LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(Magnitude, $3) }
  | DIMENSION_VECTOR LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(DimensionVector, $3) }
  | DIMENSION_MATRIX LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(DimensionMatrix, $3) }
  | ANGLE LEFT_PAREN express COMMA express RIGHT_PAREN { Angle($3, $5) }
;

types:
  | NULL { NullExpr }
  | BOOL_TRUE { Bool_Ad(true) }
  | BOOL_FALSE { Bool_Ad(false) }
  | INT { Int_Ad($1) }
  | FLOAT { Float_Ad($1) }
  | VECTOR_INT { let (dim, vec) = $1 in VectorInt_Ad (dim, vec) }
  | VECTOR_FLOAT { let (dim, vec) = $1 in VectorFloat_Ad (dim, vec) }
  | MATRIX_INT { let (row, col, mat) = $1 in MatrixInt_Ad (row, col, parse_matrix_int row col mat) }
  | MATRIX_FLOAT { let (row, col, mat) = $1 in MatrixFloat_Ad (row, col, parse_matrix_float row col mat) }
  | VAR { Var_Ad($1) }
  | FILENAME { File_Ad($1) }


integer_oper:
  | express PLUS_INTEGER express { BinOp_Ad(PlusInt, $1, $3) }
  | express MINUS_INTEGER express { BinOp_Ad(MinusInt, $1, $3) }
  | express TIMES_INTEGER express { BinOp_Ad(TimesInt, $1, $3) }
  | express DIVIDE_INTEGER express { BinOp_Ad(DivideInt, $1, $3) }
  | express MODULUS express { BinOp_Ad(Modulus, $1, $3) }
  | express POWER express { BinOp_Ad(Power, $1, $3) }
  | ABS_INTEGER LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(AbsInt, $3) }

float_oper:
  | express PLUS_FLOAT express { BinOp_Ad(PlusFloat, $1, $3) }
  | express MINUS_FLOAT express { BinOp_Ad(MinusFloat, $1, $3) }
  | express TIMES_FLOAT express { BinOp_Ad(TimesFloat, $1, $3) }
  | express DIVIDE_FLOAT express { BinOp_Ad(DivideFloat, $1, $3) }
  | ABS_FLOAT LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(AbsFloat, $3) }

vector_oper:
  | express ADD_VECTOR express { BinOp_Ad(AddVector, $1, $3) }
  | express SCALAR_MULTIPLY express { BinOp_Ad(ScalarMultiply, $1, $3) }
  | DOT_PRODUCT LEFT_PAREN express COMMA express RIGHT_PAREN { BinOp_Ad(DotProduct, $3, $5) }
  | INVERSE_VECTOR LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(InverseVector, $3) }

matrix_oper:
  | express ADD_MATRIX express { BinOp_Ad(AddMatrix, $1, $3) }
  | express SCALAR_MATRIX_MULTIPLY express { BinOp_Ad(ScalarMatrixMultiply, $1, $3) }
  | express MATRIX_MULTIPLY express { BinOp_Ad(MatrixMultiply, $1, $3) }
  | TRANSPOSE LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(Transpose, $3) }
  | INVERSE_MATRIX LEFT_PAREN express RIGHT_PAREN { UnOp_Ad(InverseMatrix, $3) }

comparison:
  | express EQUALTO express { BinOp_Ad(Equal, $1, $3) }
  | express NOTEQUAL express { BinOp_Ad(NotEqual, $1, $3) }
  | express LESSTHAN express { BinOp_Ad(Less, $1, $3) }
  | express GREATERTHAN express { BinOp_Ad(Greater, $1, $3) }
  | express LESS_EQ express { BinOp_Ad(LessEqual, $1, $3) }
  | express GREAT_EQ express { BinOp_Ad(GreaterEqual, $1, $3) }

bool_oper:
  | express AND express { BinOp_Ad(And, $1, $3) }
  | express OR express { BinOp_Ad(Or, $1, $3) }
  | NOT express { UnOp_Ad(Not, $2) }

