Designing a DSL for Matrix and Vector operations: part (b) Grammars


This is the second part of the open-ended design exercise for you to design a small programming language that manipulates vectors and matrices.   The test programs you will ultimately have to code in your own language will be, e.g., transposing a matrix,  inverting a matrix, finding determinants,  An ambitious one will be to write Gaussian elimination in your language.

In this part of the assignment, you have to specify the GRAMMATICAL ELEMENTS in your language -- using OCaml-Yacc, and implement a parser using OCaml-yacc (and OCaml-lex).

The grammar of the language should be Yacc-implementable with no reduce-reduce conflicts, and all shift-reduce conflicts resolved (you may use precedence levels for operators to do so)

In this part, you need to specify 

(1) Abstract Syntax for your language -- as an OCaml data type

(2) Output of Yacc should be the AST

(3) You should extend the type-checker of Assignment 2, so you only return well-typed ASTs -- i.e., well-typed wrt your Matrix-vector DSL (not OCaml).   That is, integrate the type checking routing into the OCaml-Yacc code.

(4) The TAs will specify example programs in pseudo-code or some other language.  You should render these in your DSL, and use OCaml-Yacc to build the corresponding ASTs.



As before the syntactic/lexical elements  of your DSL should include:

Input-Output commands to read in matrices, vectors, floats, integers, etc.   You need to support at least  Input(  <filename> ) and Input( )  as well as Print(<identifier>)
Variables -- whether boolean, integer, scalar, vector, or matrix  variables.    Typically your variables should at least be some variation of alphanumeric and may have primes and underscores.
Type names and constructions:  our types include booleans, integers, floats (scalars), vectors of dimension n, and m x n matrices.
Data: For each type we will have their constants and operations on them 
Boolean operations including constants, negation, conjunction, disjunction
Integer and Float operations including constants,  addition, multiplication, subtraction and division and abs. (all of these both for floats and integers;  for integers you also need equality and comparisons, and remainder]
Vectors — delimited using (rectangular) brackets [ and ] with commas as separators; the vector operations include constant vectors of any given dimension, addition of vectors, scalar multiplication, dot product, and angle, magnitude, dimension etc. 
Matrices:  m x n matrices modelled in row-major form (as a vector-of-vectors) with operations including constant matrices,  addition of matrices, scalar product with a matrix, matrix multiplication, transpose of a matrix, determinant of square matrices, etc.
Control Constructs  
Assignment  using := as the assignment symbol
Sequencing, with commands separated by semicolons, and sequence blocks delimited by {  and }  (as in C, C++, Java)
Conditionals: if_then_else
for loops with integer iterator variables and integer variables/constant as loop start/end limits. 
while loops with a boolean condition 
