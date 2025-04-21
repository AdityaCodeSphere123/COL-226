Assignment 3: Designing a small programming language -- part (a): Lexical Analysis


This is an open-ended design exercise for you to design a small programming language that manipulates vectors and matrices.   The test programs you will ultimately have to code in your own language will be, e.g., inverting a matrix.  An ambitious one will be to write Gaussian elimination in your language.

In this part of the assignment, you have to specify the LEXICAL ELEMENTS in your language -- using regular expressions, and implement a tokeniser using OCaml-lex.

The lexical elements of the language should at least cover the following which will be necessary to write any toy program in your own language:

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
White-space you support is your decision (space, tabs, newlines, etc.)
Your lexical specifications should also support your toy language program being decorated with comments. 


NOTE:  Since this assignment is open-ended, you can use your imagination and judgment in choosing the surface syntax, so that you programs in your language are readable and easily understandable.  Hence you should not try to copy well-worn but ugly solutions.

There will be also be enough scope in the following assignment to rectify any design choices you have made with which you are unhappy, or feel you can do better. 

BONUS ACTIVITY

Think of how you may want this to look if you had a 2-dimensional syntax (graphics)

Think of how you may want to design this language so that it may be usable for say a visually-disabled programmer. 