Assignment 2: A Type Checker and Interpreter


In this assignment, we will develop the implementation for a Domain-Specific Language (DSL) that manipulates n-dimensional vectors over a scalar field.

Our (object language) DSL has expressions that fall into 3 sorts: boolean expressions, scalar expressions and vector expressions.  

For simplicity, we will use the  OCaml float type to represent the scalar field, and float list to represent vectors, relating this to the Abstract Data Type (ADT) you have implemented in Assignment 1.

We will propose an object-language type system with three sorts of types 

  Bool, Scalar , Vector(n)
 to make sure that expressions are correctly classified.  Vector(n) (for each n > 0) denotes the type of n-dimensional vectors (over the scalar field). 

In particular, we will allow some operations such as addition, multiplication, etc. to be “overloaded”, i.e., to have multiple type signatures. [After all, in mathematics, we use + for logical "or", for addition of reals (scalar addition c1 + c2) and for vector addition  v1 + v2.]

The OCaml data type definition for Typ is given as:

type types =  Bool    (* boolean *)
            | Scalar   (* a scalar — any float value *)
            | Vector of int   (* n-dimensional with elements of type float)
;;
The OCaml data type for the Abstract Syntax of our DSL is given as:

type expr =  
T | F   (* Boolean constants *)
| ConstS of float    (* Scalar constants *)
| ConstV of float list    (* Vector constants *)
| Add of expr * expr   (* overloaded — disjunction of two booleans or sum of  two scalars or sum of two vectors of the same dimension *)
| Inv of expr     (* overloaded — negation of a boolean or additive inverse of  a scalar or additive inverse of a vector *)
| ScalProd of expr * expr   (* overloaded — conjunction of two booleans or product of a scalar with another scalar or product of a scalar and a vector *)
| DotProd of expr * expr  (* dot product of two vectors of the same dimension *)
| Mag of expr   (* overloaded: absolute value of a scalar or magnitude of a vector *)
| Angle of expr * expr  (* in radians, the angle between two vectors *)
| IsZero of expr (* overloaded: checks if a boolean expression evaluates to F,  or if a given scalar is within epsilon of 0.0 or is the vector close — within epsilon on each coordinate —  to the zero vector *)
| Cond of expr * expr * expr  (* "if_then_else" --  if the first expr evaluates to T then evaluate the second expr, else the third expr *)
;;
You may also enrich your language by introducing other operations such as 

generating unit vectors 
generating the zero vector
projecting a vector onto a hyperplane defined by a subset of axes (dimensions)
subtracting scalars or subtracting vectors
transforming a vector (e.g., rotating it, etc.) 


The assignment

Specify and implement a Type-checker for this language
type_of:  expr -> types
which returns the type for any given expression, and raises an exception if there is a type error.  The type-checker should be able to disambiguate the different uses of overloaded operations.    
Let us define OCaml representations of values and errors as follows:
type values = B of myBool |  S of float | V of vector
exception Wrong of expr;;
Specify and implement a Definitional Interpreter 

eval: expr -> values
for the language.  You should use the ADT of Assignment 1 as much as possible. 