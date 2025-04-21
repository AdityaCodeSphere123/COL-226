Vectors and Matrices


1. Read the OCaml List and Float modules and familiarise yourself with the OCaml type float for real numbers.  

(Note: The operations such as addition and multiplication are written with a dot after the operator -- e.g.,  +. and *.  -- to distinguish them from the similar operations on expressions of type  int.   In OCaml, an int is not automatically a float, but must explicitly be converted.)

2. Create a module for vectors using lists of floats as the representation form (type vector = float list), with the following operations:

create : int -> float  -> vector // (create n x) creates an n-dimensional vector containing value x, i.e. [x, ..., x]; raise  DimensionError if n < 1
dim:  vector -> int // gives the dimension of the vector (should be >= 1)
is_zero:  vector -> bool  //  checks that a given  vector v (of dim n) is the zero vector of dimension n
unit: int -> int -> vector // (unit n  j ) creates a unit vector of dim n, with a 1.0 in the j-th coordinate  (1 <= j <= n); raise DimensionError if (1 <= j <= n) is violated
scale: float -> vector -> vector // given float c and vector v, returns the vector  c v, whose coordinates are those of v multiplied by scalar c
addv : vector -> vector -> vector //  adds given vectors v1 and v2 (these should of the same dimension n. else raise the exception DimensionError) to return  v1 + v2
dot_prod: vector -> vector -> float // takes the dot product of two given vectors v1 and v2 (of the same dimension n, else raise the exception DimensionError)  to return  v1 . v2 
inv: vector -> vector //  given a vector  v, returns the vector that is its vector additive inverse. 
length: vector -> float // return the length of a given vector v
angle: vector -> vector -> float // given vectors v1 and v2 find the (smaller) angle between them in radians. 
Test your programs extensively, and submit your test data. 



Prove (not just check) the following mathematical properties hold for your module implementation:

For all vectors u, v, and w, and for all scalars b and c:

 (Commutativity)  u + v = v + u
 (Associativity) u + (v + w) = (u + v) + w
(Identity of addition)  v + O = v
(Identity scalar)  1.v = v
(Annihilator scalar)  0.v = O
(Additive Inverse)  v + (- v) = O
(Scalar product combination)  b.(c.v) = (b.c).v
(Scalar sum-product distribution)  (b + c).v = b.v + c.v
(Scalar Distribution over vector sums)  b.(u + v) = b.u + b.v
State at least three other properties (especially with respect to the length, dot product, angle etc.)