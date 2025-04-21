6. Functional Language interpreters


In this assignment, you will have to implement two abstract machines for the toy functional languages based on the Call-by-Name and Call-by-Value lambda calculi.





First, implement the Krivine machine  for call-by-name  for  the pure lambda calculus (assume closed terms).



Let closures be depicted as <<e, gamma>> where 

e is a lambda expression

gamma is a table in variable -> closure

Let \x.e1 depict "lambda x. e1"

Let f[ x |-> v ] denote extending/modifying function f at the entry for x.



(Op) << (e1 e2), gamma>>, S   =>  <<e1, gamma>> ,  <<e1, gamma>>::S

(Var)  << x, gamma>>, S   =>  gamma(x),  S

(App)  << \x.e1, gamma>>, cl::S => <<e1, \gamma[x |-> cl] >>, S





Define closures appropriately
implement the execution of the machine it cannot make any further steps
Implement the "unload" function, that unravels the resulting closure into a lambda term. 
Again you need to provide enough input cases to show your program runs correctly.  
(Hint: You may use some of the examples that encode pairing and conditionals which will be in the notes.)


Third, implement the SECD machine

S - is a stack of values (evaluated expressions)

E, or gamma, is a table mapping variables to values 

C - is a list of opcodes (the remaining program to run)

D - is a stack of S-E-C triples, representing the return context for a function call. 

Let <<x, c, gamma>> denote a typical closure



opcodes:  LOOKUP(x) |  MkCLOS(x,c) | APP | RET

where x is a variable and c is a list of opcodes.



compile(x) = [ LOOKUP(x) ]

compile (e1 e2) = (compile e1) @  (compile e2) @ [APP]

compile (\x.e1) = [ MkCLOS(x, (compile e1)  @ [RET]) ]



(Var) s, gamma, LOOKUP(x)::c',  d    ==>   gamma(x)::s, gamma, c', d

(Clos) s, gamma, MkCLOS(x, c1)::c', d ==> <<x,c1, gamma>>::s, gamma, c', d

(App)  v2::(<<x, c1, gamma1>>)::s, gamma, APP::c', D  ==>

                      EmptyStack, gamma1[x |-> v2],  c1,  (s, gamma, c')::d

(Ret)  v::s', gamma', RET::c'', (s, gamma, c')::d  ==>  v::s, gamma, c', d



Define opcodes as a data type
Define value-closures and tables appropriately
Implement the compiler and execution of the machine
Again you need to provide enough input cases to show your program runs correctly.  (Hint: You may use some of the examples that encode pairing and conditionals which will be in the notes)
For your examples, show that the resulting closure you get is indeed a correct rendering of the lambda term you should have got as an answer.
Third, for extra credits, you should try to integrate a simple set of data types such as integers, booleans etc. to make this a more complete functional language.  You can also treat as syntactic sugar some of the the definitional constructs.

