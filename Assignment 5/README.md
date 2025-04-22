#Assignment 5: Terms, Substitution, Unification


You have to define a module for terms (perhaps parameterised on type definitions for variables and symbols), substitutions and unifiers.

Choose suitable type representations for types variable and symbol.

For example, variable = string,  and for example,  symbol = string*int.



You are expected to learn and use the OCaml module Array.

Consider the representation of "pre-terms" using the following data type definition

type term = V of variable | Node of symbol * (term array);;



Given a signature consisting of symbols with their arities (>= 0) in any suitable form -- either as a list of (symbol, arity) pairs, or as a function from strings to non-negative integer arities, write a function check_sig that checks whether the signature is a valid signature (no repeated symbols, arities are non-negative etc.)

Given a valid signature (checked using check_sig), define a function wfterm that checks that a given preterm is well-formed according to the signature, i.e., every node labelled by a symbol has exactly as many subterms as specified by the arity.

Define functions ht, size and vars that given a well-formed term, return its height, the number of nodes in it, and the set of variables appearing in it respectively.  Use the functions from the Array module:  map, foldl and other such functions as far as possible wherever you use lists.  

Define a suitable representation for substitutions. 

Define the function subst that given a term t and a substitution s, applies the (Unique Homomorphic Extension of) s to t. Ensure that subst is efficiently implemented. 

Come up with an efficient representation of composition of substitutions. 

Define the function mgu that given two terms t1 and t2, returns their most general unifier, if it exists and otherwise raises an exception NOT_UNIFIABLE.

Define an efficient edit function, that given a legal position in a tree, replaces the given subtree at that position by another specified tree.

Define also an in-place substitution operation that replaces variables by given terms in situ (modifying the terms by replacing the free variable occurrences in a term). 