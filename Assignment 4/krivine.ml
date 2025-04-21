(* Aditya Anand: 2023CS50284 *)
(* KRIVINE *)

type variable = string

type lamExp =
  | V of variable
  | Lam of variable * lamExp
  | App of lamExp * lamExp
  | Num of int
  | Bool of bool
  | Add of lamExp * lamExp
  | Sub of lamExp * lamExp
  | Mult of lamExp * lamExp
  | Div of lamExp * lamExp
  | Rem of lamExp * lamExp
  | Equal of lamExp * lamExp
  | Lessthan of lamExp * lamExp
  | Greaterthan of lamExp * lamExp
  | Lessthanequal of lamExp * lamExp
  | Greaterthanequal of lamExp * lamExp
  | And of lamExp * lamExp
  | Or of lamExp * lamExp
  | Abs of lamExp
  | Not of lamExp
  | IfThenElse of lamExp * lamExp * lamExp
  | Pair of lamExp list
  | First of lamExp
  | Second of lamExp

(* Environment and Closre idhar define kiya hai *)
type closure = Closure of lamExp * gamma
and gamma = variable -> closure



let empty_env : gamma = fun z -> match z with
  | variable -> failwith ("Got Unbound variable: " ^ variable)

let env_increase x v env = fun y -> match y with
    | y when y = x -> v
    | _ -> env y


    

(* Krivine Machine start *)
let rec krivine (express : lamExp) (env : gamma) : closure = match express with

  | V x -> env (x) 
  | App (exp_1, exp_2) -> (match krivine exp_1 env with
       | Closure (Lam (x, rest), up_env) ->
           let a2 = Closure (exp_2, env) in
           krivine rest (env_increase x a2 up_env) 
       | _ -> failwith "Application applied to non-function value")
  | Lam (x, rest) -> Closure (Lam (x, rest), env) 
  | Num n -> Closure (Num n, env)
  | Bool b -> Closure (Bool b, env)
  | Add (exp_1, exp_2) ->
      let a1 = check_num (krivine exp_1 env) in
      let a2 = check_num (krivine exp_2 env) in
      Closure (Num (a1 + a2), env)
  | Sub (exp_1, exp_2) ->
      let a1 = check_num (krivine exp_1 env) in
      let a2 = check_num (krivine exp_2 env) in
      Closure (Num (a1 - a2), env)
  | Mult (exp_1, exp_2) ->
      let a1 = check_num (krivine exp_1 env) in
      let a2 = check_num (krivine exp_2 env) in
      Closure (Num (a1 * a2), env)
  | Div (exp_1, exp_2) ->
      let a1 = check_num (krivine exp_1 env) in
      let a2 = check_num (krivine exp_2 env) in
      if a2 = 0 then failwith "Division by zero is happening"
      else Closure (Num (a1 / a2), env)
  | Equal (exp_1, exp_2) ->
      let result = compare_values (krivine exp_1 env) (krivine exp_2 env) in
      Closure (Bool result, env)
  | Lessthan (exp_1, exp_2) ->
      let a1 = check_num (krivine exp_1 env) in
      let a2 = check_num (krivine exp_2 env) in
      Closure (Bool (a1 < a2), env)
  | Greaterthan (exp_1, exp_2) ->
      let a1 = check_num (krivine exp_1 env) in
      let a2 = check_num (krivine exp_2 env) in
      Closure (Bool (a1 > a2), env)
  | Lessthanequal (exp_1, exp_2) ->
      let a1 = check_num (krivine exp_1 env) in
      let a2 = check_num (krivine exp_2 env) in
      Closure (Bool (a1 <= a2), env)
  | Greaterthanequal (exp_1, exp_2) ->
      let a1 = check_num (krivine exp_1 env) in
      let a2 = check_num (krivine exp_2 env) in
      Closure (Bool (a1 >= a2), env)
  | Rem (exp_1, exp_2) ->
      let a1 = check_num (krivine exp_1 env) in
      let a2 = check_num (krivine exp_2 env) in
      if a2 = 0 then failwith "Division by zero is happening"
      else Closure (Num (a1 mod a2), env)
  | Abs e ->
      let v = check_num (krivine e env) in
      Closure (Num (-v), env)
  | And (exp_1, exp_2) ->
      let a1 = check_bool (krivine exp_1 env) in
      let a2 = check_bool (krivine exp_2 env) in
      Closure (Bool (a1 && a2), env)
  | Or (exp_1, exp_2) ->
      let a1 = check_bool (krivine exp_1 env) in
      let a2 = check_bool (krivine exp_2 env) in
      Closure (Bool (a1 || a2), env)
  | Not e ->
      let v = check_bool (krivine e env) in
      Closure (Bool (not v), env)
  | IfThenElse (cond, t_then, t_else) ->
      let cond_val = check_bool (krivine cond env) in
      if cond_val then krivine t_then env
      else krivine t_else env
  | Pair tup -> Closure (Pair tup, env)
  | First e ->
        (match unload (krivine e env) with
         | Pair (head :: _) -> krivine head env
         | _ -> failwith "First applied to non-pair ya empty pair")
  | Second e ->
        (match unload (krivine e env) with
         | Pair (_ :: head :: _) -> krivine head env
         | _ -> failwith "Second applied to non-pair with less than two elements")
    

and check_num closure = match unload closure with
  | Num n -> n
  | _ -> failwith "This should have an integer value"

and check_bool closure = match unload closure with
  | Bool b -> b
  | _ -> failwith "This should have a boolean value"

and compare_values c1 c2 = match unload c1, unload c2 with
  | Num n1, Num n2 -> n1 = n2
  | Bool b1, Bool b2 -> b1 = b2
  | _ -> failwith "This should have same type values" 

and unload (c : closure) : lamExp = match c with
  | Closure (express, env) -> match express with
      | V x ->
          (try unload (env x)
           with _ -> V x)
      | App (exp_1, exp_2) ->
          App (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Lam (x, rest) ->
          Lam (x, unload (Closure (rest, env)))
      | Num n -> Num n
      | Bool b -> Bool b
      | Add (exp_1, exp_2) -> Add (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Sub (exp_1, exp_2) -> Sub (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Mult (exp_1, exp_2) -> Mult (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Div (exp_1, exp_2) -> Div (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Equal (exp_1, exp_2) -> Equal (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Lessthan (exp_1, exp_2) -> Lessthan (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Greaterthan (exp_1, exp_2) -> Greaterthan (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Lessthanequal (exp_1, exp_2) -> Lessthanequal (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Greaterthanequal (exp_1, exp_2) -> Greaterthanequal (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Rem (exp_1, exp_2) -> Rem (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Abs e -> Abs (unload (Closure (e, env)))
      | And (exp_1, exp_2) -> And (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Or (exp_1, exp_2) -> Or (unload (Closure (exp_1, env)), unload (Closure (exp_2, env)))
      | Not e -> Not (unload (Closure (e, env)))
      | IfThenElse (cond, t, e) -> IfThenElse (unload (Closure (cond, env)),unload (Closure (t, env)), unload (Closure (e, env)))
      | Pair tup -> Pair (List.map (fun e -> unload (Closure (e, env))) tup)
      | First e -> First (unload (Closure (e, env)))
      | Second e -> Second (unload (Closure (e, env)))

(* Function comvert lamda Exp to string *)
let rec express_string express = match express with
  | V x -> x
  | Lam (x, rest) -> "\\" ^ x ^ "." ^ express_string rest
  | App (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " " ^ express_string exp_2 ^ ")"
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Add (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " + " ^ express_string exp_2 ^ ")"
  | Sub (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " - " ^ express_string exp_2 ^ ")"
  | Mult (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " * " ^ express_string exp_2 ^ ")"
  | Div (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " / " ^ express_string exp_2 ^ ")"
  | Equal (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " == " ^ express_string exp_2 ^ ")"
  | Lessthan (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " < " ^ express_string exp_2 ^ ")"
  | Greaterthan (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " > " ^ express_string exp_2 ^ ")"
  | Lessthanequal (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " <= " ^ express_string exp_2 ^ ")"
  | Greaterthanequal (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " >= " ^ express_string exp_2 ^ ")"
  | Rem (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " % " ^ express_string exp_2 ^ ")"
  | Abs e -> "ABSOLUTE(" ^ express_string e ^ ")"
  | And (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " && " ^ express_string exp_2 ^ ")"
  | Or (exp_1, exp_2) -> "(" ^ express_string exp_1 ^ " || " ^ express_string exp_2 ^ ")"
  | Not e -> "NOT(" ^ express_string e ^ ")"
  | IfThenElse (cond, t, e) -> "IFELSE(" ^ express_string cond ^ ", " ^ express_string t ^ ", " ^ express_string e ^ ")"
  | Pair tup -> "PAIR(" ^ String.concat ", " (List.map express_string tup) ^ ")"
  | First e -> "FIRST(" ^ express_string e ^ ")"
  | Second e -> "SECOND(" ^ express_string e ^ ")"
  

(* Run Krivine machine with a given expression and environment *)
let krivine_run express start_env =
  let result_closure = krivine express start_env in
  unload result_closure

let create_env (bind : (variable * closure) list) : gamma =
  let rec env x = 
    try 
      let closs = List.assoc x bind in
      match closs with
      | Closure(e, old_env) -> Closure(e, old_env)
    with Not_found -> 
      failwith ("Got Unbound Variable : " ^ x)
  in env



(* ----------------------------------------------------------------------------------------------------------*)


(* ENVIRONMENT banaya hai idhar*)
let adi_env = create_env [("n", Closure(Num 10, empty_env));("choose", Closure(Lam("b", Lam("t", Lam("f", IfThenElse(V "b", V "t", V "f")))), empty_env))]


let new_env = create_env [("compose", Closure(Lam("f", Lam("g", Lam("x", App(V "f", App(V "g", V "x"))))),empty_env));("f", Closure(Lam("x", Add(V "x", Num 10)), empty_env));("g", Closure(Lam("x", Mult(V "x", Num 2)), empty_env))]

(* Additional helper environments for more complex tests *)
let adv_env = create_env [
  ("id", Closure(Lam("x", V "x"), empty_env));
  ("add5", Closure(Lam("x", Add(V "x", Num 5)), empty_env));
  ("mult3", Closure(Lam("x", Mult(V "x", Num 3)), empty_env));
  ("const", Closure(Lam("x", Lam("y", V "x")), empty_env));
  ("true_val", Closure(Lam("x", Lam("y", V "x")), empty_env));
  ("false_val", Closure(Lam("x", Lam("y", V "y")), empty_env))
]

let church_env = create_env [
  ("zero", Closure(Lam("f", Lam("x", V "x")), empty_env));
  ("one", Closure(Lam("f", Lam("x", App(V "f", V "x"))), empty_env));
  ("two", Closure(Lam("f", Lam("x", App(V "f", App(V "f", V "x")))), empty_env));
  ("three", Closure(Lam("f", Lam("x", App(V "f", App(V "f", App(V "f", V "x"))))), empty_env));
  ("succ", Closure(Lam("n", Lam("f", Lam("x", App(V "f", App(App(V "n", V "f"), V "x"))))), empty_env));
  ("add", Closure(Lam("m", Lam("n", Lam("f", Lam("x", App(App(V "m", V "f"), App(App(V "n", V "f"), V "x")))))), empty_env));
  ("mult", Closure(Lam("m", Lam("n", Lam("f", App(V "m", App(V "n", V "f"))))), empty_env))
]

let comb_env = create_env [
  ("S", Closure(Lam("x", Lam("y", Lam("z", App(App(V "x", V "z"), App(V "y", V "z"))))), empty_env));
  ("K", Closure(Lam("x", Lam("y", V "x")), empty_env));
  ("I", Closure(Lam("x", V "x"), empty_env))
]

let pair_env = create_env [
  ("make_pair", Closure(Lam("x", Lam("y", Lam("s", App(App(V "s", V "x"), V "y")))), empty_env));
  ("fst", Closure(Lam("p", App(V "p", Lam("x", Lam("y", V "x")))), empty_env));
  ("snd", Closure(Lam("p", App(V "p", Lam("x", Lam("y", V "y")))), empty_env))
]

let arith_env = create_env [
  ("double", Closure(Lam("x", Mult(V "x", Num 2)), empty_env));
  ("square", Closure(Lam("x", Mult(V "x", V "x")), empty_env));
  ("negate", Closure(Lam("x", Sub(Num 0, V "x")), empty_env));
  ("abs_val", Closure(Lam("x", IfThenElse(Lessthan(V "x", Num 0), Mult(V "x", Num (-1)), V "x")), empty_env));
  ("is_even", Closure(Lam("x", Equal(Rem(V "x", Num 2), Num 0)), empty_env));
  ("is_odd", Closure(Lam("x", Equal(Rem(V "x", Num 2), Num 1)), empty_env))
]


(*------------------------------------------------------------------------------------------------*)

(* TEST EXPRESSIONS start here *)

(* Test Cases *)
let test1 () =
  let expr = Add(Num 5, Num 3) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 1: Basic arithmetic: %s\n" (express_string result)

let test2 () =
  let expr = IfThenElse(Lessthan(Num 2, Num 3), Num 10, Num 20) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 2: Conditional evaluation: %s\n" (express_string result)

let test3 () =
  let expr = Mult(Num 4, Num 3) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 3: Multiplication: %s\n" (express_string result)

let test4 () =
  let expr = Div(Num 10, Num 2) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 4: Division: %s\n" (express_string result)

let test5 () =
  let expr = And(Bool true, Bool false) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 5: Boolean AND: %s\n" (express_string result)

let test6 () =
  let expr = Or(Bool true, Bool false) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 6: Boolean OR: %s\n" (express_string result)

let test7 () =
  let expr = Not(Bool true) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 7: Boolean NOT: %s\n" (express_string result)

let test8 () =
  let expr = Pair([Num 1; Num 3]) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 8: Tuple creation: %s\n" (express_string result)

let test9 () =
  let expr = First(Pair([Num 1; Num 2])) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 9: First of pair: %s\n" (express_string result)

let test10 () =
  let expr = Second(Pair([Num 1; Num 2])) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 10: Second of pair: %s\n" (express_string result)

let test11 () =
  let expr = App(Lam("x", V "x"), Num 42) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 11: Function application: %s\n" (express_string result)

let test12 () =
  let expr = Add(V "x", V "y") in
  let env = create_env [("x", Closure(Num 5, empty_env));("y", Closure(Num 7, empty_env))] in
  let result = krivine_run expr env in
  Printf.printf "Test 12: Variable lookup: %s\n" (express_string result)

let test13 () =
  let church_zero = Lam("f", Lam("x", V "x")) in
  let church_inc = Lam("n", Lam("f", Lam("x", App(V "f", App(App(V "n", V "f"), V "x"))))) in
  let expr = App(church_inc, church_zero) in
  let result = krivine_run expr adi_env in
  Printf.printf "Test 13: Church numerals: %s\n" (express_string result)

let test14 () =
  let expr = App(App(App(V "choose", Bool true), Num 100), Num 200) in
  let result = krivine_run expr adi_env in
  Printf.printf "Test 14: Complex choose: %s\n" (express_string result)

let test15 () =
  let expr = App(App(V "compose", V "f"), V "g") in
  let result = krivine_run expr new_env in
  Printf.printf "Test 15: Function composition: %s\n" (express_string result)

let test16 () =
    let char_all = App(Lam("x", Bool true), Num 100) in
    let result = krivine_run char_all empty_env in
    Printf.printf "Test 16: Characteristic function: %s\n" (express_string result)
  
(* Lambda calculus in action *)
let test17 () =
  let expr = App(App(App(V "S", V "K"), V "K"), Num 5) in
  let result = krivine_run expr comb_env in
  Printf.printf "Test 17: SKK combinator applied to 5: %s\n" (express_string result)

let test18 () =
  let expr = App(App(V "S", App(V "K", App(V "S", V "I"))), V "K") in
  let result = krivine_run expr comb_env in
  Printf.printf "Test 18: Complex combinator expression: %s\n" (express_string result)

let test19 () =
  let expr = App(App(V "add", V "two"), V "three") in
  let result = krivine_run expr church_env in
  Printf.printf "Test 19: Church numeral addition (2+3): %s\n" (express_string result)

let test20 () =
  let expr = App(App(V "mult", V "two"), V "three") in
  let result = krivine_run expr church_env in
  Printf.printf "Test 20: Church numeral multiplication (2*3): %s\n" (express_string result)

let test21 () =
  let expr = App(V "succ", V "three") in
  let result = krivine_run expr church_env in
  Printf.printf "Test 21: Church numeral successor (3+1): %s\n" (express_string result)

let test22 () =
  let pair = App(App(V "make_pair", Num 10), Num 20) in
  let expr = App(V "fst", pair) in
  let result = krivine_run expr pair_env in
  Printf.printf "Test 22: Church encoding of pairs (fst): %s\n" (express_string result)

let test23 () =
  let pair = App(App(V "make_pair", Num 10), Num 20) in
  let expr = App(V "snd", pair) in
  let result = krivine_run expr pair_env in
  Printf.printf "Test 23: Church encoding of pairs (snd): %s\n" (express_string result)

let test24 () =
  let factorial = 
    Lam("fact",
        Lam("n",
            IfThenElse(
              Equal(V "n", Num 0),
              Num 1,
              Mult(V "n", App(App(V "fact", V "fact"), Sub(V "n", Num 1)))
            )
        )
    ) in
  let expr = App(App(factorial, factorial), Num 5) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 24: Factorial of 5 using Y combinator: %s\n" (express_string result)

let test25 () =
  let expr = App(V "abs_val", Num (-10)) in
  let result = krivine_run expr arith_env in
  Printf.printf "Test 25: Absolute value of -10: %s\n" (express_string result)

let test26 () =
  let expr = App(V "is_even", Num 42) in
  let result = krivine_run expr arith_env in
  Printf.printf "Test 26: Check if 42 is even: %s\n" (express_string result)

let test27 () =
  let expr = App(V "is_odd", Num 42) in
  let result = krivine_run expr arith_env in
  Printf.printf "Test 27: Check if 42 is odd: %s\n" (express_string result)

let test28 () =
  let expr = App(App(Lam("x", Lam("y", Add(V "x", V "y"))), Num 5), Num 7) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 28: Curried addition function: %s\n" (express_string result)

let test29 () =
  let expr = App(Lam("f", App(V "f", App(V "f", Num 1))), V "add5") in
  let result = krivine_run expr adv_env in
  Printf.printf "Test 29: Applying a function twice: %s\n" (express_string result)

let test30 () =
  let expr = App(App(Lam("x", Lam("y", Or(V "x", V "y"))), Bool false), Bool true) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 30: Boolean OR operation with lambdas: %s\n" (express_string result)

let test31 () =
  let expr = App(Lam("x", IfThenElse(Equal(V "x", Num 0), Bool true, Bool false)), Num 0) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 31: Zero equality check with lambda: %s\n" (express_string result)

let test32 () =
  let expr = App(App(App(Lam("cond", Lam("then", Lam("else", App(App(V "cond", V "then"), V "else")))), Bool true), Num 1), Num 0) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 32: Church-encoded if-then-else: %s\n" (express_string result)

let test33 () =
  let y_comb = Lam("f", 
                App(Lam("x", App(V "f", App(V "x", V "x"))), 
                   Lam("x", App(V "f", App(V "x", V "x"))))) in
  let factorial_gen = Lam("f", Lam("n", 
                      IfThenElse(Equal(V "n", Num 0),
                                Num 1,
                                Mult(V "n", App(V "f", Sub(V "n", Num 1)))))) in
  let expr = App(App(y_comb, factorial_gen), Num 4) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 33: Y combinator for factorial of 4: %s\n" (express_string result)

let test34 () =
  let expr = App(
              Lam("n", 
                  IfThenElse(
                    Equal(V "n", Num 0),
                    Num 0,
                    IfThenElse(
                      Equal(V "n", Num 1),
                      Num 1,
                      Add(V "n", App(V "n", Sub(V "n", Num 1)))
                    )
                  )
              ),
              Num 5) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 34: Complex recursive expression: %s\n" (express_string result)

let test35 () =
  let expr = App(App(App(Lam("x", Lam("y", Lam("z", Add(Add(V "x", V "y"), V "z")))), Num 1), Num 2), Num 3) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 35: Triple addition with lambdas: %s\n" (express_string result)

let test36 () =
  let expr = App(Lam("f", App(V "f", App(V "f", App(V "f", Num 1)))), V "double") in
  let result = krivine_run expr arith_env in
  Printf.printf "Test 36: Applying double function thrice: %s\n" (express_string result)

let test37 () =
  let expr = App(Lam("x", Pair([V "x"; Add(V "x", Num 1); Mult(V "x", Num 2)])), Num 5) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 37: Creating a triple with lambda: %s\n" (express_string result)

let test38 () =
  let expr = App(
              Lam("x", 
                  IfThenElse(
                    Lessthan(V "x", Num 10),
                    Add(V "x", Num 10),
                    Sub(V "x", Num 10)
                  )
              ),
              Num 15) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 38: Conditional operation with lambda: %s\n" (express_string result)

let test39 () =
  let expr = App(
              Lam("x", App(Lam("y", Add(V "x", V "y")), Mult(V "x", Num 2))),
              Num 3) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 39: Nested lambda with arithmetic: %s\n" (express_string result)

let test40 () =
  let swap = Lam("p", Lam("f", App(App(V "p", Lam("x", Lam("y", App(App(V "f", V "y"), V "x")))), V "f"))) in
  let pair = App(App(V "make_pair", Num 1), Num 2) in
  let expr = App(App(swap, pair), V "make_pair") in
  let result = krivine_run expr pair_env in
  Printf.printf "Test 40: Swapping a pair's components: %s\n" (express_string result)

let test41 () =
  let expr = App(
              Lam("p", First(App(V "p", Lam("x", Lam("y", Pair([V "y"; V "x"])))))),
              App(App(V "make_pair", Num 10), Num 20)) in
  let result = krivine_run expr pair_env in
  Printf.printf "Test 41: Mix of Church pairs and built-in pairs: %s\n" (express_string result)

let test42 () =
  let is_zero = Lam("n", App(App(V "n", Lam("x", Bool false)), Bool true)) in
  let expr = App(is_zero, V "zero") in
  let result = krivine_run expr church_env in
  Printf.printf "Test 42: Church numeral zero test: %s\n" (express_string result)

let test43 () =
  let is_zero = Lam("n", App(App(V "n", Lam("x", Bool false)), Bool true)) in
  let expr = App(is_zero, V "one") in
  let result = krivine_run expr church_env in
  Printf.printf "Test 43: Church numeral non-zero test: %s\n" (express_string result)

let test44 () =
  let let_binding = App(Lam("x", App(Lam("y", Add(V "x", V "y")), Num 20)), Num 10) in
  let result = krivine_run let_binding empty_env in
  Printf.printf "Test 44: Let binding with arithmetic: %s\n" (express_string result)

let test45 () =
  let expr = App(
              Lam("x", 
                  IfThenElse(
                    Greaterthan(V "x", Num 0),
                    V "x",
                    Mult(V "x", Num (-1))
                  )
              ),
              Num (-5)) in
  let result = krivine_run expr empty_env in
  Printf.printf "Test 45: Absolute value implementation: %s\n" (express_string result)

let test46 () =
  let compose = Lam("f", Lam("g", Lam("x", App(V "f", App(V "g", V "x"))))) in
  let expr = App(
              App(
                App(compose, V "double"),
                V "square"
              ),
              Num 3) in
  let result = krivine_run expr arith_env in
  Printf.printf "Test 46: Function composition (double ∘ square): %s\n" (express_string result)

let () =
  print_endline "\n------------ Starting Krivine Machine Tests ------------";
  List.iter (fun f -> f()) [
    test1; test2; test3; test4; test5; 
    test6; test7; test8; test9; test10;
    test11; test12; test13; test14; test15; test16;
    test18; test19; test20; test21;  
    test25; test26; test27; test28;  test30;
    test31; test35;  test37;
    test38; test45; 
    test46; test17; test22; test23; test24; test29; test32; test36; 
    test39; test40; test41;test42; test43; test44;
  ];
  print_endline "\n------------ All Tests Completed ------------"
