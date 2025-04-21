(* Aditya Anand: 2023CS50284 *)
(* SECD *)

type variable = string

type lamexp =
  | V of variable
  | App of lamexp * lamexp
  | Lam of variable * lamexp
  | Num of int
  | Bool of bool
  | Add of lamexp * lamexp
  | Sub of lamexp * lamexp
  | Mult of lamexp * lamexp
  | Div of lamexp * lamexp
  | Rem of lamexp * lamexp
  | And of lamexp * lamexp
  | Or of lamexp * lamexp
  | Equal of lamexp * lamexp
  | Lessthan of lamexp * lamexp
  | Greaterthan of lamexp * lamexp
  | Lessthanequal of lamexp * lamexp
  | Greaterthanequal of lamexp * lamexp
  | Not of lamexp
  | Abs of lamexp
  | Pair of lamexp list
  | First of lamexp
  | Second of lamexp
  | IfThenElse of lamexp * lamexp * lamexp

(* Closure and Gammma Table *)
type closure = Closure of variable * opcode list * gamma
and gamma = (variable * value) list
and value =
  | ValueClosure of closure
  | Int of int
  | Bool of bool
  | PairVal of value list

(* SECD opcode *)
and opcode =
  | LOOKUP of variable
  | MkCLOS of variable * opcode list
  | APP
  | RET
  | INT_OP of int
  | BOOL_OP of bool
  | ADD 
  | SUB 
  | MUL 
  | DIV 
  | REM
  | AND 
  | OR 
  | EQUALTO 
  | LESSTHAN 
  | GREATERTHAN 
  | LESSTHANEQUAL 
  | GREATERTHANEQUAL 
  | NOT 
  | ABSOLUTE
  | PAIR of int
  | FIRST 
  | SECOND
  | IFELSE of opcode list * opcode list
  | TEST

let rec take n lst = if n <= 0 then []
  else match lst with
    | [] -> []
    | x :: xs -> x :: take (n-1) xs

let rec drop n lst = if n <= 0 then lst
  else match lst with
    | [] -> []
    | _ :: xs -> drop (n-1) xs

(* SECD machine *)
type machine_state = {stack: value list; env: gamma;control: opcode list; dump: (value list * gamma * opcode list) list}

(* Prrint *)
let rec opcodetostring = function
  | LOOKUP x -> "LOOKUP \"" ^ x ^ "\""
  | MkCLOS(x, c) -> "MkCLOS(\"" ^ x ^ "\", [" ^ String.concat "; " (List.map opcodetostring c) ^ "])"
  | APP -> "APP"
  | RET -> "RET"
  | INT_OP n -> "INT " ^ string_of_int n
  | BOOL_OP b -> "BOOL " ^ string_of_bool b
  | ADD -> "ADD"
  | SUB -> "SUBTRACT"
  | MUL -> "MULT"
  | DIV -> "DIVIDE"
  | REM -> "REM"
  | AND -> "AND"
  | OR -> "OR"
  | EQUALTO -> "EQUALTO"
  | LESSTHAN -> "LESSTHAN"
  | GREATERTHAN -> "GREATERTHAN"
  | LESSTHANEQUAL -> "LESSTHANEQUAL"
  | GREATERTHANEQUAL -> "GREATERTHANEQUAL"
  | NOT -> "NOT"
  | ABSOLUTE -> "ABSOLUTE"
  | PAIR n -> "PAIR " ^ string_of_int n
  | FIRST -> "FIRST"
  | SECOND -> "SECOND"
  | TEST -> "TEST"
  | IFELSE(t, express) -> "IFELSE([" ^ String.concat "; " (List.map opcodetostring t) ^ "], [" ^ 
                              String.concat "; " (List.map opcodetostring express) ^ "])"



let rec valutostr = function
  | ValueClosure(Closure(x, c, g)) -> "<<" ^ x ^ ", [" ^ String.concat "; " (List.map opcodetostring c) ^ "], " ^ gammastring g ^ ">>"
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | PairVal vs -> "PairVal([" ^ String.concat "; " (List.map valutostr vs) ^ "])"

and gammastring gamma =
  "[" ^ String.concat "; " (List.map (fun (x, v) -> "\"" ^ x ^ "\" -> " ^ valutostr v) gamma) ^ "]"

(* Compiler: LamExprssion -> Opcode *)
let rec compile (express: lamexp) : opcode list = match express with
  | V x -> [LOOKUP x]
  | App (e1, e2) -> compile e1 @ compile e2 @ [APP]
  | Lam (x, e1) -> [MkCLOS(x, compile e1 @ [RET])]
  | Num n -> [INT_OP n]
  | Bool b -> [BOOL_OP b]
  | Add (e1, e2) -> compile e1 @ compile e2 @ [ADD]
  | Sub (e1, e2) -> compile e1 @ compile e2 @ [SUB]
  | Mult (e1, e2) -> compile e1 @ compile e2 @ [MUL]
  | Div (e1, e2) -> compile e1 @ compile e2 @ [DIV]
  | Rem (e1, e2) -> compile e1 @ compile e2 @ [REM]
  | And (e1, e2) -> compile e1 @ compile e2 @ [AND]
  | Or (e1, e2) -> compile e1 @ compile e2 @ [OR]
  | Equal (e1, e2) -> compile e1 @ compile e2 @ [EQUALTO]
  | Lessthan (e1, e2) -> compile e1 @ compile e2 @ [LESSTHAN]
  | Greaterthan (e1, e2) -> compile e1 @ compile e2 @ [GREATERTHAN]
  | Lessthanequal (e1, e2) -> compile e1 @ compile e2 @ [LESSTHANEQUAL]
  | Greaterthanequal (e1, e2) -> compile e1 @ compile e2 @ [GREATERTHANEQUAL]
  | Not e1 -> compile e1 @ [NOT]
  | Abs e1 -> compile e1 @ [ABSOLUTE]
  | Pair es -> List.concat (List.map compile es) @ [PAIR (List.length es)]
  | First e1 -> compile e1 @ [FIRST]
  | Second e1 -> compile e1 @ [SECOND]
  | IfThenElse (cond, then_expr, else_expr) -> compile cond @ [TEST; IFELSE(compile then_expr, compile else_expr)]

let rec find_var (myvar: variable) (env: gamma) : value = match env with
  | [] -> failwith ("No variable found: " ^ myvar)
  | (gotvar, var_val) :: rest -> if myvar = gotvar then var_val else find_var myvar rest



let exe_instr (state: machine_state) : machine_state option = match state.control, state.stack, state.dump with
  | [], _, _ -> None   

  | (LOOKUP x) :: rem_code, stack, dump ->
    let v = find_var x state.env in
    Some { state with stack = v :: stack; control = rem_code }

  | (MkCLOS(x, c1)) :: rem_code, stack, dump ->
    let closure = Closure(x, c1, state.env) in
    Some { state with stack = ValueClosure closure :: stack; control = rem_code }

  | APP :: rem_code, v2 :: (ValueClosure (Closure(x, c1, env1))) :: rem_stack, dump ->
    Some {stack = []; env = (x, v2) :: env1; control = c1; dump = (rem_stack, state.env, rem_code) :: dump }

  | RET :: _, v :: _, (stack, env, rem_code) :: rem_dump ->
    Some {stack = v :: stack;env = env; control = rem_code; dump = rem_dump}


  | (INT_OP n) :: rem_code, stack, dump ->
    Some { state with stack = Int n :: stack; control = rem_code }

  | (BOOL_OP b) :: rem_code, stack, dump ->
    Some { state with stack = Bool b :: stack; control = rem_code }


  | ADD :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    Some { state with stack = Int (n1 + n2) :: rem_stack; control = rem_code }

  | SUB :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    Some { state with stack = Int (n1 - n2) :: rem_stack; control = rem_code }

  | MUL :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    Some { state with stack = Int (n1 * n2) :: rem_stack; control = rem_code }

  | DIV :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    if n2 = 0 then failwith "Division by zero is happening"
    else Some { state with stack = Int (n1 / n2) :: rem_stack; control = rem_code }


  | REM :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    if n2 = 0 then failwith "Division by zero is happening"
    else Some { state with stack = Int (n1 mod n2) :: rem_stack; control = rem_code }


  | AND :: rem_code, Bool b2 :: Bool b1 :: rem_stack, dump ->
    Some { state with stack = Bool (b1 && b2) :: rem_stack; control = rem_code }

  | OR :: rem_code, Bool b2 :: Bool b1 :: rem_stack, dump ->
    Some { state with stack = Bool (b1 || b2) :: rem_stack; control = rem_code }


  | EQUALTO :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    Some { state with stack = Bool (n1 = n2) :: rem_stack; control = rem_code }
  | EQUALTO :: rem_code, Bool b2 :: Bool b1 :: rem_stack, dump ->
    Some { state with stack = Bool (b1 = b2) :: rem_stack; control = rem_code }
  | LESSTHAN :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    Some { state with stack = Bool (n1 < n2) :: rem_stack; control = rem_code }
  | GREATERTHAN :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    Some { state with stack = Bool (n1 > n2) :: rem_stack; control = rem_code }
  | LESSTHANEQUAL :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    Some { state with stack = Bool (n1 <= n2) :: rem_stack; control = rem_code }
  | GREATERTHANEQUAL :: rem_code, Int n2 :: Int n1 :: rem_stack, dump ->
    Some { state with stack = Bool (n1 >= n2) :: rem_stack; control = rem_code }
  | NOT :: rem_code, Bool b :: rem_stack, dump ->
    Some { state with stack = Bool (not b) :: rem_stack; control = rem_code }

  | ABSOLUTE :: rem_code, Int n :: rem_stack, dump ->
    Some { state with stack = Int (abs n) :: rem_stack; control = rem_code }


  | (PAIR n) :: rem_code, stack, dump ->
    let tuple_vals = List.rev (take n stack) in
    let remaining_stack = drop n stack in
    Some { state with stack = PairVal tuple_vals :: remaining_stack; control = rem_code }

  | FIRST :: rem_code, (PairVal (v :: _)) :: rem_stack, dump ->
    Some { state with stack = v :: rem_stack; control = rem_code }
  | FIRST :: _, (PairVal []) :: _, _ ->
    failwith "Cannot get first element of an empty tuple"
  | FIRST :: _, _ :: _, _ ->
    failwith "Top of stack is not a tuple for 'first'"
  | SECOND :: rem_code, (PairVal (_ :: v :: _)) :: rem_stack, dump ->
    Some { state with stack = v :: rem_stack; control = rem_code }
  | SECOND :: _, (PairVal (_ :: [])) :: _, _ | SECOND :: _, (PairVal []) :: _, _ ->
    failwith "Pair does not have a second element"
  | SECOND :: _, _ :: _, _ ->
    failwith "Top of stack is not a tuple for 'second'"
  | TEST :: (IFELSE(then_code, else_code)) :: rem_code, (Bool b) :: rem_stack, dump ->
    let branch_exe = if b then then_code else else_code in
    Some {stack = rem_stack; env = state.env; control = branch_exe @ rem_code;dump = dump  }
  | _ -> failwith "Invalid SECD machine state"



let rec run (state: machine_state) : value =
  match exe_instr state with
  | None -> (match state.stack with
     | [v] -> v
     | _ -> failwith "Machine is stopped in invalid state")
  | Some state' -> run state'
let evaluate (express : lamexp) (initial_env: gamma) : value = let opcodes = compile express in
  let initial_state = {stack = []; env = initial_env; control = opcodes; dump = [] } in
  run initial_state


(* ----------------------- TESTCASES -----------------------------------------*)


let rec express_string = function
  | V x -> x
  | App(e1, e2) -> "App(" ^ express_string e1 ^ ", " ^ express_string e2 ^ ")"
  | Lam(x, express) -> "Lam(\"" ^ x ^ "\", " ^ express_string express ^ ")"
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Add(e1, e2) -> "(" ^ express_string e1 ^ " + " ^ express_string e2 ^ ")"
  | Sub(e1, e2) -> "(" ^ express_string e1 ^ " - " ^ express_string e2 ^ ")"
  | Mult(e1, e2) -> "(" ^ express_string e1 ^ " * " ^ express_string e2 ^ ")"
  | Div(e1, e2) -> "(" ^ express_string e1 ^ " / " ^ express_string e2 ^ ")"
  | Rem(e1, e2) -> "(" ^ express_string e1 ^ " % " ^ express_string e2 ^ ")"
  | And(e1, e2) -> "(" ^ express_string e1 ^ " && " ^ express_string e2 ^ ")"
  | Or(e1, e2) -> "(" ^ express_string e1 ^ " || " ^ express_string e2 ^ ")"
  | Equal(e1, e2) -> "(" ^ express_string e1 ^ " == " ^ express_string e2 ^ ")"
  | Lessthan(e1, e2) -> "(" ^ express_string e1 ^ " < " ^ express_string e2 ^ ")"
  | Greaterthan(e1, e2) -> "(" ^ express_string e1 ^ " > " ^ express_string e2 ^ ")"
  | Lessthanequal(e1, e2) -> "(" ^ express_string e1 ^ " <= " ^ express_string e2 ^ ")"
  | Greaterthanequal(e1, e2) -> "(" ^ express_string e1 ^ " >= " ^ express_string e2 ^ ")"
  | Not(e1) -> "NOT(" ^ express_string e1 ^ ")"
  | Abs(e1) -> "ABSOLUTE(" ^ express_string e1 ^ ")"
  | Pair(es) -> "PAIR([" ^ String.concat "; " (List.map express_string es) ^ "])"
  | First(e1) -> "FIRST(" ^ express_string e1 ^ ")"
  | Second(e1) -> "SECOND(" ^ express_string e1 ^ ")"
  | IfThenElse(cond, then_expr, else_expr) -> "IFELSE(" ^ express_string cond ^ ", " ^ express_string then_expr ^ ", " ^ express_string else_expr ^ ")"

let test_expr name expr initial_env =
  print_endline ("Test: " ^ name);
  print_endline ("Expression: " ^ express_string expr);
  print_endline ("Opcodes: [" ^ String.concat "; " (List.map opcodetostring (compile expr)) ^ "]");
  try
    let result = evaluate expr initial_env in
    print_endline ("Result: " ^ valutostr result);
  with Failure msg ->
    print_endline ("Error: " ^ msg);
  print_endline ""

(* Test cases start here se *)
let test1 () =
  let expr = Lam("x", V "x") in
  print_string "\nTest 1: ";
  test_expr "Identity function" expr []

let test2 () =
  let expr = App(Lam("x", V "x"), Num 42) in
  print_string "\nTest 2: ";
  test_expr "Application" expr []

let test3 () =
  let expr = Add(Num 5, Mult(Num 3, Num 2)) in
  print_string "\nTest 3: ";
  test_expr "Arithmetic" expr []

let test4 () =
  let expr = IfThenElse(Bool true, Num 1, Num 2) in
  print_string "\nTest 4: ";
  test_expr "Conditional" expr []

let test5 () =
  let expr = Lam("x", IfThenElse(
    Lessthan(V "x", Num 5),
    Add(V "x", Num 1),
    Mult(V "x", Num 2)
  )) in
  print_string "\nTest 5: ";
  test_expr "Complex lambda" expr [("x", ValueClosure(Closure("y", [RET],[])))]

let test6 () =
  let char_all = Lam("x", Bool true) in
  let expr = App(char_all, Num 100) in
  print_string "\nTest 6: ";
  test_expr "Characteristic function" expr []

(* Main test runner *)
let () =
  print_endline "\n--------------- Starting SECD Tests --------------";
  List.iter (fun f -> f()) [
    test1; test2; test3; test4; test5; test6
  ];
  print_endline "---------------- Tests Completed -------------------------"

let run_all_tests () =
  print_endline "-------------------SECD Machine Comprehensive Tests -------------------";
  
  (* Test 1: Basic Lambda Calculus *)
  let test1 () =
    (* Identity function applied to 42 *)
    let expr = App(Lam("x", V "x"), V "y") in
    test_expr "Test 1: Identity function applied to undefined integer" expr []
  in

  (* Test 2: Higher-order functions *)
  let test2 () =
    (* (λf.λx.f(f x)) (λy.y+1) 5 - Apply a function twice to an input *)
    let expr = App(
      App(
        Lam("f", Lam("x", App(V "f", App(V "f", V "x")))),
        Lam("y", Add(V "y", Num 1))
      ),
      Num 5
    ) in
    test_expr "Test 2: Higher-order function (double application)" expr []
  in

  (* Test 3: Non-empty environment with closures *)
  let test3 () =
    (* Using a function from environment: increment(10) *)
    let expr = App(V "increment", Num 10) in
    let env = [("increment", ValueClosure(Closure("x", [LOOKUP "x"; INT_OP 1; ADD; RET], [])))] in
    test_expr "Test 3: Apply function from environment" expr env
  in

  (* Test 4: Nested lambdas with environment *)
  let test4 () =
    (* ((λx.λy.x+y) 3) 4 *)
    let expr = App(App(Lam("x", Lam("y", Add(V "x", V "y"))), Num 3), Num 4) in
    test_expr "Test 4: Nested lambdas with currying" expr []
  in

  (* Test 5: Complex arithmetic in lambdas *)
  let test5 () =
    (* (λx.x*x + 2*x + 1) 5 - Evaluate a quadratic expression *)
    let expr = App(
      Lam("x", 
        Add(
          Add(
            Mult(V "x", V "x"),
            Mult(Num 2, V "x")
          ),
          Num 1
        )
      ),
      Num 5
    ) in
    test_expr "Test 5: Complex arithmetic in lambda (quadratic function)" expr []
  in

  (* Test 6: Conditional expressions with lambdas *)
  let test6 () =
    (* (λx. if x > 10 then x*2 else x+2) 15 *)
    let expr = App(
      Lam("x", 
        IfThenElse(
          Greaterthan(V "x", Num 10),
          Mult(V "x", Num 2),
          Add(V "x", Num 2)
        )
      ),
      Num 15
    ) in
    test_expr "Test 6: Conditional in lambda with true condition" expr []
  in

  (* Test 7: Another conditional with false case *)
  let test7 () =
    (* (λx. if x > 10 then x*2 else x+2) 5 *)
    let expr = App(
      Lam("x", 
        IfThenElse(
          Greaterthan(V "x", Num 10),
          Mult(V "x", Num 2),
          Add(V "x", Num 2)
        )
      ),
      Num 5
    ) in
    test_expr "Test 7: Conditional in lambda with false condition" expr []
  in

  (* Test 8: Lambda with boolean operations *)
  let test8 () =
    (* (λx.λy. (x && y) || (!x && !y)) true false - XOR implementation *)
    let expr = App(
      App(
        Lam("x", Lam("y", 
          Or(
            And(V "x", V "y"),
            And(Not(V "x"), Not(V "y"))
          )
        )),
        Bool true
      ),
      Bool false
    ) in
    test_expr "Test 8: Lambda with complex boolean operations (XNOR)" expr []
  in

  (* Test 9: Multiple argument lambda via currying *)
  let test9 () =
    (* (λa.λb.λc. a*b + b*c + a*c) 2 3 4 *)
    let expr = App(
      App(
        App(
          Lam("a", Lam("b", Lam("c",
            Add(
              Add(
                Mult(V "a", V "b"),
                Mult(V "b", V "c")
              ),
              Mult(V "a", V "c")
            )
          ))),
          Num 2
        ),
        Num 3
      ),
      Num 4
    ) in
    test_expr "Test 9: Triple curried application (3-variable function)" expr []
  in

  (* Test 10: Lambda creating pairs *)
  let test10 () =
    (* (λx. (x, x+1, x*x)) 7 *)
    let expr = App(
      Lam("x", Pair([V "x"; Add(V "x", Num 1); Mult(V "x", V "x")])),
      Num 7
    ) in
    test_expr "Test 10: Lambda creating tuple" expr []
  in

  (* Test 11: Accessing pair elements in lambda *)
  let test11 () =
    (* (λp. first(p) + second(p)) (5, 10) *)
    let expr = App(
      Lam("p", Add(First(V "p"), Second(V "p"))),
      Pair([Num 5; Num 10])
    ) in
    test_expr "Test 11: Lambda accessing tuple elements" expr []
  in

  (* Test 12: Lambda with absolute function *)
  let test12 () =
    (* (λx. |x - 5|) 2 *)
    let expr = App(
      Lam("x", Abs(Sub(V "x", Num 5))),
      Num 2
    ) in
    test_expr "Test 12: Lambda with absolute value function" expr []
  in

  (* Test 13: Complex environment with multiple variables *)
  let test13 () =
    (* Using x and y from environment in lambda: (λz. x + y + z) 3 *)
    let expr = App(
      Lam("z", Add(Add(V "x", V "y"), V "z")),
      Num 3
    ) in
    let env = [("x", Int 10); ("y", Int 20)] in
    test_expr "Test 13: Lambda using variables from environment" expr env
  in

  (* Test 14: Environment with function application *)
  let test14 () =
    (* Using increment function from environment *)
    let expr = App(
      Lam("x", Add(App(V "increment", V "x"), Num 5)),
      Num 10
    ) in
    let env = [("increment", ValueClosure(Closure("n", [LOOKUP "n"; INT_OP 1; ADD; RET], [])))] in
    test_expr "Test 14: Lambda using function from environment" expr env
  in

  (* Test 15: Lambda composition *)
  let test15 () =
    (* (λf.λg.λx. f(g(x))) (λa.a*a) (λb.b+1) 3 - Function composition *)
    let expr = App(
      App(
        App(
          Lam("f", Lam("g", Lam("x", App(V "f", App(V "g", V "x"))))),
          Lam("a", Mult(V "a", V "a"))
        ),
        Lam("b", Add(V "b", Num 1))
      ),
      Num 3
    ) in
    test_expr "Test 15: Lambda for function composition" expr []
  in

  (* Test 16: Factorial using lambda Y-combinator (recursion) *)
  let test16 () =
    (* A simplified factorial approximation (not true recursion): (λn. if n <= 1 then 1 else n * (n-1)) 5 *)
    let expr = App(
      Lam("n", 
        IfThenElse(
          Lessthanequal(V "n", Num 1),
          Num 1,
          Mult(V "n", Sub(V "n", Num 1))
        )
      ),
      Num 5
    ) in
    test_expr "Test 16: Simplified factorial approximation" expr []
  in

  (* Test 17: Complex nested conditionals *)
  let test17 () =
    (* (λx. if x < 0 then |x| else if x < 10 then x*x else x+10) (-5) *)
    let expr = App(
      Lam("x", 
        IfThenElse(
          Lessthan(V "x", Num 0),
          Abs(V "x"),
          IfThenElse(
            Lessthan(V "x", Num 10),
            Mult(V "x", V "x"),
            Add(V "x", Num 10)
          )
        )
      ),
      Num (-5)
    ) in
    test_expr "Test 17: Lambda with nested conditionals (negative case)" expr []
  in

  (* Test 18: Same as Test 17 but different input *)
  let test18 () =
    (* (λx. if x < 0 then |x| else if x < 10 then x*x else x+10) 5 *)
    let expr = App(
      Lam("x", 
        IfThenElse(
          Lessthan(V "x", Num 0),
          Abs(V "x"),
          IfThenElse(
            Lessthan(V "x", Num 10),
            Mult(V "x", V "x"),
            Add(V "x", Num 10)
          )
        )
      ),
      Num 5
    ) in
    test_expr "Test 18: Lambda with nested conditionals (middle case)" expr []
  in

  (* Test 19: Same as Test 17 but different input *)
  let test19 () =
    (* (λx. if x < 0 then |x| else if x < 10 then x*x else x+10) 15 *)
    let expr = App(
      Lam("x", 
        IfThenElse(
          Lessthan(V "x", Num 0),
          Abs(V "x"),
          IfThenElse(
            Lessthan(V "x", Num 10),
            Mult(V "x", V "x"),
            Add(V "x", Num 10)
          )
        )
      ),
      Num 15
    ) in
    test_expr "Test 19: Lambda with nested conditionals (last case)" expr []
  in

  (* Test 20: Lambda returning another lambda *)
  let test20 () =
    (* (λx. (λy. x + y)) 10 5 *)
    let expr = App(
      App(
        Lam("x", Lam("y", Add(V "x", V "y"))),
        Num 10
      ),
      Num 5
    ) in
    test_expr "Test 20: Lambda returning another lambda (closure test)" expr []
  in

  (* Test 21: Lambda with complex tuple operations *)
  let test21 () =
    (* (λx. (first(x), second(x), first(x) + second(x))) (3, 4) *)
    let expr = App(
      Lam("x", Pair([First(V "x"); Second(V "x"); Add(First(V "x"), Second(V "x"))])),
      Pair([Num 3; Num 4])
    ) in
    test_expr "Test 21: Lambda with tuple operations" expr []
  in

  (* Test 22: Lambda with environment and nested applications *)
  let test22 () =
    (* Using multiply and add from environment: (λx.λy. multiply(x, add(y, 2))) 4 5 *)
    let expr = App(
      App(
        Lam("x", Lam("y", App(App(V "multiply", V "x"), App(V "add", V "y")))),
        Num 4
      ),
      Num 5
    ) in
    let env = [
    ("add", ValueClosure(Closure("n", [LOOKUP "n"; INT_OP 2; ADD; RET], []))); 
    ("multiply", ValueClosure(Closure("m", [MkCLOS("n", [LOOKUP "m"; LOOKUP "n"; MUL;RET]);RET], [])))
  ] in
    test_expr "Test 22: Lambda with environment functions" expr env
  in

  (* Test 23: Complex boolean expression with lambda *)
  let test23 () =
    (* (λa.λb.λc. (a && !b) || (b && !c) || (a && c)) true false true *)
    let expr = App(
      App(
        App(
          Lam("a", Lam("b", Lam("c",
            Or(
              Or(
                And(V "a", Not(V "b")),
                And(V "b", Not(V "c"))
              ),
              And(V "a", V "c")
            )
          ))),
          Bool true
        ),
        Bool false
      ),
      Bool true
    ) in
    test_expr "Test 23: Lambda with complex boolean logic" expr []
  in

  (* Test 24: Lambda that manipulates pairs in environment *)
  let test24 () =
    (* With pair (3,4) in environment: (λp. (first(p)*2, second(p)*3)) myPair *)
    let expr = App(
      Lam("p", Pair([Mult(First(V "p"), Num 2); Mult(Second(V "p"), Num 3)])),
      V "myPair"
    ) in
    let env = [("myPair", PairVal [Int 3; Int 4])] in
    test_expr "Test 24: Lambda manipulating pair from environment" expr env
  in

  (* Test 25: Nested lambdas with complex environment *)
  let test25 () =
    (* Lambda accessing multiple environment variables *)
    let expr = App(
      Lam("z", App(
        App(V "mathOp", V "x"),
        Add(V "y", V "z")
      )),
      Num 4
    ) in
    let env = [
      ("x", Int 5);
      ("y", Int 7);
      ("mathOp", ValueClosure(Closure("a", [MkCLOS("b", [LOOKUP "a"; LOOKUP "b"; MUL; RET]);RET], [])))
    ] in
    test_expr "Test 25: Nested lambdas with complex environment" expr env
  in

  (* Test 26: Advanced arithmetic with lambdas *)
  let test26 () =
     (*(λx. (x % 3 == 0 && x % 5 == 0) ? "FizzBuzz" : (x % 3 == 0) ? "Fizz" : (x % 5 == 0) ? "Buzz" : x) 15 
       Simplified to use integers instead of strings *)
    let expr = App(
      Lam("x", 
        IfThenElse(
          And(Equal(Rem(V "x", Num 3), Num 0), Equal(Rem(V "x", Num 5), Num 0)),
          Num 15,  (* FizzBuzz = 15 *)
          IfThenElse(
            Equal(Rem(V "x", Num 3), Num 0),
            Num 3,  (* Fizz = 3 *)
            IfThenElse(
              Equal(Rem(V "x", Num 5), Num 0),
              Num 5,  (* Buzz = 5 *)
              V "x"
            )
          )
        )
      ),
      Num 15
    ) in
    test_expr "Test 26: FizzBuzz implementation with lambda (FizzBuzz case)" expr []
  in

  (* Test 27: Complex environment with multiple functions *)
  let test27 () =
    (* Use compose, increment, and square from environment *)
    let expr = App(
      App(V "compose", V "square"),
      App(V "increment", Num 4)
    ) in
    let env = [
      ("increment", ValueClosure(Closure("x", [LOOKUP "x"; INT_OP 1; ADD; RET], []))); 
      ("square", ValueClosure(Closure("x", [LOOKUP "x"; LOOKUP "x"; MUL; RET], []))); 
      ("compose", ValueClosure(Closure("f", [MkCLOS("x", [LOOKUP "x"; LOOKUP "f"; APP; RET])], [])))
    ] in
    test_expr "Test 27: Environment with function composition" expr env
  in

  (* Test 28: Lambda with division and remainder checks *)
  let test28 () =
    (* (λa.λb. if b != 0 then (a/b, a%b) else (-1,-1)) 17 5 *)
    let expr = App(
      App(
        Lam("a", Lam("b", 
          IfThenElse(
            Not(Equal(V "b", Num 0)),
            Pair([Div(V "a", V "b"); Rem(V "a", V "b")]),
            Pair([Num (-1); Num (-1)])
          )
        )),
        Num 17
      ),
      Num 5
    ) in
    test_expr "Test 28: Lambda with division and remainder operations" expr []
  in

  (* Test 29: Complex nested tuples with lambda *)
  let test29 () =
    (* (λx. (x, (x*x, x+1), ((x-1, x), (x+1, x+2)))) 3 *)
    let expr = App(
      Lam("x", 
        Pair([
          V "x"; 
          Pair([Mult(V "x", V "x"); Add(V "x", Num 1)]); 
          Pair([
            Pair([Sub(V "x", Num 1); V "x"]);
            Pair([Add(V "x", Num 1); Add(V "x", Num 2)])
          ])
        ])
      ),
      Num 3
    ) in
    test_expr "Test 29: Lambda creating complex nested tuples" expr []
  in

  (* Test 30: Ultimate complex test with environment, recursion approximation and conditionals *)
  let test30 () =
    (* A complex lambda expression combining many features
       (λn. if n <= 0 then baseValue else oper(n, (λm. if m <= 1 then 1 else m * (m-1)) (n-1))) 6 *)
    let expr = App(
      Lam("n", 
        IfThenElse(
          Lessthanequal(V "n", Num 0),
          V "baseValue",
          App(
            App(V "oper", V "n"),
            App(
              Lam("m", 
                IfThenElse(
                  Lessthanequal(V "m", Num 1),
                  Num 1,
                  Mult(V "m", Sub(V "m", Num 1))
                )
              ),
              Sub(V "n", Num 1)
            )
          )
        )
      ),
      Num 6
    ) in
    let env = [
      ("baseValue", Int 100);
      ("oper", ValueClosure(Closure("x", [MkCLOS("y", [LOOKUP "x"; LOOKUP "y"; ADD; RET]) ;RET], [])))
    ] in
    test_expr "Test 30: Ultimate complex lambda with environment and nested expressions" expr env
  in

  List.iter (fun f -> f()) [
    test1; test2; test3; test4; test5; test6; test7; test8; test9; test10;
    test11; test12; test13; test14; test15; test16; test17; test18; test19; test20;
    test21; test22; test23; test24; test25; test26; test27; test28; test29; test30
  ];
  print_endline "-------------------- Tests Completed --------------------"

let () = run_all_tests ()