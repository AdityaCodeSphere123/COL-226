(* Assignment 5: Terms, Substitution, Unification *)
open Printf
type variable = string
type symbol = string * int  

type signature = (symbol list)

type term = V of variable | Node of symbol * (term array)

(* Exception for unification failure *)
exception NOT_UNIFIABLE


let rec check_negative_arity (x : signature) : bool= match x with
  | [] -> false
  | (_, arity) :: xs -> 
      if arity < 0 then 
        true
      else check_negative_arity xs

(* 1. check_sig: no repeated symbols and non-negative arities *)
let check_sig (sign: signature) : bool = 
    (* Check all arities grester than equal 0 *)
    if (check_negative_arity sign) then
        false
    else
        let table_size = List.length sign in
        let sym_table = Hashtbl.create (table_size) in
        let rec check_unique = function
          | [] -> true
          | (var_name, _) :: remain ->
              if Hashtbl.mem sym_table var_name then
                false
              else (
                Hashtbl.add sym_table var_name true;
                check_unique remain
              )
        in
        check_unique sign
    
(* 2. Check if a term is well-formed according to a signature *)
let wfterm signatures term =
  (* Create a hashtable for quick symbol lookup *)
  let sig_table = Hashtbl.create (List.length signatures) in
  List.iter (fun ((sign, arity) as sym) -> 
    Hashtbl.add sig_table sign arity
  ) signatures;
  
  (* Recursive check function *)
  let rec check = function
    | V _ -> true
    | Node((sign, _), subterms) ->
        try
          let actual_arity = Array.length subterms in
          let expected_arity = 
            try Hashtbl.find sig_table sign
            with Not_found -> 
              raise (Invalid_argument ("Unknown symbol: " ^ sign))
          in
          if expected_arity <> actual_arity then
            false
          else
            Array.for_all check subterms
        with Invalid_argument _ -> false
  in
  check term

(* 3. Calculate the height of a term *)
let ht term =
  let rec height = function
    | V _ -> 0
    | Node(_, subterms) ->
        if Array.length subterms = 0 then 0
        else 1 + Array.fold_left (fun acc t -> max acc (height t)) 0 subterms
  in
  height term

(* Calculate the size (number of nodes) of a term *)
let size term =
  let rec count = function
    | V _ -> 1
    | Node(_, subterms) -> 
        1 + Array.fold_left (fun acc t -> acc + count t) 0 subterms
  in
  count term

(* Extract the set of variables in a term *)
let vars term =
  let var_set = Hashtbl.create 10 in
  let rec collect = function
    | V v -> Hashtbl.replace var_set v true
    | Node(_, subterms) -> Array.iter collect subterms
  in
  collect term;
  Hashtbl.fold (fun v _ acc -> v :: acc) var_set []

(* 4. Substitution representation as a list of variable-term pairs *)
type substitution = (variable * term) list

(* 5. Apply a substitution to a term *)
let subst term sigma =
  let subst_table = Hashtbl.create (List.length sigma) in
  List.iter (fun (v, t) -> Hashtbl.add subst_table v t) sigma;
  
  let rec apply t =
    match t with
    | V x -> 
        (try Hashtbl.find subst_table x 
         with Not_found -> t)
    | Node(s, args) -> 
        Node(s, Array.map apply args)
  in
  apply term

(* 6. Compose two substitutions s1 and s2 (s1 ∘ s2) *)
let compose s1 s2 =
  (* Apply s1 to the range of s2 *)
  let s2' = List.map (fun (v, t) -> (v, subst t s1)) s2 in
  
  (* Get domain of s2 *)
  let dom_s2 = List.map fst s2 in
  
  (* Filter s1 to include only bindings whose variables are not in dom_s2 *)
  let s1_filtered = List.filter (fun (v, _) -> 
    not (List.mem v dom_s2)
  ) s1 in
  
  (* Combine filtered s1 with modified s2 *)
  s1_filtered @ s2'

(* 7. Check if a variable occurs in a term (occurs check) *)
let rec occurs var term =
  match term with
  | V v -> v = var
  | Node(_, args) -> Array.exists (occurs var) args

(* Most general unifier implementation *)
let mgu t1 t2 =
  let rec unify eqs acc =
    match eqs with
    | [] -> acc
    | (s, t) :: rest when s = t -> unify rest acc  (* Identical terms unify trivially *)
    | (V x, t) :: rest ->
        if occurs x t then
          raise NOT_UNIFIABLE  (* Occurs check failure *)
        else
          let subst_x_t = [(x, t)] in
          let rest' = List.map (fun (s, t) -> (subst s subst_x_t, subst t subst_x_t)) rest in
          unify rest' ((x, t) :: acc)
    | (t, V x) :: rest -> 
        unify ((V x, t) :: rest) acc  (* Swap to handle previous case *)
    | (Node(s1, args1), Node(s2, args2)) :: rest ->
        if s1 <> s2 || Array.length args1 <> Array.length args2 then
          raise NOT_UNIFIABLE
        else
          let new_eqs = 
            List.init (Array.length args1) (fun i -> (args1.(i), args2.(i))) 
          in
          unify (new_eqs @ rest) acc
  in
  try
    let result = unify [(t1, t2)] [] in
    List.rev result  (* Return in appropriate order *)
  with NOT_UNIFIABLE -> raise NOT_UNIFIABLE

(* 8. Edit function to replace a subtree at a given position *)
let edit term position new_subtree =
  if position = [] then new_subtree  (* Replace the entire term *)
  else
    let rec replace t pos =
      match t, pos with
      | _, [] -> new_subtree  (* Replace at current position *)
      | Node(sym, args), idx :: rest_pos ->
          if idx < 0 || idx >= Array.length args then
            raise (Invalid_argument "Invalid position")
          else
            let new_args = Array.copy args in
            new_args.(idx) <- replace args.(idx) rest_pos;
            Node(sym, new_args)
      | V _, _ -> 
          raise (Invalid_argument "Cannot navigate into a variable")
    in
    replace term position

(* 9. In-place substitution that modifies the term directly *)
let subst_in_place term sigma =
  (* Create substitution table for quick lookup *)
  let subst_table = Hashtbl.create (List.length sigma) in
  List.iter (fun (v, t) -> Hashtbl.add subst_table v t) sigma;
  
  (* Recursive function to apply substitutions *)
  let rec apply t =
    match t with
    | V x as var_term ->
        (try Hashtbl.find subst_table x
         with Not_found -> var_term)
    | Node(sym, args) ->
        (* Modify array elements in place *)
        for i = 0 to Array.length args - 1 do
          args.(i) <- apply args.(i)
        done;
        t  (* Return the same term with modified contents *)
  in
  apply term

(* Example usage *)
let () =
  (* Example signature *)
  let example_sig = [
    ("f", 2);  (* binary function symbol *)
    ("g", 1);  (* unary function symbol *)
    ("h", 0);  (* constant symbol (arity 0) *)
  ] in
  
  (* Test signature validation *)
  let valid_sig = check_sig example_sig in
  Printf.printf "Is signature valid? %b\n" valid_sig;
  
  (* Example terms *)
  let term1 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    Node(("h", 0), [||])
  |]) in
  
  let term2 = Node(("f", 2), [|
    V "y";
    Node(("g", 1), [|V "x"|])
  |]) in
  
  (* Test well-formedness *)
  let wf1 = wfterm example_sig term1 in
  let wf2 = wfterm example_sig term2 in
  Printf.printf "Is term1 well-formed? %b\n" wf1;
  Printf.printf "Is term2 well-formed? %b\n" wf2;
  
  (* Test term properties *)
  Printf.printf "Height of term1: %d\n" (ht term1);
  Printf.printf "Size of term1: %d\n" (size term1);
  Printf.printf "Variables in term1: %s\n" (String.concat ", " (vars term1));
  
  (* Test substitution *)
  let sigma = [("x", V "z"); ("y", Node(("h", 0), [||]))] in
  let term1_subst = subst term1 sigma in
  
  (* Test unification *)
  try
    let unifier = mgu term1 term2 in
    Printf.printf "Terms are unifiable!\n";
    List.iter (fun (v, t) ->
      Printf.printf "%s -> " v;
      match t with
      | V var -> Printf.printf "V %s\n" var
      | Node((s, _), _) -> Printf.printf "Node %s\n" s
    ) unifier
  with NOT_UNIFIABLE ->
    Printf.printf "Terms are not unifiable!\n"


(* Test cases for the Term Module *)

(* Test 1: check_sig - Valid signature *)
let test1 = 
  let sig1 = [("f", 2); ("g", 1); ("h", 0)] in
  printf "Test1: check_sig with valid signature: %b\n" (check_sig sig1)

(* Test 2: check_sig - Negative arity *)
let test2 = 
  let sig2 = [("f", 2); ("g", -1); ("h", 0)] in
  printf "Test2: check_sig with negative arity: %b\n" (check_sig sig2)

(* Test 3: check_sig - Duplicate symbols *)
let test3 = 
  let sig3 = [("f", 2); ("g", 1); ("f", 3)] in
  printf "Test3: check_sig with duplicate symbols: %b\n" (check_sig sig3)

(* Test 4: check_sig - Empty signature *)
let test4 = 
  printf "Test4: check_sig with empty signature: %b\n" (check_sig [])

(* Test 5: check_sig - Single symbol *)
let test5 = 
  printf "Test5: check_sig with single symbol: %b\n" (check_sig [("f", 1)])

(* Test 6: check_sig - Zero arity *)
let test6 = 
  let sig6 = [("a", 0); ("b", 0); ("c", 0)] in
  printf "Test6: check_sig with all zero arity: %b\n" (check_sig sig6)

(* Test 7: check_sig - Same arity different symbols *)
let test7 = 
  let sig7 = [("f", 2); ("g", 2); ("h", 2)] in
  printf "Test7: check_sig with same arity different symbols: %b\n" (check_sig sig7)

(* Test 8: check_sig - Large signature (100 symbols) *)
let test8 = 
  let sig8 = List.init 100 (fun i -> ("sym" ^ string_of_int i, i mod 5)) in
  printf "Test8: check_sig with large signature (100 symbols): %b\n" (check_sig sig8)

(* Test 9: check_sig - Large signature with one duplicate *)
let test9 = 
  let sig9 = List.init 100 (fun i -> 
    if i = 99 then ("sym0", 0) else ("sym" ^ string_of_int i, i mod 5)
  ) in
  printf "Test9: check_sig with large signature with one duplicate: %b\n" (check_sig sig9)

(* Test 10: check_sig - Large signature with one negative *)
let test10 = 
  let sig10 = List.init 100 (fun i -> 
    if i = 50 then ("sym50", -1) else ("sym" ^ string_of_int i, i mod 5)
  ) in
  printf "Test10: check_sig with large signature with one negative: %b\n" (check_sig sig10)

(* Test 11: check_sig - Signature with high arity *)
let test11 = 
  let sig11 = [("high", 100); ("normal", 2)] in
  printf "Test11: check_sig with high arity: %b\n" (check_sig sig11)

(* Test 12: check_sig - Symbols with special characters *)
let test12 = 
  let sig12 = [("f+", 1); ("g-", 2); ("h*", 3)] in
  printf "Test12: check_sig with special characters: %b\n" (check_sig sig12)

(* Test 13: check_sig - Large signatures with high arities *)
let test13 = 
  let sig13 = List.init 500 (fun i -> ("sym" ^ string_of_int i, 10 + (i mod 20))) in
  printf "Test13: check_sig with large signature and high arities: %b\n" (check_sig sig13)

(* Test 14: check_sig - Mixed case symbols *)
let test14 = 
  let sig14 = [("F", 1); ("f", 2); ("G", 1); ("g", 2)] in
  printf "Test14: check_sig with mixed case symbols: %b\n" (check_sig sig14)

(* Test 15: check_sig - Identical symbols with identical arities (should fail) *)
let test15 = 
  let sig15 = [("f", 2); ("g", 1); ("f", 2)] in
  printf "Test15: check_sig with identical symbols and arities: %b\n" (check_sig sig15)

(* Basic signature for remaining tests *)
let basic_sig = [("f", 2); ("g", 1); ("h", 0); ("i", 3)]

(* Test 16: wfterm - Simple valid term *)
let test16 = 
  let t16 = Node(("f", 2), [|V "x"; V "y"|]) in
  printf "Test16: wfterm with simple valid term: %b\n" (wfterm basic_sig t16)

(* Test 17: wfterm - Valid complex term *)
let test17 = 
  let t17 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]); 
    Node(("h", 0), [||])
  |]) in
  printf "Test17: wfterm with valid complex term: %b\n" (wfterm basic_sig t17)

(* Test 18: wfterm - Variable *)
let test18 = 
  let t18 = V "x" in
  printf "Test18: wfterm with variable: %b\n" (wfterm basic_sig t18)

(* Test 19: wfterm - Invalid arity *)
let test19 = 
  let t19 = Node(("f", 2), [|V "x"|]) in  (* f should have 2 args *)
  printf "Test19: wfterm with invalid arity: %b\n" (wfterm basic_sig t19)

(* Test 20: wfterm - Unknown symbol *)
let test20 = 
  let t20 = Node(("unknown", 1), [|V "x"|]) in
  printf "Test20: wfterm with unknown symbol: %b\n" (wfterm basic_sig t20)

(* Test 21: wfterm - Deep nesting *)
let test21 = 
  let t21 = Node(("f", 2), [|
    Node(("f", 2), [|
      Node(("f", 2), [|V "x"; V "y"|]);
      V "z"
    |]);
    Node(("g", 1), [|V "w"|])
  |]) in
  printf "Test21: wfterm with deep nesting: %b\n" (wfterm basic_sig t21)

(* Test 22: wfterm - Mixed valid and invalid subterms *)
let test22 = 
  let t22 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]); 
    Node(("g", 1), [|V "y"; V "z"|])  (* g should have 1 arg, not 2 *)
  |]) in
  printf "Test22: wfterm with mixed valid/invalid subterms: %b\n" (wfterm basic_sig t22)

(* Test 23: wfterm - Large term (balanced tree of depth 5) *)
let rec make_balanced_term depth =
  if depth = 0 then
    V ("x" ^ string_of_int depth)
  else
    Node(("f", 2), [|
      make_balanced_term (depth - 1);
      make_balanced_term (depth - 1)
    |])

let test23 = 
  let t23 = make_balanced_term 5 in
  printf "Test23: wfterm with large balanced term: %b\n" (wfterm basic_sig t23)

(* Test 24: wfterm - Large term (unbalanced, right-heavy) *)
let rec make_right_heavy depth =
  if depth = 0 then
    V ("x" ^ string_of_int depth)
  else
    Node(("f", 2), [|
      V ("x" ^ string_of_int depth);
      make_right_heavy (depth - 1)
    |])

let test24 = 
  let t24 = make_right_heavy 100 in
  printf "Test24: wfterm with large right-heavy term: %b\n" (wfterm basic_sig t24)

(* Test 25: wfterm - Large term (unbalanced, left-heavy) *)
let rec make_left_heavy depth =
  if depth = 0 then
    V ("x" ^ string_of_int depth)
  else
    Node(("f", 2), [|
      make_left_heavy (depth - 1);
      V ("x" ^ string_of_int depth)
    |])

let test25 = 
  let t25 = make_left_heavy 100 in
  printf "Test25: wfterm with large left-heavy term: %b\n" (wfterm basic_sig t25)

(* Test 26: wfterm - Term with high arity symbol *)
let test26 = 
  let high_arity_sig = basic_sig @ [("high", 10)] in
  let t26 = Node(("high", 10), Array.init 10 (fun i -> V ("x" ^ string_of_int i))) in
  printf "Test26: wfterm with high arity symbol: %b\n" (wfterm high_arity_sig t26)

(* Test 27: wfterm - Term with mixed valid symbols *)
let test27 = 
  let t27 = Node(("i", 3), [|
    Node(("f", 2), [|V "a"; V "b"|]);
    Node(("g", 1), [|V "c"|]);
    Node(("h", 0), [||])
  |]) in
  printf "Test27: wfterm with mixed valid symbols: %b\n" (wfterm basic_sig t27)

(* Test 28: wfterm - Complex invalid term (correct at top level, invalid deeper) *)
let test28 = 
  let t28 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"; V "y"|]);  (* g takes only 1 arg *)
    Node(("h", 0), [||])
  |]) in
  printf "Test28: wfterm with deep invalid structure: %b\n" (wfterm basic_sig t28)

(* Test 29: wfterm - Large term with one error deep inside *)
let rec make_mostly_valid_term depth error_at =
  if depth = 0 then
    V ("x" ^ string_of_int depth)
  else if depth = error_at then
    Node(("g", 1), [|V "a"; V "b"|])  (* Error: g takes 1 arg, giving 2 *)
  else
    Node(("f", 2), [|
      make_mostly_valid_term (depth - 1) error_at;
      make_mostly_valid_term (depth - 1) error_at
    |])

let test29 = 
  let t29 = make_mostly_valid_term 10 5 in
  printf "Test29: wfterm with large term and one deep error: %b\n" (wfterm basic_sig t29)

(* Test 30: wfterm - Empty term array for non-zero arity *)
let test30 = 
  let t30 = Node(("g", 1), [||]) in  (* g takes 1 arg, giving 0 *)
  printf "Test30: wfterm with empty term array for non-zero arity: %b\n" (wfterm basic_sig t30)

(* Test 31: ht - Variable *)
let test31 = 
  let t31 = V "x" in
  printf "Test31: ht of variable: %d\n" (ht t31)

(* Test 32: ht - Constant *)
let test32 = 
  let t32 = Node(("h", 0), [||]) in
  printf "Test32: ht of constant: %d\n" (ht t32)

(* Test 33: ht - Simple term *)
let test33 = 
  let t33 = Node(("f", 2), [|V "x"; V "y"|]) in
  printf "Test33: ht of simple term: %d\n" (ht t33)

(* Test 34: ht - Nested term *)
let test34 = 
  let t34 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    V "y"
  |]) in
  printf "Test34: ht of nested term: %d\n" (ht t34)

(* Test 35: ht - Deep nesting on one side *)
let test35 = 
  let t35 = Node(("f", 2), [|
    Node(("f", 2), [|
      Node(("f", 2), [|V "x"; V "y"|]);
      V "z"
    |]);
    V "w"
  |]) in
  printf "Test35: ht of deep nested term: %d\n" (ht t35)

(* Test 36: ht - Balanced term *)
let test36 = 
  let t36 = make_balanced_term 3 in
  printf "Test36: ht of balanced term: %d\n" (ht t36)

(* Test 37: ht - Very deep term *)
let test37 = 
  let t37 = make_right_heavy 100 in
  printf "Test37: ht of very deep term: %d\n" (ht t37)

(* Test 38: ht - Complex nested term *)
let test38 = 
  let t38 = Node(("i", 3), [|
    Node(("f", 2), [|
      Node(("g", 1), [|V "a"|]);
      Node(("h", 0), [||])
    |]);
    Node(("f", 2), [|V "b"; V "c"|]);
    Node(("g", 1), [|
      Node(("f", 2), [|V "d"; V "e"|])
    |])
  |]) in
  printf "Test38: ht of complex nested term: %d\n" (ht t38)

(* Test 39: ht - Wide term with same height branches *)
let test39 = 
  let t39 = Node(("i", 3), [|
    Node(("g", 1), [|V "a"|]);
    Node(("g", 1), [|V "b"|]);
    Node(("g", 1), [|V "c"|])
  |]) in
  printf "Test39: ht of wide term with same height branches: %d\n" (ht t39)

(* Test 40: ht - Term with varying depth branches *)
let test40 = 
  let t40 = Node(("i", 3), [|
    V "a";
    Node(("g", 1), [|V "b"|]);
    Node(("f", 2), [|
      Node(("g", 1), [|V "c"|]);
      V "d"
    |])
  |]) in
  printf "Test40: ht of term with varying depth branches: %d\n" (ht t40)

(* Test 41: ht - Large balanced binary tree *)
let test41 = 
  let t41 = make_balanced_term 10 in
  printf "Test41: ht of large balanced binary tree: %d\n" (ht t41)

(* Test 42: ht - Zero height term (constant) *)
let test42 = 
  let t42 = Node(("h", 0), [||]) in
  printf "Test42: ht of zero height term: %d\n" (ht t42)

(* Test 43: ht - Term with max height on non-first branch *)
let test43 = 
  let t43 = Node(("i", 3), [|
    V "a";
    make_balanced_term 5;
    V "b"
  |]) in
  printf "Test43: ht of term with max height on non-first branch: %d\n" (ht t43)

(* Test 44: ht - Large complex term *)
let test44 = 
  let make_complex n =
    let rec build depth idx =
      if depth = 0 then V ("x" ^ string_of_int idx)
      else if idx mod 3 = 0 then
        Node(("f", 2), [|build (depth-1) (2*idx); build (depth-1) (2*idx+1)|])
      else if idx mod 3 = 1 then
        Node(("g", 1), [|build (depth-1) (3*idx)|])
      else
        Node(("i", 3), [|
          build (depth-1) (3*idx); 
          build (depth-1) (3*idx+1); 
          build (depth-1) (3*idx+2)
        |])
    in
    build n 1
  in
  let t44 = make_complex 6 in
  printf "Test44: ht of large complex term: %d\n" (ht t44)

(* Test 45: ht - One-sided very deep term *)
let test45 = 
  let t45 = make_left_heavy 50 in
  printf "Test45: ht of one-sided very deep term: %d\n" (ht t45)

(* Test 46: size - Variable *)
let test46 = 
  let t46 = V "x" in
  printf "Test46: size of variable: %d\n" (size t46)

(* Test 47: size - Constant *)
let test47 = 
  let t47 = Node(("h", 0), [||]) in
  printf "Test47: size of constant: %d\n" (size t47)

(* Test 48: size - Simple term *)
let test48 = 
  let t48 = Node(("f", 2), [|V "x"; V "y"|]) in
  printf "Test48: size of simple term: %d\n" (size t48)

(* Test 49: size - Nested term *)
let test49 = 
  let t49 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    V "y"
  |]) in
  printf "Test49: size of nested term: %d\n" (size t49)

(* Test 50: size - Deep nesting *)
let test50 = 
  let t50 = Node(("f", 2), [|
    Node(("f", 2), [|
      Node(("f", 2), [|V "x"; V "y"|]);
      V "z"
    |]);
    V "w"
  |]) in
  printf "Test50: size of deep nested term: %d\n" (size t50)

(* Test 51: size - Balanced term *)
let test51 = 
  let t51 = make_balanced_term 3 in
  printf "Test51: size of balanced term: %d\n" (size t51)

(* Test 52: size - Large term *)
let test52 = 
  let t52 = make_balanced_term 10 in
  printf "Test52: size of large balanced term: %d\n" (size t52)

(* Test 53: size - Complex term *)
let test53 = 
  let t53 = Node(("i", 3), [|
    Node(("f", 2), [|
      Node(("g", 1), [|V "a"|]);
      Node(("h", 0), [||])
    |]);
    Node(("f", 2), [|V "b"; V "c"|]);
    Node(("g", 1), [|
      Node(("f", 2), [|V "d"; V "e"|])
    |])
  |]) in
  printf "Test53: size of complex term: %d\n" (size t53)

(* Test 54: size - Very deep linear term *)
let test54 = 
  let t54 = make_right_heavy 30 in
  printf "Test54: size of very deep linear term: %d\n" (size t54)

(* Test 55: size - Term with high-arity node *)
let test55 = 
  let high_arity_sig = basic_sig @ [("high", 10)] in
  let t55 = Node(("high", 10), Array.init 10 (fun i -> V ("x" ^ string_of_int i))) in
  printf "Test55: size of term with high-arity node: %d\n" (size t55)

(* Test 56: size - Large complex term *)
let test56 = 
  let make_complex n =
    let rec build depth idx =
      if depth = 0 then V ("x" ^ string_of_int idx)
      else if idx mod 3 = 0 then
        Node(("f", 2), [|build (depth-1) (2*idx); build (depth-1) (2*idx+1)|])
      else if idx mod 3 = 1 then
        Node(("g", 1), [|build (depth-1) (3*idx)|])
      else
        Node(("i", 3), [|
          build (depth-1) (3*idx); 
          build (depth-1) (3*idx+1); 
          build (depth-1) (3*idx+2)
        |])
    in
    build n 1
  in
  let t56 = make_complex 5 in
  printf "Test56: size of large complex term: %d\n" (size t56)

(* Test 57: size - Comparison with height *)
let test57 = 
  let t57 = make_left_heavy 10 in
  printf "Test57: size compared to height (should be 11 vs 21): height=%d, size=%d\n" 
         (ht t57) (size t57)

(* Test 58: size - Very large term *)
let test58 = 
  let t58 = make_balanced_term 12 in
  printf "Test58: size of very large term: %d\n" (size t58)

(* Test 59: size - Term with many duplicate subterms *)
let test59 = 
  let v = V "x" in
  let node = Node(("g", 1), [|v|]) in
  let t59 = Node(("f", 2), [|node; node|]) in
  printf "Test59: size of term with duplicate subterms: %d\n" (size t59)

(* Test 60: size - Empty constant *)
let test60 = 
  let t60 = Node(("h", 0), [||]) in
  printf "Test60: size of empty constant: %d\n" (size t60)

(* Test 61: vars - Variable *)
let test61 = 
  let t61 = V "x" in
  let vars61 = vars t61 in
  printf "Test61: vars of single variable: %s\n" 
         (String.concat ", " vars61)

(* Test 62: vars - Constant *)
let test62 = 
  let t62 = Node(("h", 0), [||]) in
  let vars62 = vars t62 in
  printf "Test62: vars of constant: %s\n" 
         (if vars62 = [] then "empty" else String.concat ", " vars62)

(* Test 63: vars - Simple term with different variables *)
let test63 = 
  let t63 = Node(("f", 2), [|V "x"; V "y"|]) in
  let vars63 = vars t63 in
  printf "Test63: vars of term with different variables: %s\n" 
         (String.concat ", " vars63)

(* Test 64: vars - Term with repeated variables *)
let test64 = 
  let t64 = Node(("f", 2), [|V "x"; V "x"|]) in
  let vars64 = vars t64 in
  printf "Test64: vars of term with repeated variables: %s\n" 
         (String.concat ", " vars64)

(* Test 65: vars - Complex term with multiple variables *)
let test65 = 
  let t65 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    Node(("f", 2), [|V "y"; V "z"|])
  |]) in
  let vars65 = vars t65 in
  printf "Test65: vars of complex term: %s\n" 
         (String.concat ", " vars65)

(* Test 66: vars - Term with many duplicate variables *)
let test66 = 
  let t66 = Node(("i", 3), [|
    Node(("f", 2), [|V "x"; V "y"|]);
    Node(("f", 2), [|V "x"; V "z"|]);
    Node(("f", 2), [|V "y"; V "z"|])
  |]) in
  let vars66 = vars t66 in
  printf "Test66: vars of term with many duplicate variables: %s\n" 
         (String.concat ", " vars66)

(* Test 67: vars - Term with no variables *)
let test67 = 
  let t67 = Node(("f", 2), [|
    Node(("h", 0), [||]);
    Node(("h", 0), [||])
  |]) in
  let vars67 = vars t67 in
  printf "Test67: vars of term with no variables: %s\n" 
         (if vars67 = [] then "empty" else String.concat ", " vars67)

(* Test 68: vars - Large term with many variables *)
let test68 = 
  let t68 = make_balanced_term 5 in  (* Uses variables like x0, x1, etc. *)
  let vars68 = vars t68 in
  printf "Test68: vars of large term (%d unique variables): [%s%s]\n" 
         (List.length vars68)
         (String.concat ", " (List.filteri (fun i _ -> i < 5) vars68))
         (if List.length vars68 > 5 then ", ..." else "")

(* Test 69: vars - Large term with repeated variables *)
let test69 = 
  let rec make_term_with_limited_vars depth =
    if depth = 0 then
      V (String.make 1 (Char.chr (97 + (depth mod 3))))  (* a, b, c only *)
    else
      Node(("f", 2), [|
        make_term_with_limited_vars (depth - 1);
        make_term_with_limited_vars (depth - 1)
      |])
  in
  let t69 = make_term_with_limited_vars 6 in
  let vars69 = vars t69 in
  printf "Test69: vars of large term with limited variables: %s\n" 
         (String.concat ", " vars69)

(* Test 70: vars - Term with variables having special characters *)
let test70 = 
  let t70 = Node(("f", 2), [|
    V "x_1";
    Node(("g", 1), [|V "y'"|])
  |]) in
  let vars70 = vars t70 in
  printf "Test70: vars of term with special character variables: %s\n" 
         (String.concat ", " vars70)

(* Test 71: vars - Term with mixed repeated and unique variables *)
let test71 = 
  let t71 = Node(("i", 3), [|
    V "a"; 
    Node(("f", 2), [|V "a"; V "b"|]); 
    Node(("g", 1), [|V "c"|])
  |]) in
  let vars71 = vars t71 in
  printf "Test71: vars of term with mixed repeated/unique variables: %s\n" 
         (String.concat ", " vars71)

(* Test 72: vars - Very large term with many variables *)
let test72 = 
  let rec build_large_var_term depth idx =
    if depth = 0 then
      V ("var" ^ string_of_int (idx mod 20))  (* Limit to 20 distinct vars *)
    else
      Node(("f", 2), [|
        build_large_var_term (depth-1) (2*idx);
        build_large_var_term (depth-1) (2*idx+1)
      |])
  in
  let t72 = build_large_var_term 8 1 in
  let vars72 = vars t72 in
  printf "Test72: vars of very large term (expected vars ~20): %d unique vars\n" 
         (List.length vars72)

(* Test 73: vars - Deep term with unique variables at each level *)
let test73 = 
  let rec build_deep_var_term depth =
    if depth = 0 then
      V "x0"
    else
      Node(("f", 2), [|
        V ("x" ^ string_of_int depth);
        build_deep_var_term (depth - 1)
      |])
  in
  let t73 = build_deep_var_term 10 in
  let vars73 = vars t73 in
  printf "Test73: vars of deep term with level-specific variables: %d vars\n" 
         (List.length vars73)

(* Test 74: vars - Term with numeric variable names *)
let test74 = 
  let t74 = Node(("f", 2), [|V "1"; V "2"|]) in
  let vars74 = vars t74 in
  printf "Test74: vars of term with numeric variable names: %s\n" 
         (String.concat ", " vars74)

(* Test 75: vars - Term with empty string variable (edge case) *)
let test75 = 
  let t75 = Node(("f", 2), [|V ""; V "x"|]) in
  let vars75 = vars t75 in
  printf "Test75: vars of term with empty string variable: %s\n" 
         (String.concat ", " vars75)

(* Basic substitution tests *)
let basic_subst = [("x", Node(("h", 0), [||])); ("y", V "z")]

(* Test 76: subst - Apply to variable that is in substitution *)
let test76 = 
  let t76_before = V "x" in
  let t76_after = subst t76_before basic_subst in
  printf "Test76: subst variable in substitution: %s\n" 
         (match t76_after with
          | V _ -> "still variable"
          | Node((name, _), _) -> "node with symbol " ^ name)

(* Test 77: subst - Apply to variable not in substitution *)
let test77 = 
  let t77_before = V "w" in  (* not in basic_subst *)
  let t77_after = subst t77_before basic_subst in
  printf "Test77: subst variable not in substitution: %s\n" 
         (match t77_after with
          | V var -> "still variable " ^ var
          | Node _ -> "incorrectly substituted")

(* Test 78: subst - Apply to compound term *)
let test78 = 
  let t78_before = Node(("f", 2), [|V "x"; V "y"|]) in
  let t78_after = subst t78_before basic_subst in
  printf "Test78: subst compound term: %s\n"
         (match t78_after with
          | Node((sym, _), args) -> 
              let arg0_desc = match args.(0) with
                | V _ -> "variable"
                | Node((s, _), _) -> "node " ^ s
              in
              let arg1_desc = match args.(1) with
                | V var -> "variable " ^ var
                | Node _ -> "node"
              in
              sprintf "%s with args [%s, %s]" sym arg0_desc arg1_desc
          | V _ -> "incorrectly became variable")