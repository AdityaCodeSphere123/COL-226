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
;;

(* 2. Check if a term is well-formed according to a signature *)
let wfterm sym term =
    if ((check_sig sym) = false) then
        false
    else
      (* Check if the term is well-formed according to the signature *)
      let table_size = List.length sym in
      let sig_table = Hashtbl.create (table_size) in
      
      (* Recursive function to build symbol table *)
      let rec table_make = function
        | [] -> ()
        | (sign, arity) :: remain ->
            Hashtbl.add sig_table sign arity;
            table_make remain
      in
      table_make sym;
        
      (* Check if the term is well-formed *)
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
;;

(* 3. Calculate the height of a term *)
let ht (term: term) : int =
  let rec height = function
    | V _ -> 0
    | Node(_, subterms) ->
        if Array.length subterms = 0 then 0
        else 1 + Array.fold_left (fun acc t -> max acc (height t)) 0 subterms
  in
  height term
;;

(* Calculate the size (number of nodes) of a term *)
let size term =
  let rec count = function
    | V _ -> 1
    | Node(_, subterms) -> 
        1 + Array.fold_left (fun acc t -> acc + count t) 0 subterms
  in
  count term
;;


(* Extract the set of variables in a term *)
let vars term =
  let var_set = Hashtbl.create 10 in
  let rec collect = function
    | V v -> Hashtbl.replace var_set v true
    | Node(_, subterms) -> Array.iter collect subterms
  in
  collect term;
  Hashtbl.fold (fun v _ acc -> v :: acc) var_set []
;;


(* 4. Substitution representation as a list of variable-term pairs *)
type substitution = (variable, term) Hashtbl.t

(* 5. Apply a substitution to a term *)
let subst (term: term) (sigma: substitution) =
  let rec make_subst t =match t with
    | V x -> (try Hashtbl.find sigma x with Not_found -> t)
    | Node(s, rem_term) -> Node(s, Array.map make_subst rem_term)
  in
  make_subst term
;;


(* 6. Compose two substitutions s1 and s2 (s1 ∘ s2) *)
let compose (s1: substitution) (s2: substitution) : substitution =

  let new_composition = Hashtbl.create (Hashtbl.length s1 + Hashtbl.length s2) in

  (* Apply s1 to the range of s2 and add to the new_composition substitution *)
  Hashtbl.iter (fun var term -> Hashtbl.add new_composition var (subst term s1)) s2;

  (* Add bindings from s1 whose domain variables are not in s2's domain *)
  Hashtbl.iter (fun var term -> if not (Hashtbl.mem s2 var) then
      Hashtbl.add new_composition var term
  ) s1;

  new_composition
;;

(* 7. Check if a variable occurs in a term (occurs check) *)
let rec occurs var term = match term with
  | V v -> v = var
  | Node(_, args) -> Array.exists (occurs var) args

(* Most general unifier implementation *)
let mgu t1 t2 =
  let rec unify eqs acc = match eqs with
    | [] -> acc
    | (s, t) :: rest when s = t -> unify rest acc  (* Identical terms unify trivially *)
    | (V x, t) :: rest ->
        if occurs x t then
          raise NOT_UNIFIABLE  (* Occurs check failure *)
        else
          let subst_x_t = Hashtbl.create 1 in
          Hashtbl.add subst_x_t x t;  (* Directly use a hash table for substitution *)
          let rest' = List.map (fun (s, t) -> (subst s subst_x_t, subst t subst_x_t)) rest in
          Hashtbl.iter (fun var term -> Hashtbl.replace acc var term) subst_x_t;  (* Merge into acc *)
          unify rest' acc
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
    let result = Hashtbl.create 10 in
    unify [(t1, t2)] result;
    result  (* Return the resulting substitution as a hash table *)
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
let t1 = Node(("f", 2), [|V "x"; V "y"|]);
let t2 = Node(("f", 2), [|Node(("g", 1), [|V "z"|]); V "w"|]);

try
  let unifier = mgu t1 t2 in
  Hashtbl.iter (fun var term ->
    Printf.printf "%s -> " var;
    match term with
    | V v -> Printf.printf "V %s\n" v
    | Node((s, _), _) -> Printf.printf "Node %s\n" s
  ) unifier
with NOT_UNIFIABLE ->
  Printf.printf "Terms are not unifiable!\n";


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

(* Test 77: subst - Apply to variable not in substitution *)
let test77 = 
  let t77_before = V "w" in  (* not in basic_subst *)
  let t77_after = subst t77_before basic_subst in
  printf "Test77: subst variable not in substitution: %s\n" 
         (match t77_after with
          | V var -> "still variable " ^ var
          | _ -> "not a variable anymore")

(* Test 78: subst - Apply to constant *)
let test78 = 
  let t78_before = Node(("h", 0), [||]) in
  let t78_after = subst t78_before basic_subst in
  printf "Test78: subst constant: %b\n" (t78_before = t78_after)

(* Test 79: subst - Apply to simple term *)
let test79 = 
  let t79_before = Node(("f", 2), [|V "x"; V "y"|]) in
  let t79_after = subst t79_before basic_subst in
  printf "Test79: subst simple term: %s\n" 
         (match t79_after with
          | Node(_, args) -> 
              sprintf "node with %d args" (Array.length args)
          | _ -> "not a node")

(* Test 80: subst - Apply with variables that map to other variables *)
let test80 = 
  let t80_before = Node(("f", 2), [|V "x"; V "y"|]) in
  let subst80 = [("x", V "a"); ("y", V "b")] in
  let t80_after = subst t80_before subst80 in
  let vars80 = vars t80_after in
  printf "Test80: subst with var->var mappings: vars = %s\n" 
         (String.concat ", " vars80)

(* Test 81: subst - Apply with nested substitution effects *)
let test81 = 
  let t81_before = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    V "y"
  |]) in
  let subst81 = [("x", V "z"); ("y", Node(("g", 1), [|V "x"|]))] in
  let t81_after = subst t81_before subst81 in
  printf "Test81: subst with nested effects: results in term of size %d\n" 
         (size t81_after)

(* Test 82: subst - Apply with empty substitution *)
let test82 = 
  let t82_before = Node(("f", 2), [|V "x"; V "y"|]) in
  let t82_after = subst t82_before [] in
  printf "Test82: subst with empty substitution: %b\n" 
         (t82_before = t82_after)

(* Test 83: subst - Apply substitution to complex term *)
let test83 = 
  let t83_before = Node(("i", 3), [|
    Node(("f", 2), [|V "x"; V "y"|]);
    Node(("g", 1), [|V "z"|]);
    V "w"
  |]) in
  let subst83 = [
    ("x", Node(("h", 0), [||]));
    ("y", V "a");
    ("z", Node(("f", 2), [|V "b"; V "c"|]));
    ("w", V "d")
  ] in
  let t83_after = subst t83_before subst83 in
  printf "Test83: subst complex term: size before=%d, size after=%d\n" 
         (size t83_before) (size t83_after)

(* Test 84: subst - Apply to large term *)
let test84 = 
  let t84_before = make_balanced_term 5 in
  let subst84 = [("x0", V "a"); ("x1", V "b")] in
  let t84_after = subst t84_before subst84 in
  printf "Test84: subst large term: height before=%d, height after=%d\n" 
         (ht t84_before) (ht t84_after)

(* Test 85: subst - Substitution that creates a larger term *)
let test85 = 
  let t85_before = V "x" in
  let large_term = make_balanced_term 5 in
  let subst85 = [("x", large_term)] in
  let t85_after = subst t85_before subst85 in
  printf "Test85: subst creating larger term: size=%d\n" (size t85_after)

(* Test 86: subst - Multiple substitutions for same variable *)
let test86 = 
  let t86_before = Node(("f", 2), [|V "x"; V "x"|]) in
  let subst86 = [("x", V "y")] in
  let t86_after = subst t86_before subst86 in
  let vars86 = vars t86_after in
  printf "Test86: subst with repeated variables: vars=%s\n" 
         (String.concat ", " vars86)

(* Test 87: subst - Complex nested term with substitution *)
let test87 = 
  let t87_before = Node(("f", 2), [|
    Node(("f", 2), [|
      Node(("g", 1), [|V "x"|]);
      V "y"
    |]);
    Node(("g", 1), [|V "z"|])
  |]) in
  let subst87 = [
    ("x", Node(("h", 0), [||]));
    ("y", Node(("g", 1), [|V "a"|]));
    ("z", V "b")
  ] in
  let t87_after = subst t87_before subst87 in
  printf "Test87: subst complex nested term: size=%d, height=%d\n" 
         (size t87_after) (ht t87_after)

(* Test 88: subst - Very large term with minimal substitution *)
let test88 = 
  let t88_before = make_balanced_term 8 in
  let subst88 = [("x0", V "root")] in
  let t88_after = subst t88_before subst88 in
  printf "Test88: subst very large term with minimal subs: sizes equal? %b\n" 
         ((size t88_before) = (size t88_after))

(* Test 89: subst - Very large substitution *)
let test89 = 
  let t89_before = make_balanced_term 4 in
  let subst89 = List.init 100 (fun i -> 
    ("x" ^ string_of_int i, Node(("h", 0), [||]))
  ) in
  let t89_after = subst t89_before subst89 in
  printf "Test89: subst with very large substitution: vars before=%d, vars after=%d\n" 
         (List.length (vars t89_before)) (List.length (vars t89_after))

(* Test 90: subst - Identity substitution *)
let test90 = 
  let t90_before = Node(("f", 2), [|V "x"; V "y"|]) in
  let subst90 = [("x", V "x"); ("y", V "y")] in
  let t90_after = subst t90_before subst90 in
  printf "Test90: subst with identity substitution: terms equal? %b\n" 
         (t90_before = t90_after)

(* Tests for composition *)

(* Test 91: compose - Basic composition *)
let test91 = 
  let s1 = [("x", V "y")] in
  let s2 = [("y", V "z")] in
  let s3 = compose s1 s2 in
  printf "Test91: compose basic substitutions: %s\n" 
         (String.concat ", " (List.map (fun (v, t) -> 
           match t with 
           | V t_var -> v ^ "->" ^ t_var 
           | _ -> v ^ "->term"
         ) s3))

(* Test 92: compose - Empty substitutions *)
let test92 = 
  let s92_1 = [] in
  let s92_2 = [] in
  let s92_3 = compose s92_1 s92_2 in
  printf "Test92: compose empty substitutions: length=%d\n" (List.length s92_3)

(* Test 93: compose - Left empty substitution *)
let test93 = 
  let s93_1 = [] in
  let s93_2 = [("x", V "y"); ("z", Node(("h", 0), [||]))] in
  let s93_3 = compose s93_1 s93_2 in
  printf "Test93: compose with left empty: lengths equal? %b\n" 
         (List.length s93_2 = List.length s93_3)

(* Test 94: compose - Right empty substitution *)
let test94 = 
  let s94_1 = [("a", V "b"); ("c", Node(("f", 2), [|V "d"; V "e"|]))] in
  let s94_2 = [] in
  let s94_3 = compose s94_1 s94_2 in
  printf "Test94: compose with right empty: lengths equal? %b\n" 
         (List.length s94_1 = List.length s94_3)

(* Test 95: compose - Disjoint domains *)
let test95 = 
  let s95_1 = [("x", V "a"); ("y", V "b")] in
  let s95_2 = [("z", V "c"); ("w", V "d")] in
  let s95_3 = compose s95_1 s95_2 in
  printf "Test95: compose with disjoint domains: length=%d\n" (List.length s95_3)

(* Test 96: compose - Overlapping domains *)
let test96 = 
  let s96_1 = [("x", V "a"); ("y", V "b")] in
  let s96_2 = [("y", V "c"); ("z", V "d")] in
  let s96_3 = compose s96_1 s96_2 in
  printf "Test96: compose with overlapping domains: length=%d\n" (List.length s96_3)

(* Test 97: compose - Composition with complex terms *)
let test97 = 
  let s97_1 = [
    ("x", Node(("f", 2), [|V "y"; V "z"|]));
    ("w", V "u")
  ] in
  let s97_2 = [
    ("y", Node(("g", 1), [|V "a"|]));
    ("z", V "b")
  ] in
  let s97_3 = compose s97_1 s97_2 in
  printf "Test97: compose with complex terms: length=%d\n" (List.length s97_3)

(* Test 98: compose - Multi-step substitution chain *)
let test98 = 
  let s98_1 = [("x", V "y")] in
  let s98_2 = [("y", V "z")] in
  let s98_3 = [("z", V "w")] in
  let s98_12 = compose s98_1 s98_2 in
  let s98_123 = compose s98_12 s98_3 in
  let result = subst (V "x") s98_123 in
  printf "Test98: compose multi-step chain: result=%s\n" 
         (match result with V v -> v | _ -> "not a variable")

(* Test 99: compose - Large substitutions *)
let test99 = 
  let s99_1 = List.init 50 (fun i -> 
    ("x" ^ string_of_int i, V ("y" ^ string_of_int i))
  ) in
  let s99_2 = List.init 50 (fun i -> 
    ("y" ^ string_of_int i, V ("z" ^ string_of_int i))
  ) in
  let s99_3 = compose s99_1 s99_2 in
  printf "Test99: compose large substitutions: length=%d\n" (List.length s99_3)

(* Test 100: compose - Cyclical substitutions *)
let test100 = 
  let s100_1 = [("x", V "y"); ("y", V "z"); ("z", V "x")] in
  let s100_2 = [("a", V "b"); ("b", V "c"); ("c", V "a")] in
  let s100_3 = compose s100_1 s100_2 in
  printf "Test100: compose cyclical substitutions: length=%d\n" (List.length s100_3)

(* Test 101: compose - Composition with identity substitution left *)
let test101 = 
  let id_subst = [("x", V "x"); ("y", V "y")] in
  let s101 = [("x", V "z"); ("y", Node(("h", 0), [||]))] in
  let s101_result = compose id_subst s101 in
  printf "Test101: compose with identity left: modified s? %b\n" 
         (s101 <> s101_result)

(* Test 102: compose - Composition with identity substitution right *)
let test102 = 
  let s102 = [("x", V "z"); ("y", Node(("h", 0), [||]))] in
  let id_subst = [("z", V "z"); ("y", V "y")] in
  let s102_result = compose s102 id_subst in
  printf "Test102: compose with identity right: modified s? %b\n" 
         (s102 <> s102_result)

(* Test 103: compose - Complex substitution chain *)
let test103 = 
  let s1 = [("x", V "y")] in
  let s2 = [("y", Node(("f", 2), [|V "z"; V "w"|]))] in
  let s3 = [("z", V "a"); ("w", V "b")] in
  let s12 = compose s1 s2 in
  let s123 = compose s12 s3 in
  let result = subst (V "x") s123 in
  printf "Test103: compose complex chain: result height=%d\n" (ht result)

(* Test 104: compose - Very large substitution composition *)
let test104 = 
  let s1 = List.init 100 (fun i -> 
    ("x" ^ string_of_int i, 
     if i mod 2 = 0 then V ("y" ^ string_of_int i)
     else Node(("h", 0), [||]))
  ) in
  let s2 = List.init 100 (fun i -> 
    ("y" ^ string_of_int i, 
     if i mod 3 = 0 then V ("z" ^ string_of_int i)
     else Node(("g", 1), [|V ("z" ^ string_of_int i)|]))
  ) in
  let s3 = compose s1 s2 in
  printf "Test104: compose very large substitutions: length=%d\n" (List.length s3)

(* Test 105: compose - Substitution with constants *)
let test105 = 
  let s105_1 = [
    ("x", Node(("h", 0), [||]));
    ("y", Node(("h", 0), [||]))
  ] in
  let s105_2 = [("z", V "w")] in
  let s105_3 = compose s105_1 s105_2 in
  printf "Test105: compose with constants: length=%d\n" (List.length s105_3)

(* Tests for mgu *)

(* Test 106: mgu - Basic unification of variables *)
let test106 = 
  try
    let t106_1 = V "x" in
    let t106_2 = V "y" in
    let u106 = mgu t106_1 t106_2 in
    printf "Test106: mgu of two variables: %s\n" 
           (String.concat ", " (List.map (fun (v, t) -> 
             match t with 
             | V t_var -> v ^ "->" ^ t_var 
             | _ -> v ^ "->term"
           ) u106))
  with NOT_UNIFIABLE -> 
    printf "Test106: mgu of two variables: NOT_UNIFIABLE\n"

(* Test 107: mgu - Variables and constants *)
let test107 = 
  try
    let t107_1 = V "x" in
    let t107_2 = Node(("h", 0), [||]) in
    let u107 = mgu t107_1 t107_2 in
    printf "Test107: mgu of variable and constant: %s\n" 
           (String.concat ", " (List.map (fun (v, _) -> v) u107))
  with NOT_UNIFIABLE -> 
    printf "Test107: mgu of variable and constant: NOT_UNIFIABLE\n"

(* Test 108: mgu - Equal terms *)
let test108 = 
  try
    let t108 = Node(("f", 2), [|V "x"; V "y"|]) in
    let u108 = mgu t108 t108 in
    printf "Test108: mgu of identical terms: length=%d\n" (List.length u108)
  with NOT_UNIFIABLE -> 
    printf "Test108: mgu of identical terms: NOT_UNIFIABLE\n"

(* Test 109: mgu - Different function symbols *)
let test109 = 
  try
    let t109_1 = Node(("f", 2), [|V "x"; V "y"|]) in
    let t109_2 = Node(("g", 2), [|V "x"; V "y"|]) in
    let u109 = mgu t109_1 t109_2 in
    printf "Test109: mgu of different function symbols: %d bindings\n" 
           (List.length u109)
  with NOT_UNIFIABLE -> 
    printf "Test109: mgu of different function symbols: NOT_UNIFIABLE\n"

(* Test 110: mgu - Different arities *)
let test110 = 
  try
    let t110_1 = Node(("f", 2), [|V "x"; V "y"|]) in
    let t110_2 = Node(("f", 1), [|V "z"|]) in
    let u110 = mgu t110_1 t110_2 in
    printf "Test110: mgu of different arities: %d bindings\n" 
           (List.length u110)
  with NOT_UNIFIABLE -> 
    printf "Test110: mgu of different arities: NOT_UNIFIABLE\n"

(* Test 111: mgu - Simple unification *)
let test111 = 
  try
    let t111_1 = Node(("f", 2), [|V "x"; V "y"|]) in
    let t111_2 = Node(("f", 2), [|V "z"; Node(("h", 0), [||])|]) in
    let u111 = mgu t111_1 t111_2 in
    printf "Test111: mgu of simple terms: %d bindings\n" 
           (List.length u111)
  with NOT_UNIFIABLE -> 
    printf "Test111: mgu of simple terms: NOT_UNIFIABLE\n"

(* Test 112: mgu - Occurs check failure *)
let test112 = 
  try
    let t112_1 = V "x" in
    let t112_2 = Node(("f", 1), [|V "x"|]) in
    let u112 = mgu t112_1 t112_2 in
    printf "Test112: mgu with occurs check: %d bindings\n" 
           (List.length u112)
  with NOT_UNIFIABLE -> 
    printf "Test112: mgu with occurs check: NOT_UNIFIABLE\n"

(* Test 113: mgu - Deep occurs check *)
let test113 = 
  try
    let t113_1 = V "x" in
    let t113_2 = Node(("f", 1), [|
      Node(("f", 1), [|
        Node(("f", 1), [|V "x"|])
      |])
    |]) in
    let u113 = mgu t113_1 t113_2 in
    printf "Test113: mgu with deep occurs check: %d bindings\n" 
           (List.length u113)
  with NOT_UNIFIABLE -> 
    printf "Test113: mgu with deep occurs check: NOT_UNIFIABLE\n"

(* Test 114: mgu - Complex unification *)
let test114 = 
  try
    let t114_1 = Node(("f", 2), [|
      Node(("g", 1), [|V "x"|]);
      V "y"
    |]) in
    let t114_2 = Node(("f", 2), [|
      Node(("g", 1), [|Node(("h", 0), [||])|]);
      Node(("g", 1), [|V "z"|])
    |]) in
    let u114 = mgu t114_1 t114_2 in
    printf "Test114: mgu of complex terms: %d bindings\n" 
           (List.length u114)
  with NOT_UNIFIABLE -> 
    printf "Test114: mgu of complex terms: NOT_UNIFIABLE\n"

(* Test 115: mgu - Multiple equation unification *)
let test115 = 
  try
    let t115_1 = Node(("f", 3), [|V "x"; V "y"; V "z"|]) in
    let t115_2 = Node(("f", 3), [|V "z"; V "x"; V "y"|]) in
    let u115 = mgu t115_1 t115_2 in
    printf "Test115: mgu with multiple equations: %d bindings\n" 
           (List.length u115)
  with NOT_UNIFIABLE -> 
    printf "Test115: mgu with multiple equations: NOT_UNIFIABLE\n"

(* Test 116: mgu - Unification with large terms *)
let test116 = 
  try
    let t116_1 = make_balanced_term 3 in
    let t116_2 = make_balanced_term 3 in
    let u116 = mgu t116_1 t116_2 in
    printf "Test116: mgu of large terms: %d bindings\n" 
           (List.length u116)
  with NOT_UNIFIABLE -> 
    printf "Test116: mgu of large terms: NOT_UNIFIABLE\n"

(* Test 117: mgu - Unification with shared variables *)
let test117 = 
  try
    let t117_1 = Node(("f", 2), [|V "x"; V "x"|]) in
    let t117_2 = Node(("f", 2), [|V "y"; Node(("h", 0), [||])|]) in
    let u117 = mgu t117_1 t117_2 in
    printf "Test117: mgu with shared variables: %d bindings\n" 
           (List.length u117)
  with NOT_UNIFIABLE -> 
    printf "Test117: mgu with shared variables: NOT_UNIFIABLE\n"

(* Test 118: mgu - Unification requiring deep substitution *)
let test118 = 
  try
    let t118_1 = Node(("f", 2), [|
      V "x";
      Node(("g", 1), [|V "y"|])
    |]) in
    let t118_2 = Node(("f", 2), [|
      Node(("g", 1), [|V "z"|]);
      V "w"
    |]) in
    let u118 = mgu t118_1 t118_2 in
    printf "Test118: mgu requiring deep substitution: %d bindings\n" 
           (List.length u118)
  with NOT_UNIFIABLE -> 
    printf "Test118: mgu requiring deep substitution: NOT_UNIFIABLE\n"

(* Test 119: mgu - Very complex terms *)
let test119 = 
  try
    let t119_1 = Node(("f", 3), [|
      Node(("g", 2), [|V "x"; Node(("h", 0), [||])|]);
      V "y";
      Node(("g", 2), [|V "z"; V "w"|])
    |]) in
    let t119_2 = Node(("f", 3), [|
      Node(("g", 2), [|Node(("g", 2), [|V "a"; V "b"|]); V "c"|]);
      Node(("g", 2), [|V "d"; V "e"|]);
      V "f"
    |]) in
    let u119 = mgu t119_1 t119_2 in
    printf "Test119: mgu of very complex terms: %d bindings\n" 
           (List.length u119)
  with NOT_UNIFIABLE -> 
    printf "Test119: mgu of very complex terms: NOT_UNIFIABLE\n"

(* Test 120: mgu - Nested occurrences *)
let test120 = 
  try
    let t120_1 = Node(("f", 2), [|
      V "x";
      Node(("g", 1), [|V "y"|])
    |]) in
    let t120_2 = Node(("f", 2), [|
      Node(("g", 1), [|V "z"|]);
      V "x"
    |]) in
    let u120 = mgu t120_1 t120_2 in
    printf "Test120: mgu with nested occurrences: %d bindings\n" 
           (List.length u120)
  with NOT_UNIFIABLE -> 
    printf "Test120: mgu with nested occurrences: NOT_UNIFIABLE\n"

(* Tests for edit function *)

(* Test 121: edit - Replace at root *)
let test121 = 
  let t121 = Node(("f", 2), [|V "x"; V "y"|]) in
  let new_t121 = Node(("g", 1), [|V "z"|]) in
  let result = edit t121 [] new_t121 in
  printf "Test121: edit replace at root: symbol=%s\n" 
         (match result with
          | Node((s, _), _) -> s
          | V _ -> "variable")

(* Test 122: edit - Replace first subterm *)
let test122 = 
  let t122 = Node(("f", 2), [|V "x"; V "y"|]) in
  let new_t122 = Node(("g", 1), [|V "z"|]) in
  let result = edit t122 [0] new_t122 in
  printf "Test122: edit replace first subterm: %s\n" 
         (match result with
          | Node((s, _), args) -> 
              sprintf "%s with first arg %s" s 
                (match args.(0) with
                 | Node((s2, _), _) -> s2
                 | V _ -> "variable")
          | V _ -> "variable")

(* Test 123: edit - Replace at deep position *)
let test123 = 
  let t123 = Node(("f", 2), [|
    Node(("g", 1), [|
      Node(("h", 1), [|V "x"|])
    |]);
    V "y"
  |]) in
  let new_t123 = V "z" in
  let result = edit t123 [0; 0; 0] new_t123 in
  printf "Test123: edit replace at deep position: %s\n" 
         (let rec path_str t path =
            match path with
            | [] -> 
                (match t with
                 | V v -> "variable " ^ v
                 | Node((s, _), _) -> "node " ^ s)
            | i :: rest ->
                match t with
                | Node(_, args) -> 
                    if i >= 0 && i < Array.length args then
                      sprintf "node with subterm: %s" (path_str args.(i) rest)
                    else "invalid path"
                | V _ -> "invalid path into variable"
          in path_str result [0; 0])

(* Test 124: edit - Replace with complex term *)
let test124 = 
  let t124 = Node(("f", 2), [|V "x"; V "y"|]) in
  let new_t124 = Node(("f", 2), [|
    Node(("g", 1), [|V "a"|]);
    Node(("h", 0), [||])
  |]) in
  let result = edit t124 [1] new_t124 in
  printf "Test124: edit replace with complex term: size=%d\n" (size result)

(* Test 125: edit - Invalid position (too deep) *)
let test125 = 
  let t125 = Node(("f", 2), [|V "x"; V "y"|]) in
  let new_t125 = V "z" in
  try
    let result = edit t125 [0; 0] new_t125 in
    printf "Test125: edit invalid position (too deep): succeeded unexpectedly\n"
  with Invalid_argument msg ->
    printf "Test125: edit invalid position (too deep): caught exception: %s\n" 
           (if String.length msg > 20 then String.sub msg 0 20 ^ "..." else msg)

(* Test 126: edit - Invalid position (negative index) *)
let test126 = 
  let t126 = Node(("f", 2), [|V "x"; V "y"|]) in
  let new_t126 = V "z" in
  try
    let result = edit t126 [-1] new_t126 in
    printf "Test126: edit invalid position (negative): succeeded unexpectedly\n"
  with Invalid_argument msg ->
    printf "Test126: edit invalid position (negative): caught exception: %s\n" 
           (if String.length msg > 20 then String.sub msg 0 20 ^ "..." else msg)

(* Test 127: edit - Invalid position (index out of bounds) *)
let test127 = 
  let t127 = Node(("f", 2), [|V "x"; V "y"|]) in
  let new_t127 = V "z" in
  try
    let result = edit t127 [2] new_t127 in
    printf "Test127: edit invalid position (out of bounds): succeeded unexpectedly\n"
  with Invalid_argument msg ->
    printf "Test127: edit invalid position (out of bounds): caught exception: %s\n" 
           (if String.length msg > 20 then String.sub msg 0 20 ^ "..." else msg)

(* Test 128: edit - Position into variable *)
let test128 = 
  let t128 = V "x" in
  let new_t128 = V "y" in
  try
    let result = edit t128 [0] new_t128 in
    printf "Test128: edit position into variable: succeeded unexpectedly\n"
  with Invalid_argument msg ->
    printf "Test128: edit position into variable: caught exception: %s\n" 
           (if String.length msg > 20 then String.sub msg 0 20 ^ "..." else msg)

(* Test 129: edit - Replace at root with empty path *)
let test129 = 
  let t129 = Node(("f", 2), [|V "x"; V "y"|]) in
  let new_t129 = Node(("g", 1), [|V "z"|]) in
  let result = edit t129 [] new_t129 in
  printf "Test129: edit replace at root with empty path: %s\n" 
         (match result with
          | Node((s, _), _) -> s
          | V _ -> "variable")  
