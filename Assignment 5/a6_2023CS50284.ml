(* Aditya Anand: 2023CS50284 *)

open Printf

exception NOT_UNIFIABLE
exception SYMBOL_NOT_FOUND
exception INDEX_OUT_OF_BOUNDS
exception INVALID

type variable = string
type symbol = string * int  

type signature = (symbol list)

type term = V of variable | Node of symbol * (term array)


let rec check_negative_arity (x : signature) : bool= match x with
  | [] -> false
  | (_, arity) :: xs -> 
      if arity < 0 then 
        true
      else check_negative_arity xs



let check_sig (sign: signature) : bool = 
    (* Check all arities grester than equall 0 *)
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



let wfterm sym term =
    if ((check_sig sym) = false) then
        false
    else
      let table_size = List.length sym in
      let sig_table = Hashtbl.create (table_size) in

      let rec table_make = function
        | [] -> ()
        | (sign, arity) :: remain ->
            Hashtbl.add sig_table sign arity;
            table_make remain
      in
      table_make sym;
        
      let rec wellform_see = function
        | V _ -> true
        | Node((sign, _), rem_term) ->
            try
              let actual_arity = Array.length rem_term in
              let expected_arity = 
                try Hashtbl.find sig_table sign
                with Not_found -> 
                  raise (SYMBOL_NOT_FOUND)
              in
              if expected_arity <> actual_arity then
                false
              else
                Array.for_all wellform_see rem_term
            with SYMBOL_NOT_FOUND -> false
      in
      wellform_see term
;;


let ht (term: term) : int =
  let rec term_ht = function
    | V _ -> 0
    | Node(_, subterms) ->
        if Array.length subterms = 0 then 0
        else 1 + Array.fold_left(fun grp t -> max grp (term_ht t)) 0 subterms
  in
  term_ht term
;;



let size (term: term) : int =
  let rec term_size = function
    | V _ -> 1
    | Node(_, subterms) -> 
        1 + Array.fold_left (fun grp t -> grp + term_size t) 0 subterms
  in
  term_size term
;;



let vars (term: term) =
  let var_set = Hashtbl.create 10 in
  let rec var_list = function
    | V v -> Hashtbl.replace var_set v true
    | Node(_, subterms) -> Array.iter var_list subterms
  in
  var_list term;
  Hashtbl.fold (fun v _ grp -> v :: grp) var_set []
;;


(* SUBSTITUTION *)
type substitution = (variable, term) Hashtbl.t

let subst_emp () = Hashtbl.create 15

let initial_subst var term =
  let subst = Hashtbl.create 1 in
  Hashtbl.add subst var term;
  subst

let rec check_varexist variable term =match term with
  | V v -> v = variable
  | Node(_, sub_terms) -> Array.exists (check_varexist variable) sub_terms

(* DOING SUBSTITUTION *)
let subst (term: term ) (substi: substitution) =
  let rec make_subst z = match z with
    | V x -> 
        (try 
          let replacement = Hashtbl.find substi x in
          make_subst replacement
        with Not_found -> z)
    | Node(s,rem_term) -> 
        Node(s,Array.map make_subst rem_term)
  in
  make_subst term

(* COMPOSED SUBSTITUTION *)
let compose (subst1: substitution) (subst2: substitution) : substitution =
  let length_subst1 = Hashtbl.length subst1 in
  let length_subst2 = Hashtbl.length subst2 in
  let new_len = length_subst1 + length_subst2 in
   
  let composed_res = Hashtbl.create (new_len) in
  
  Hashtbl.iter (fun var term -> 
    let substituted_term = subst term subst2 in
    Hashtbl.add composed_res var substituted_term
  ) subst1;
  
  Hashtbl.iter (fun var term ->
    if not (Hashtbl.mem composed_res var) then
      Hashtbl.add composed_res var term
  ) subst2;
  
  composed_res

(* Most General Unifier *)
let mgu term_1 term_2 =

    let final = subst_emp() in
    
    let rec subst_all sigma exp =
      List.map (fun (left, right) -> (subst left sigma, subst right sigma)) exp
    in
    
    let rec up_res signa =
      Hashtbl.iter (fun var term ->
        if Hashtbl.mem final var then
          Hashtbl.replace final var (subst (Hashtbl.find final var) signa)
        else
          Hashtbl.add final var term
      ) signa
    in
    
    let rec mgu_note exp =
      match exp with
      | [] -> final 
      | (s, t) :: last_rem when s = t -> mgu_note last_rem
      | (V x, V y) :: last_rem when x=y ->mgu_note last_rem
      | (V x, V y) :: last_rem when x <> y ->
          if check_varexist x (V y) then 
            raise NOT_UNIFIABLE
          else begin
            let sigma = initial_subst x (V y) in
            Hashtbl.add final x (V y);
            let new_eqs = subst_all sigma last_rem in
            up_res sigma;
            mgu_note new_eqs
          end
      
      (* Variable and term *)
      | (V x, ter) :: rest -> 
          if check_varexist x ter then 
            raise NOT_UNIFIABLE
          else begin
            let sigma = initial_subst x ter in
            Hashtbl.add final x ter;
            let new_eqs = subst_all sigma rest in
            up_res sigma;
            mgu_note new_eqs
          end
      | (ter, V x) :: rest -> mgu_note ((V x, ter) :: rest)
      
      (* Two Terms *)
      | (Node((var_1, first_arity), sub_term1), Node((var_2, second_arity), sub_term2)) :: rest ->
          if ((var_1 <> var_2) || (first_arity <> second_arity)) then
            raise NOT_UNIFIABLE
          else
            let new_eqs = ref rest in
            let len_subterm = Array.length sub_term1 in
            for y = len_subterm - 1 downto 0 do
              new_eqs := (sub_term1.(y), sub_term2.(y)) :: !new_eqs
            done;
            mgu_note !new_eqs
    in
    
    try
      mgu_note [(term_1, term_2)]

    with NOT_UNIFIABLE -> raise NOT_UNIFIABLE

let edit point_pos term new_subterm =
  if point_pos = [] then new_subterm  
  else
    let rec change_ter alph_term pos = match alph_term, pos with
      | _, [] -> new_subterm  
      | Node(sym, sub_terms), index :: rest_pos ->
          let len_remain = Array.length sub_terms in
          if ((index >= len_remain) || (index < 0)) then
            raise (INDEX_OUT_OF_BOUNDS)
          else
            let new_term = Array.copy sub_terms in
            new_term.(index) <- change_ter sub_terms.(index) rest_pos;
            Node(sym, new_term)
      | V _, _ -> raise (INVALID)
    in

    try
      change_ter term point_pos
    with 
      | INDEX_OUT_OF_BOUNDS ->Printf.eprintf "Got Error: Index out of bounds\n";
          term  
      | INVALID-> Printf.eprintf "Got Error: Cannot search into a variable\n";
          term  

(* INPLACE SUBSTITUTE *)
let subst_in_place term substitute =
  let rec rec_substitution gam visited_var = match gam with
    | V x ->
        if Hashtbl.mem visited_var x then gam
        else
          (try 
            let replacement = Hashtbl.find substitute x in
            Hashtbl.add visited_var x true;
            let final = rec_substitution replacement visited_var in
            Hashtbl.remove visited_var x;
            final
          with Not_found -> gam)
    | Node(sym, sub_terms) -> let n = ref 0 in 
        let args_length = Array.length sub_terms in
        while (!n < args_length) do
          sub_terms.(!n) <- rec_substitution sub_terms.(!n) visited_var;
          n := !n + 1  
        done;
        gam
  in
  let visited_var = Hashtbl.create 15 in
  rec_substitution term visited_var





(* ---------------- TESTCASES ----------------------------------------- *)


let rec string_term = function
  | V x -> "V(" ^ x ^ ")"
  | Node((s, _), sub_terms) ->
      if Array.length sub_terms = 0 then
        s
      else
        s ^ "(" ^ (String.concat ", " (Array.to_list (Array.map string_term sub_terms))) ^ ")"


let print_sub sigma =
  Printf.printf "Substitution:\n";
  Hashtbl.iter (fun var term ->
    Printf.printf "  %s -> %s\n" var (string_term term)
  ) sigma

let () =
  Printf.printf "Testing my Code\n";

  (* Test 1: Signature validation *)
  let valid_sig = [("f", 2); ("g", 1); ("h", 0)] in
  let invalid_sig1 = [("f", 2); ("f", 1)] in  
  let invalid_sig2 = [("f", 2); ("g", -1)] in  
  
  Printf.printf "Test 1: Signature Validation\n";
  Printf.printf "  Valid signature: %b\n" (check_sig valid_sig);
  Printf.printf "  Invalid signature (repeated symbol): %b\n" (check_sig invalid_sig1);
  Printf.printf "  Invalid signature (negative arity): %b\n" (check_sig invalid_sig2);
  Printf.printf "\n";

  (* Test 2: Well-formed terms *)
  let term1 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    Node(("h", 0), [||])
  |]) in
  
  let term2 = Node(("f", 2), [|
    V "y";
    Node(("g", 1), [|V "x"|])
  |]) in

  let invalid_term = Node(("f", 2), [|V "x"|]) in  (* Wrong arity *)
  
  Printf.printf "Test 2: Well-formed Terms\n";
  Printf.printf "  term1 = %s\n" (string_term term1);
  Printf.printf "  term2 = %s\n" (string_term term2);
  Printf.printf "  invalid_term = %s\n" (string_term invalid_term);
  Printf.printf "  Is term1 well-formed? %b\n" (wfterm valid_sig term1);
  Printf.printf "  Is term2 well-formed? %b\n" (wfterm valid_sig term2);
  Printf.printf "  Is invalid_term well-formed? %b\n" (wfterm valid_sig invalid_term);
  Printf.printf "\n";

  (* Test 3: Term properties *)
  Printf.printf "Test 3: Term Properties\n";
  Printf.printf "  Height of term1: %d\n" (ht term1);
  Printf.printf "  Size of term1: %d\n" (size term1);
  Printf.printf "  Variables in term1: %s\n" (String.concat ", " (vars term1));
  Printf.printf "  Height of term2: %d\n" (ht term2);
  Printf.printf "  Size of term2: %d\n" (size term2);
  Printf.printf "  Variables in term2: %s\n" (String.concat ", " (vars term2));
  Printf.printf "\n";

  (* Test 4: Simple substitution *)
  Printf.printf "Test 4: Simple Substitution\n";
  let sigma = subst_emp() in
  Hashtbl.add sigma "x" (Node(("h", 0), [||]));
  Hashtbl.add sigma "y" (V "z");
  
  Printf.printf "  Original term1: %s\n" (string_term term1);
  Printf.printf "  Substitution:\n";
  Printf.printf "    x -> h\n";
  Printf.printf "    y -> z\n";
  let term1' = subst term1 sigma in
  Printf.printf "  After substitution: %s\n" (string_term term1');
  Printf.printf "\n";

  (* Test 5: Substitution composition *)
  Printf.printf "Test 5: Substitution Composition\n";
  let sigma1 = subst_emp() in
  Hashtbl.add sigma1 "x" (V "y");
  Hashtbl.add sigma1 "z" (Node(("h", 0), [||]));
  
  let sigma2 = subst_emp() in
  Hashtbl.add sigma2 "y" (Node(("g", 1), [|V "w"|]));
  
  Printf.printf "  sigma1:\n";
  Printf.printf "    x -> y\n";
  Printf.printf "    z -> h\n";
  Printf.printf "  sigma2:\n";
  Printf.printf "    y -> g(w)\n";
  
  let composed = compose sigma1 sigma2 in
  Printf.printf "  Composed substitution (sigma1 ∘ sigma2):\n";
  Hashtbl.iter (fun var term ->
    Printf.printf "    %s -> %s\n" var (string_term term)
  ) composed;
  Printf.printf "\n";

  (*(* Test 6: Simple unification *)
  Printf.printf "Test 6: Simple Unification\n";
  let term_1 = Node(("f", 2), [|V "x"; V "y"|]) in
  let term_2 = Node(("f", 2), [|V "z"; Node(("h", 0), [||])|]) in
  
  Printf.printf "  term_1 = %s\n" (string_term term_1);
  Printf.printf "  term_2 = %s\n" (string_term term_2);
  
  try
    let unifier = mgu term_1 term_2 in
    Printf.printf "  Unifier:\n";
    Hashtbl.iter (fun var term ->
      Printf.printf "    %s -> %s\n" var (string_term term)
    ) unifier;
  with NOT_UNIFIABLE ->
    Printf.printf "  Terms are not unifiable!\n";
  Printf.printf "\n";*)

  (* Test 7: Occurs check unification failure *)
  Printf.printf "Test 7: Occurs Check Unification\n";
  let t3 = V "x" in
  let t4 = Node(("f", 1), [|V "x"|]) in
  
  Printf.printf "  t3 = %s\n" (string_term t3);
  Printf.printf "  t4 = %s\n" (string_term t4);
  
  try
    let unifier = mgu t3 t4 in
    Printf.printf "  Unifier:\n";
    Hashtbl.iter (fun var term ->
      Printf.printf "    %s -> %s\n" var (string_term term)
    ) unifier;
  with NOT_UNIFIABLE ->
    Printf.printf "  Terms are not unifiable! (Occurs check failure)\n";
  Printf.printf "\n";

  (*(* Test 8: Complex unification *)
  Printf.printf "Test 8: Complex Unification\n";
  let t5 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    V "y"
  |]) in
  let t6 = Node(("f", 2), [|
    V "z";
    Node(("g", 1), [|V "w"|])
  |]) in
  
  Printf.printf "  t5 = %s\n" (string_term t5);
  Printf.printf "  t6 = %s\n" (string_term t6);
  
  try
    let unifier = mgu t5 t6 in
    Printf.printf "  Unifier:\n";
    Hashtbl.iter (fun var term ->
      Printf.printf "    %s -> %s\n" var (string_term term)
    ) unifier;
  with NOT_UNIFIABLE ->
    Printf.printf "  Terms are not unifiable!\n";
  Printf.printf "\n";*)

  (* Test 9: Edit function *)
  Printf.printf "Test 9: Edit Function\n";
  let original = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    Node(("h", 0), [||])
  |]) in
  let replacement = V "z" in
  let point_pos = [0] in  (* Replace the first argument of f *)
  
  Printf.printf "  Original term: %s\n" (string_term original);
  Printf.printf "  Replacement: %s\n" (string_term replacement);
  Printf.printf "  Position: [0]\n";
  
  let edited = edit point_pos original replacement in
  Printf.printf "  After edit: %s\n" (string_term edited);
  Printf.printf "\n";

  (* Test 10: In-place substitution *)
  Printf.printf "Test 10: In-place Substitution\n";
  let t = Node(("f", 2), [|V "x"; V "y"|]) in
  let s = subst_emp() in
  Hashtbl.add s "x" (Node(("h", 0), [||]));
  Hashtbl.add s "y" (V "z");
  
  Printf.printf "  Original term: %s\n" (string_term t);
  Printf.printf "  Substitution:\n";
  Printf.printf "    x -> h\n";
  Printf.printf "    y -> z\n";
  
  let final = subst_in_place t s in
  Printf.printf "  After in-place substitution: %s\n" (string_term final);
  Printf.printf "  Original term (should be modified): %s\n" (string_term t);

  Printf.printf "\n";

  (*(* Test 11: Deeply nested terms *)
  let make n acc =
    let rec aux n acc =
      if n = 0 then acc
      else aux (n-1) (Node(("g", 1), [|acc|]))
    in
    aux n acc
  in
  let deep_term1 = Node(("f", 2), [|make 10 (V "x"); V "y"|]) in
  let deep_term2 = Node(("f", 2), [|V "z"; make 10 (V "w")|]) in

  Printf.printf "Test 11: Deeply Nested Terms\n";
  let deep_term1 = 
    Node(("f", 2), [|make 10 (V "x"); V "y"|])
  in
  let deep_term2 = 
    Node(("f", 2), [|V "z"; make 10 (V "w")|])
  in
  Printf.printf "  deep_term1 = %s\n" (string_term deep_term1);
  Printf.printf "  deep_term2 = %s\n" (string_term deep_term2);
  try
    let unifier = mgu deep_term1 deep_term2 in
    Printf.printf "  Unifier:\n";
    Hashtbl.iter (fun var term ->
      Printf.printf "    %s -> %s\n" var (string_term term)
    ) unifier;
  with NOT_UNIFIABLE ->
    Printf.printf "  Terms are not unifiable!\n";
  Printf.printf "\n";*)

  Printf.printf "Test 12: Large Substitution Composition\n";
let sigma1 = subst_emp () in
let sigma2 = subst_emp () in
for i = 1 to 20 do
  Hashtbl.add sigma1 ("x" ^ string_of_int i) (V ("y" ^ string_of_int i));
  Hashtbl.add sigma2 ("y" ^ string_of_int i) (Node(("h", 0), [||]));
done;
let composed = compose sigma1 sigma2 in
Printf.printf "  Composed substitution:\n";
Hashtbl.iter (fun var term ->
  Printf.printf "    %s -> %s\n" var (string_term term)
) composed;
Printf.printf "\n";

(*Printf.printf "Test 13: Unification with Many Variables\n";
let vars = Array.init 15 (fun i -> V ("x" ^ string_of_int i)) in
let termA = Node(("f", 15), vars) in
let termB = Node(("f", 15), Array.init 15 (fun i -> Node(("g", 1), [|V ("y" ^ string_of_int i)|]))) in
try
  let unifier = mgu termA termB in
  Printf.printf "  Unifier:\n";
  Hashtbl.iter (fun var term ->
    Printf.printf "    %s -> %s\n" var (string_term term)
  ) unifier;
with NOT_UNIFIABLE ->
  Printf.printf "  Terms are not unifiable!\n";
Printf.printf "\n";*)


Printf.printf "Test 14: Large In-place Substitution\n";
let t = Node(("f", 10), Array.init 10 (fun i -> V ("x" ^ string_of_int i))) in
let s = subst_emp () in
for i = 0 to 9 do
  Hashtbl.add s ("x" ^ string_of_int i) (Node(("h", 0), [||]));
done;
Printf.printf "  Original term: %s\n" (string_term t);
let final = subst_in_place t s in
Printf.printf "  After in-place substitution: %s\n" (string_term final);
Printf.printf "  Original term (should be modified): %s\n" (string_term t);
Printf.printf "\n";


(*Printf.printf "Test 15: Unification Failure with Large Terms\n";
let t1 = Node(("f", 5), [|V "a"; V "b"; V "c"; V "d"; V "e"|]) in
let t2 = Node(("f", 5), [|V "a"; V "b"; V "c"; V "d"; Node(("g", 2), [|V "x"; V "x"|])|]) in
try
  let unifier = mgu t1 t2 in
  Printf.printf "  Unifier:\n";
  Hashtbl.iter (fun var term ->
    Printf.printf "    %s -> %s\n" var (string_term term)
  ) unifier;
with NOT_UNIFIABLE ->
  Printf.printf "  Terms are not unifiable!\n";
Printf.printf "\n";*)

Printf.printf "Test 16: Occurs Check Failure (Direct)\n";
let t1 = V "x" in
let t2 = Node(("f", 1), [|V "x"|]) in
try
  let _ = mgu t1 t2 in
  Printf.printf "  ERROR: Unification should have failed (occurs check)!\n"
with NOT_UNIFIABLE ->
  Printf.printf "  Correctly failed: Occurs check detected.\n";
Printf.printf "\n";

Printf.printf "Test 17: Occurs Check Failure (Indirect)\n";
let t1 = V "x" in
let t2 = Node(("f", 1), [|Node(("g", 1), [|V "x"|])|]) in
try
  let _ = mgu t1 t2 in
  Printf.printf "  ERROR: Unification should have failed (occurs check)!\n"
with NOT_UNIFIABLE ->
  Printf.printf "  Correctly failed: Occurs check detected.\n";
Printf.printf "\n";


Printf.printf "Test 18: Different Root Symbols\n";
let t1 = Node(("f", 1), [|V "x"|]) in
let t2 = Node(("g", 1), [|V "x"|]) in
try
  let _ = mgu t1 t2 in
  Printf.printf "  ERROR: Unification should have failed (different root symbols)!\n"
with NOT_UNIFIABLE ->
  Printf.printf "  Correctly failed: Different root symbols.\n";
Printf.printf "\n";


Printf.printf "Test 19: Different Arity\n";
let t1 = Node(("f", 2), [|V "x"; V "y"|]) in
let t2 = Node(("f", 1), [|V "z"|]) in
try
  let _ = mgu t1 t2 in
  Printf.printf "  ERROR: Unification should have failed (different arity)!\n"
with NOT_UNIFIABLE ->
  Printf.printf "  Correctly failed: Different arity.\n";
Printf.printf "\n";


Printf.printf "Test 20: Occurs Check with Multiple Variables\n";
let t1 = V "x" in
let t2 = Node(("f", 2), [|V "y"; V "x"|]) in
try
  let _ = mgu t1 t2 in
  Printf.printf "  ERROR: Unification should have failed (occurs check)!\n"
with NOT_UNIFIABLE ->
  Printf.printf "  Correctly failed: Occurs check detected.\n";
Printf.printf "\n";


Printf.printf "Test 21: Large Nested Unification\n";
let t1 = Node(("f", 4), [|
  Node(("g", 2), [|V "a"; Node(("h", 1), [|V "b"|])|]);
  Node(("g", 2), [|V "c"; V "d"|]);
  Node(("h", 1), [|V "e"|]);
  V "x"
|]) in
let t2 = Node(("f", 4), [|
  Node(("g", 2), [|Node(("h", 1), [|V "y"|]); Node(("h", 1), [|V "z"|])|]);
  Node(("g", 2), [|V "w"; Node(("h", 1), [|V "u"|])|]);
  Node(("h", 1), [|V "v"|]);
  Node(("h", 1), [|V "t"|])
|]) in
Printf.printf "  t1 = %s\n" (string_term t1);
Printf.printf "  t2 = %s\n" (string_term t2);
try
  let unifier = mgu t1 t2 in
  Printf.printf "  Unifier:\n";
  Hashtbl.iter (fun var term ->
    Printf.printf "    %s -> %s\n" var (string_term term)
  ) unifier;
with NOT_UNIFIABLE ->
  Printf.printf "  Terms are not unifiable!\n";
Printf.printf "\n";


Printf.printf "Test 22: Many Variables and Deep Nesting\n";
let t1 = Node(("f", 5), [|
  V "a";
  Node(("g", 2), [|V "b"; Node(("h", 1), [|V "c"|])|]);
  Node(("g", 2), [|V "d"; V "e"|]);
  Node(("h", 1), [|V "f"|]);
  V "x"
|]) in
let t2 = Node(("f", 5), [|
  Node(("h", 1), [|V "y"|]);
  Node(("g", 2), [|Node(("h", 1), [|V "z"|]); Node(("h", 1), [|V "u"|])|]);
  Node(("g", 2), [|V "w"; Node(("h", 1), [|V "v"|])|]);
  Node(("h", 1), [|V "t"|]);
  Node(("h", 1), [|V "s"|])
|]) in
Printf.printf "  t1 = %s\n" (string_term t1);
Printf.printf "  t2 = %s\n" (string_term t2);
try
  let unifier = mgu t1 t2 in
  Printf.printf "  Unifier:\n";
  Hashtbl.iter (fun var term ->
    Printf.printf "    %s -> %s\n" var (string_term term)
  ) unifier;
with NOT_UNIFIABLE ->
  Printf.printf "  Terms are not unifiable!\n";
Printf.printf "\n";



Printf.printf "Test 23: Large Substitution Chain\n";
let t1 = Node(("f", 3), [|V "a"; V "b"; V "c"|]) in
let t2 = Node(("f", 3), [|V "x"; V "y"; V "z"|]) in
let sigma = subst_emp () in
Hashtbl.add sigma "x" (V "b");
Hashtbl.add sigma "y" (V "c");
Hashtbl.add sigma "z" (Node(("h", 1), [|V "a"|]));
let t2_subst = subst t2 sigma in
Printf.printf "  t1 = %s\n" (string_term t1);
Printf.printf "  t2 after substitution = %s\n" (string_term t2_subst);
try
  let unifier = mgu t1 t2_subst in
  Printf.printf "  Unifier:\n";
  Hashtbl.iter (fun var term ->
    Printf.printf "    %s -> %s\n" var (string_term term)
  ) unifier;
with NOT_UNIFIABLE ->
  Printf.printf "  Terms are not unifiable!\n";
Printf.printf "\n";

Printf.printf "End \n";





