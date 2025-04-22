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
    (* Check all arities greater than equal 0 *)
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

(* 4. Substitution representation as a hashtable mapping variables to terms *)
type substitution = (variable, term) Hashtbl.t

(* Create an empty substitution *)
let empty_subst () = Hashtbl.create 10

(* Create a singleton substitution mapping var to term *)
let singleton_subst var term =
  let subst = Hashtbl.create 1 in
  Hashtbl.add subst var term;
  subst

(* 5. Apply a substitution to a term *)
let subst (term: term) (sigma: substitution) =
  let rec make_subst t = match t with
    | V x -> 
        (try 
          let replacement = Hashtbl.find sigma x in
          (* Apply substitution recursively to handle chained substitutions *)
          make_subst replacement
        with Not_found -> t)
    | Node(s, rem_term) -> 
        Node(s, Array.map make_subst rem_term)
  in
  make_subst term

(* 6. Compose two substitutions s1 and s2 (s1 ∘ s2) *)
let compose (s1: substitution) (s2: substitution) : substitution =
  let result = Hashtbl.create (Hashtbl.length s1 + Hashtbl.length s2) in
  
  (* First add all bindings from s2 *)
  Hashtbl.iter (fun var term -> 
    Hashtbl.add result var term
  ) s2;
  
  (* Then add bindings from s1, applying s1 to the range of s2 *)
  Hashtbl.iter (fun var term ->
    (* If var is already bound in s2, skip it *)
    if not (Hashtbl.mem result var) then
      Hashtbl.add result var term
    else
      (* Apply s1 to the term bound to var in result *)
      let term_in_result = Hashtbl.find result var in
      Hashtbl.replace result var (subst term_in_result s1)
  ) s1;
  
  result

(* 7. Check if a variable occurs in a term (occurs check) *)
let rec occurs var term = match term with
  | V v -> v = var
  | Node(_, args) -> Array.exists (occurs var) args

(* Most general unifier implementation *)
let mgu t1 t2 =
  let result = empty_subst() in
  
  let rec unify eqs =
    match eqs with
    | [] -> ()  (* Success - all equations unified *)
    | (s, t) :: rest when s = t -> 
        unify rest  (* Identical terms unify trivially *)
    
    | (V x, t) :: rest ->
        if occurs x t then
          raise NOT_UNIFIABLE  (* Occurs check failure *)
        else begin
          (* Create substitution {x ↦ t} *)
          let sigma_x = singleton_subst x t in
          
          (* Apply substitution to remaining equations *)
          let rest' = List.map (fun (lhs, rhs) -> 
            (subst lhs sigma_x, subst rhs sigma_x)
          ) rest in
          
          (* Add binding to result *)
          Hashtbl.add result x t;
          
          unify rest'
        end
    
    | (t, V x) :: rest -> 
        unify ((V x, t) :: rest)  (* Swap to handle previous case *)
    
    | (Node(s1, args1), Node(s2, args2)) :: rest ->
        if s1 <> s2 || Array.length args1 <> Array.length args2 then
          raise NOT_UNIFIABLE
        else
          let new_eqs = List.init (Array.length args1) 
            (fun i -> (args1.(i), args2.(i))) 
          in
          unify (new_eqs @ rest)
  in
  
  try
    unify [(t1, t2)];
    result
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
  let rec apply t =
    match t with
    | V x ->
        (try Hashtbl.find sigma x
         with Not_found -> t)
    | Node(sym, args) ->
        (* Modify array elements in place *)
        for i = 0 to Array.length args - 1 do
          args.(i) <- apply args.(i)
        done;
        t  (* Return the same term with modified contents *)
  in
  apply term

(* Helper function to print a term *)
let rec string_of_term = function
  | V x -> "V(" ^ x ^ ")"
  | Node((s, _), args) ->
      if Array.length args = 0 then
        s
      else
        s ^ "(" ^ (String.concat ", " (Array.to_list (Array.map string_of_term args))) ^ ")"

(* Helper function to print a substitution *)
let print_subst sigma =
  Printf.printf "Substitution:\n";
  Hashtbl.iter (fun var term ->
    Printf.printf "  %s -> %s\n" var (string_of_term term)
  ) sigma

(* Main function for running tests *)
let () =
  Printf.printf "Testing Term Unification Implementation\n";
  Printf.printf "=====================================\n\n";

  (* Test 1: Signature validation *)
  let valid_sig = [("f", 2); ("g", 1); ("h", 0)] in
  let invalid_sig1 = [("f", 2); ("f", 1)] in  (* Repeated symbol *)
  let invalid_sig2 = [("f", 2); ("g", -1)] in  (* Negative arity *)
  
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
  Printf.printf "  term1 = %s\n" (string_of_term term1);
  Printf.printf "  term2 = %s\n" (string_of_term term2);
  Printf.printf "  invalid_term = %s\n" (string_of_term invalid_term);
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
  let sigma = empty_subst() in
  Hashtbl.add sigma "x" (Node(("h", 0), [||]));
  Hashtbl.add sigma "y" (V "z");
  
  Printf.printf "  Original term1: %s\n" (string_of_term term1);
  Printf.printf "  Substitution:\n";
  Printf.printf "    x -> h\n";
  Printf.printf "    y -> z\n";
  let term1' = subst term1 sigma in
  Printf.printf "  After substitution: %s\n" (string_of_term term1');
  Printf.printf "\n";

  (* Test 5: Substitution composition *)
  Printf.printf "Test 5: Substitution Composition\n";
  let sigma1 = empty_subst() in
  Hashtbl.add sigma1 "x" (V "y");
  Hashtbl.add sigma1 "z" (Node(("h", 0), [||]));
  
  let sigma2 = empty_subst() in
  Hashtbl.add sigma2 "y" (Node(("g", 1), [|V "w"|]));
  
  Printf.printf "  sigma1:\n";
  Printf.printf "    x -> y\n";
  Printf.printf "    z -> h\n";
  Printf.printf "  sigma2:\n";
  Printf.printf "    y -> g(w)\n";
  
  let composed = compose sigma1 sigma2 in
  Printf.printf "  Composed substitution (sigma1 ∘ sigma2):\n";
  Hashtbl.iter (fun var term ->
    Printf.printf "    %s -> %s\n" var (string_of_term term)
  ) composed;
  Printf.printf "\n";

  (* Test 6: Simple unification *)
  Printf.printf "Test 6: Simple Unification\n";
  let t1 = Node(("f", 2), [|V "x"; V "y"|]) in
  let t2 = Node(("f", 2), [|V "z"; Node(("h", 0), [||])|]) in
  
  Printf.printf "  t1 = %s\n" (string_of_term t1);
  Printf.printf "  t2 = %s\n" (string_of_term t2);
  
  try
    let unifier = mgu t1 t2 in
    Printf.printf "  Unifier:\n";
    Hashtbl.iter (fun var term ->
      Printf.printf "    %s -> %s\n" var (string_of_term term)
    ) unifier;
  with NOT_UNIFIABLE ->
    Printf.printf "  Terms are not unifiable!\n";
  Printf.printf "\n";

  (* Test 7: Occurs check unification failure *)
  Printf.printf "Test 7: Occurs Check Unification\n";
  let t3 = V "x" in
  let t4 = Node(("f", 1), [|V "x"|]) in
  
  Printf.printf "  t3 = %s\n" (string_of_term t3);
  Printf.printf "  t4 = %s\n" (string_of_term t4);
  
  try
    let unifier = mgu t3 t4 in
    Printf.printf "  Unifier:\n";
    Hashtbl.iter (fun var term ->
      Printf.printf "    %s -> %s\n" var (string_of_term term)
    ) unifier;
  with NOT_UNIFIABLE ->
    Printf.printf "  Terms are not unifiable! (Occurs check failure)\n";
  Printf.printf "\n";

  (* Test 8: Complex unification *)
  Printf.printf "Test 8: Complex Unification\n";
  let t5 = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    V "y"
  |]) in
  let t6 = Node(("f", 2), [|
    V "z";
    Node(("g", 1), [|V "w"|])
  |]) in
  
  Printf.printf "  t5 = %s\n" (string_of_term t5);
  Printf.printf "  t6 = %s\n" (string_of_term t6);
  
  try
    let unifier = mgu t5 t6 in
    Printf.printf "  Unifier:\n";
    Hashtbl.iter (fun var term ->
      Printf.printf "    %s -> %s\n" var (string_of_term term)
    ) unifier;
  with NOT_UNIFIABLE ->
    Printf.printf "  Terms are not unifiable!\n";
  Printf.printf "\n";

  (* Test 9: Edit function *)
  Printf.printf "Test 9: Edit Function\n";
  let original = Node(("f", 2), [|
    Node(("g", 1), [|V "x"|]);
    Node(("h", 0), [||])
  |]) in
  let replacement = V "z" in
  let position = [0] in  (* Replace the first argument of f *)
  
  Printf.printf "  Original term: %s\n" (string_of_term original);
  Printf.printf "  Replacement: %s\n" (string_of_term replacement);
  Printf.printf "  Position: [0]\n";
  
  let edited = edit original position replacement in
  Printf.printf "  After edit: %s\n" (string_of_term edited);
  Printf.printf "\n";

  (* Test 10: In-place substitution *)
  Printf.printf "Test 10: In-place Substitution\n";
  let t = Node(("f", 2), [|V "x"; V "y"|]) in
  let s = empty_subst() in
  Hashtbl.add s "x" (Node(("h", 0), [||]));
  Hashtbl.add s "y" (V "z");
  
  Printf.printf "  Original term: %s\n" (string_of_term t);
  Printf.printf "  Substitution:\n";
  Printf.printf "    x -> h\n";
  Printf.printf "    y -> z\n";
  
  let result = subst_in_place t s in
  Printf.printf "  After in-place substitution: %s\n" (string_of_term result);
  Printf.printf "  Original term (should be modified): %s\n" (string_of_term t);