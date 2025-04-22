(* Assignment 5: Terms, Substitution, Unification *)

type variable = string
type symbol = string * int  


type term = V of variable | Node of symbol * (term array)

(* Exception for unification failure *)
exception NOT_UNIFIABLE

(* 1. Check if a signature is valid (no repeated symbols and non-negative arities) *)
let check_sig signatures =
    let rec check seen = function
      | [] -> true  
      | (sign, arity) :: remain ->  if arity < 0 then 
            (* Negative arity is invalid *)
            false 
          else if List.exists (fun (n, _) -> n = sign) seen then
            (* Symbol already seen - duplicate *)
            false
          else 
            (* This signature is valid so far, continue checking *)
            check ((sign, arity) :: seen) remain
    in
    check [] signatures

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