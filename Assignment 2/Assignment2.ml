
(* Aditya Anand: 2023CS50284 *)

(* -----------------------------------------------CODE------------------------------------------------------------- *) 

(* ------------------------------ EXCEPTIONS RAISED ------------------------------ *)
exception DimensionError
exception DivisionError 
  
  
(* ------------------------------ VECTOR MODULE ------------------------------ *)

     
module Vectors = struct

  type vector = float list 
  
  let dim v =
    if v = [] then 
      raise DimensionError
    else
      let rec get_dim num dim_list = match dim_list with 
          [] -> num
        | _ :: rest -> get_dim (num + 1) rest
      in
      get_dim 0 v


  let is_zero v =
    if v = [] then 
      raise DimensionError
    else 
      let rec check_zero z_list = match z_list with
          [] -> true 
        | x :: rest -> if ( x <= 0.000001 && x >= -0.000001) then check_zero rest else false 
      in
      check_zero v 
        
  
  let scale c v =
    if v = [] then
      raise DimensionError
    else 
      let rec scalar_mult sc_list v = match v with
          [] -> List.rev sc_list
        | x :: rest -> scalar_mult ((c *. x) :: sc_list) rest
      in 
      scalar_mult [] v
  
  let addv v1 v2 =
    match v1, v2 with
      [], [] -> raise DimensionError
    | _ -> let rec add_func add_list v1 v2 = match v1, v2 with
          [], [] -> List.rev add_list
        | [], _ | _, [] -> raise DimensionError 
        | a :: u, b :: v -> add_func ((a +. b) :: add_list) u v
        in
        add_func [] v1 v2
 
  
  let dot_prod v1 v2 =
    match v1, v2 with
      [], [] -> raise DimensionError
    | _ -> let rec dot_func result v1 v2 = match v1, v2 with
          [], [] -> result
        | [], _ | _, [] -> raise DimensionError
        | a :: u, b :: v -> dot_func (result +. (a *. b)) u v
        in
        dot_func 0.0 v1 v2
          
  let inv v = scale (-1.) v 
  
  let length v =
    if v = [] then
      raise DimensionError
    else
      let rec sum_func square_sum x = match x with
          [] -> sqrt square_sum
        | a :: rest -> sum_func (square_sum +. (a *. a)) rest
      in
      sum_func 0.0 v

  let angle v1 v2 =
    if dim v1 == dim v2 then 
      let len1 = length v1 in
      let len2 = length v2 in
      if (len1 = 0.0 || len2 = 0.0) 
      then raise DivisionError 
      else 
        let dot = dot_prod v1 v2 in
        let cosine = dot /. (len1 *. len2) in 
        let cosine = if cosine < -1.0 then -1.0 else if cosine > 1.0 then 1.0 else cosine in
        let answer = acos cosine in
        if answer < 1e-7 then 0.0 else answer 
             
    else raise DimensionError
        
        
  let unit n j =
    if n = 0 then
      raise DimensionError
    else if j < 1 || j > n then
      raise DimensionError
    else
      let rec make_one i list = match i with
          0 -> list
        | _ -> 
            if i = j then 
              make_one (i - 1) (1.0 :: list)  
            else 
              make_one (i - 1) (0.0 :: list)  
      in
      make_one n []
        
  let zero_vector n x =
    if n < 1 then 
      raise DimensionError
    else 
      let rec create_list my_list count = match count with
          0 -> my_list 
        | _ -> create_list (x :: my_list) (count - 1)
      in
      create_list [] n
  
end


(* --------------------------- TYPES --------------------------- *)
type types = Bool 
           | Scalar 
           | Vector of int 
                           

(* --------------------------- VALUES --------------------------- *)

type values = B of bool | S of float | V of float list 
                  
                                                       
(* --------------------------- EXPRESSIONS --------------------------- *)
type expr =  
    T | F   (* Boolean constants *)
  | ConstS of float    (* Scalar constants *)
  | ConstV of float list    (* Vector constants *)
  | Add of expr * expr   (* overloaded — disjunction of two booleans or sum of  two scalars or sum of two vectors of the same dimension *)
  | Inv of expr     (* overloaded — negation of a boolean or additive inverse of  a scalar or additive inverse of a vector *)
  | ScalProd of expr * expr   (* overloaded — conjunction of two booleans or product of a scalar with another scalar or product of a scalar and a vector *)
  | DotProd of expr * expr  (* dot product of two vectors of the same dimension *)
  | Mag of expr   (* overloaded: absolute value of a scalar or magnitude of a vector *)
  | Angle of expr * expr  (* in radians, the angle between two vectors *)
  | IsZero of expr (* overloaded: checks if a boolean expression evaluates to F,  or if a given scalar is within epsilon of 0.0 or is the vector close — within epsilon on each coordinate —  to the zero vector *)
  | Cond of expr * expr * expr  (* "if_then_else" --  if the first expr evaluates to T then evaluate the second expr, else the third expr *)
;; 

(* WRONG EXCEPTION *)
exception Wrong of expr
    
    
let vector_dim v = List.length v
    
let same_dim x y =  
  if x = y then true  
  else false 

let check_vector v =
  if vector_dim v = 0 then false else true

(* --------------------------------------- TYPE CHECK --------------------------------------- *)
let rec type_of e = match e with
    T -> Bool
  | F -> Bool
  | ConstS _ -> Scalar 
  | ConstV v -> 
      if check_vector v then
        Vector (vector_dim v)
      else
        raise (Wrong (ConstV v)) 
  | Add (e1, e2) ->  
      (let first = type_of e1 in  
       let second = type_of e2 in  
       match first, second with  
       | Bool, Bool -> Bool  
       | Scalar, Scalar -> Scalar  
       | Vector a, Vector b when same_dim a b -> Vector a  
       | _ -> raise (Wrong (Add (e1, e2))))

  | Inv e1 -> type_of e1

  | ScalProd (e1, e2) ->  
      (let first = type_of e1 in  
       let second = type_of e2 in  
       match first, second with  
       | Bool, Bool -> Bool
       | Scalar, Scalar -> Scalar
       | Scalar, Vector v -> Vector v
       | Vector v, Scalar -> Vector v
       | _ -> raise (Wrong (ScalProd (e1, e2))))

  | DotProd (e1, e2) -> 
      (let first = type_of e1 in  
       let second = type_of e2 in 
       match first, second with
       | Vector a, Vector b when same_dim a b -> Scalar
       | _ -> raise (Wrong (DotProd (e1, e2))))
    
  | Mag e1 -> 
      (let check = type_of e1 in
       match check with
       | Scalar -> Scalar
       | Vector _ -> Scalar
       | _ -> raise (Wrong (Mag e1)))
    
  | Angle (e1, e2) -> 
      (let first = type_of e1 in  
       let second = type_of e2 in 
       match first, second with
       | Vector a, Vector b when same_dim a b -> Scalar
       | _ -> raise (Wrong (Angle (e1, e2))))
    
  | IsZero _ -> Bool 
    
  | Cond (e1, e2, e3) -> 
      (if ((type_of e1 = Bool) && (type_of e2 = type_of e3)) then type_of e3
       else raise (Wrong (Cond (e1, e2, e3))))


(* --------------------------------------- EVAL FUNCTIONS --------------------------------------- *)
let rec eval e = match e with
    T -> B true
  | F -> B false
  | ConstS x -> S x
  | ConstV [] -> raise (Wrong e)
  | ConstV v -> V v
                  
  | Add (e1, e2) -> 
      (if type_of e1 = type_of e2 then
         match eval e1, eval e2 with
         | B b1, B b2 -> B (b1 || b2)
         | S s1, S s2 -> S (s1 +. s2)
         | V v1, V v2 -> V (Vectors.addv v1 v2)
         | _ -> raise (Wrong e)
       else raise (Wrong e))
      
  | Inv e1 -> 
      (match eval e1 with
       | B b -> B (not b)
       | S s -> S (-.s)
       | V v -> V (Vectors.inv v)) 
      
  | ScalProd (e1, e2) -> 
      (match eval e1, eval e2 with 
       | S s, V v -> V (Vectors.scale s v)
       | V v, S s -> V (Vectors.scale s v)
       | B b1, B b2 -> B (b1 && b2)
       | S s1, S s2 -> S (s1 *. s2)
       | _ -> raise (Wrong e)) 
    
  | DotProd (e1, e2) -> 
      (if type_of e1 = type_of e2 then
         match eval e1, eval e2 with
         | V v1, V v2 -> S (Vectors.dot_prod v1 v2)
         | _ -> raise (Wrong e)
       else raise (Wrong e))
    
  | Mag e1 -> 
      (if type_of e1 = Bool then
         raise (Wrong e) 
       else 
         match eval e1 with 
           S s -> if s >= 0.0 then S s
             else S (-.s)
         | V v -> S (Vectors.length v)
         | _ -> raise (Wrong e))
    
  | Angle (e1, e2) -> 
      (if type_of e1 = type_of e2 then 
         if (type_of e1 = Scalar || type_of e1 = Bool) then raise (Wrong e) else
           match eval e1, eval e2 with
           | V v1, V v2 -> 
               if Vectors.length v1 = 0.0 || Vectors.length v2 = 0.0 then 
                 raise (Wrong e) 
               else 
                 S (Vectors.angle v1 v2)
           | _ -> raise (Wrong e)
       else raise (Wrong e))

  | IsZero e1 -> 
      (match eval e1 with
       | B b -> B (not b)
       | S s -> B (s <= 0.000001 && s >= -0.000001)
       | V v -> B (Vectors.is_zero v)) 
    
  | Cond (e1, e2, e3) ->
      (if type_of e2 = type_of e3 then
         match eval e1 with
         | B true -> eval e2
         | B false -> eval e3
         | _ -> raise (Wrong e)
       else raise (Wrong e))
      
      