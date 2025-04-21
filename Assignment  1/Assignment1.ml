(* Aditya Anand: 2023CS50284 *)

(* ========================================CODE============================================ *)
exception DimensionError
exception DivisionError

module Vectors = struct

  type vector = float list 
  
  let create n x =
    if n < 1 then 
      raise DimensionError
    else 
      let rec create_list my_list count = match count with
          0 -> my_list 
        | _ -> create_list (x :: my_list) (count - 1)
      in
      create_list [] n 
  
  let dim v =
    if v = [] then 
      raise DimensionError
    else
      let rec get_dim num my_list = match my_list with 
          [] -> num
        | _ :: rest -> get_dim (num + 1) rest
      in
      get_dim 0 v


  let is_zero v =
    if v = [] then 
      raise DimensionError
    else
      let rec check_zero list = match list with
          [] -> true 
        | 0.0 :: rest -> check_zero rest 
        | _ -> false 
      in
      check_zero v 
        
  let unit n j =
    if n = 0 then
      raise DimensionError
    else if j < 1 || j > n then
      raise DimensionError
    else
      let rec make_one i acc = match i with
          0 -> acc
        | _ -> 
            if i = j then 
              make_one (i - 1) (1.0 :: acc)  
            else 
              make_one (i - 1) (0.0 :: acc)  
      in
      make_one n []
  
  let scale c v = 
    if v = [] then
      raise DimensionError
    else 
      let rec scalar_mult c v = match v with
          [] -> []
        | x :: rest -> (c *. x) :: scalar_mult c rest
      in scalar_mult c v
  
  let rec addv (v1: vector) (v2: vector) = match v1, v2 with
      [], [] -> [] 
    | [], _ | _, [] -> raise DimensionError
    | a :: u, b :: v -> (a +. b) :: addv u v 
 
  
  let rec dot_prod v1 v2 =  match (v1, v2) with
      [], [] -> 0.0
    | [], _ | _, [] -> raise DimensionError
    | a :: u, b :: v -> (a *. b) +. dot_prod u v
  
  
  let rec inv v = scale (-1.) v  
  
  let length v =
    if v = [] then
      raise DimensionError
    else
      let rec square_sum x = match x with
          [] -> 0.0
        | a :: rest -> (a *. a) +. square_sum rest
      in
      sqrt (square_sum v)

  
  let angle v1 v2 =
    let rec get_angle v1 v2 dot len1 len2 = match v1, v2 with
        [], [] -> 
          if len1 = 0.0 || len2 = 0.0 then
            raise DivisionError  
          else
            let cosine = dot /. (sqrt len1 *. sqrt len2) in
            let cosine = if cosine < -1.0 then -1.0 else if cosine > 1.0 then 1.0 else cosine in
            acos cosine  
      | x1 :: xs1, x2 :: xs2 -> 
          let new_dot = dot +. (x1 *. x2) in
          let new_len1 = len1 +. (x1 *. x1) in
          let new_len2 = len2 +. (x2 *. x2) in
          get_angle xs1 xs2 new_dot new_len1 new_len2 
      | _ -> raise DimensionError 
    in
    get_angle v1 v2 0.0 0.0 0.0
  
end

(* ==================================TESTCASES===================================== *)

open Printf;;
(*
  let () =
  
  (* -------------------------------- CREATE TESTS -------------------------------*)
    printf "Testing Create Function...\n";

  (* Test Case 1: Create a vector with 5 elements, all 2.0 *) 
    let n1 = 5 in
    let x1 = 2.0 in 
    let result1 = Vectors.create n1 x1 in
    Printf.printf "Vector with %d elements, with all elements %0.2f:\n" n1 x1;
    List.iter (Printf.printf "%0.2f ") result1;
    Printf.printf "\n";

  (* Test Case 2: Create a vector with 1 element, all -4.7 *)
    let n2 = 1 in
    let x2 = -4.7 in
    let result2 = Vectors.create n2 x2 in
    Printf.printf "Vector with %d elements, with all elements %0.2f:\n" n2 x2;
    List.iter (Printf.printf "%0.2f ") result2;
    Printf.printf "\n";

  (* Test Case 3: Create a vector with 25 elements, all 16.3 *)
    let n3 = 10 in
    let x3 = 16.3 in
    let result3 = Vectors.create n3 x3 in
    Printf.printf "Vector with %d elements, with all elements %0.2f:\n" n3 x3;
    List.iter (Printf.printf "%0.2f ") result3;
    Printf.printf "\n";

  (* Test Case 4: Create a vector with 0 elements *)
    let n4 = 0 in
    let x4 = 10.0 in
    (try
       let result4 = Vectors.create n4 x4 in
       Printf.printf "Vector with %d elements, with all elements %0.2f:\n" n4 x4;
       List.iter (Printf.printf "%0.2f ") result4;
       Printf.printf "\n"
     with
     | DimensionError -> Printf.printf "Caught DimensionError for n = %d\n" n4);

    let n5 = 8 in
    let x5 = -3.14 in
    let result5 = Vectors.create n5 x5 in
    Printf.printf "Vector with %d elements, with all elements %0.2f:\n" n5 x5;
    List.iter (Printf.printf "%0.2f ") result5;
    Printf.printf "\n";

    Printf.printf "Testing Create Ends\n"; 
  
  (* -------------------------------- DIM TESTS -------------------------------*)
  
    Printf.printf "Testing Dim Function...\n";

  (* Test Case 1: Non-empty vector with multiple elements *)
    let v1 = [6.1; 3.8; 4.2; 19.4; 294.24; 18.3; 1932.4] in
    let dim1 = Vectors.dim v1 in
    Printf.printf "Dimension of vector [6.1; 3.8; 4.2; 19.4; 294.24; 18.3; 1932.4]: %d\n" dim1;

  (* Test Case 2: Vector with a single element *)
    let v2 = [-0.0] in
    let dim2 = Vectors.dim v2 in
    Printf.printf "Dimension of vector [-0.0]: %d\n" dim2; 

  (* Test Case 3: Vector with a multiple random elements *)
    let v3 = [-1.0; 2.5; -3.5; 4.2; 0.0; 13.54; -192.34; 1029.39; -23.10; -1.0; 2.5; -3.5; 4.2; 0.0; 13.54; -192.34; 1029.39; -23.10; -1.0; 2.5; -3.5; 4.2; 0.0; 13.54; -192.34; 1029.39; -23.10; -1.0; 2.5; -3.5; 4.2; 0.0; 13.54; -192.34; 1029.39; -23.10] in 
    let dim3 = Vectors.dim v3 in
    Printf.printf "Dimension of vector with 36 mixed value elements: %d\n" dim3;  

  (* Test Case 4: Large vector *)
    let v4 = List.init 15 (fun _ -> -1.0) in
    let dim4 = Vectors.dim v4 in
    Printf.printf "Dimension of vector with 60 elements: %d\n" dim4;

  
  (* -------------------------------- IS_ZERO TESTS -------------------------------*)
  
    Printf.printf "Testing is_zero Function...\n";
  
    let v1 = [0.0; 0.0; -0.0] in
    Printf.printf "Test Case 1 - All Zeros: %b\n" (Vectors.is_zero v1);
  (* Expected output: true *)

    let v2 = [0.0; 1.2; 0.0; -18.4; 19.0; 13.9; -12.0] in
    Printf.printf "Test Case 2 - Non-zero elements: %b\n" (Vectors.is_zero v2);
  (* Expected output: false *)
  
    let v3 = [] in
    (try
       let _ = Vectors.is_zero v3 in
       Printf.printf "Test Case 3 - Empty vector: This should raise an error.\n"
     with
     | DimensionError -> Printf.printf "Caught DimensionError for empty vector.\n");
   (* Expected output: Caught DimensionError for empty vector. *)

    let v4 = [0.0] in
    Printf.printf "Test Case 4 - Single zero: %b\n" (Vectors.is_zero v4);
  (* Expected output: true *)
  
    let v5 = [0.0;0.0; 0.0;0.0; 0.0;0.0; 0.0;0.0; 0.0;0.0; 0.0;0.0; 0.0;0.0; 0.0;0.0; 0.0;0.0; 0.0;0.0; 1.0; 0.0; 0.0] in
    Printf.printf "Test Case 5 - Mixed zeros and non-zeros: %b\n" (Vectors.is_zero v5);
  (* Expected output: false *) 
  
    Printf.printf "Testing is_zero Ends\n";
   
(* -------------------------------- UNIT TESTS -------------------------------*)

    Printf.printf "Testing unit function...\n";

  (* Test Case 1: Valid unit vector of size 5, j = 3 *)
    let v1 = Vectors.unit 5 3 in
    Printf.printf "Test Case 1 - Unit vector (n = 5, j = 3): [%s]\n"
      (String.concat "; " (List.map string_of_float v1));

  (* Test Case 2: Invalid j (out of range, j = 6 for n = 5) *) 

  (* Test Case 3: Unit vector of size 1, j = 1 *)
    let v3 = Vectors.unit 1 1 in
    Printf.printf "Test Case 3 - Unit vector (n = 1, j = 1): [%s]\n"
      (String.concat "; " (List.map string_of_float v3));
  

  (* Test Case 5: Valid unit vector of size 8, j = 8 *)
    let v5 = Vectors.unit 4 4 in
    Printf.printf "Test Case 4 - Unit vector (n = 4, j = 4): [%s]\n"
      (String.concat "; " (List.map string_of_float v5));
  
    Printf.printf "Testing unit Ends\n";
  
  
(* -------------------------------- SCALE TESTS -------------------------------*)

    Printf.printf "Testing scale function...\n";
  
  (* Test Case 1: Scaling by 0.1 *)
    let v1 = [15.0; -24.0; 33.0] in
    let result1 = Vectors.scale 1. v1 in
    Printf.printf "Test Case 1 - Scaling by 1.: %b\n"
      (result1 = [15.0; -24.0; 33.0]);

  (* Test Case 2: Scaling by zero *)
    let v2 = [1.0; -2.0; 3.0] in
    let result2 = Vectors.scale 0.0 v2 in
    Printf.printf "Test Case 2 - Scaling by zero: %b\n"
      (result2 = [0.0; -0.0; 0.0]);

  (* Test Case 6: Large vector *)
    let v3 = List.init 12 (fun i -> float_of_int i) in
    let result3 = Vectors.scale 0.5 v3 in
    Printf.printf "Test Case 3 - Large vector: %b\n"
      (result3 = List.init 12 (fun i -> (float_of_int i) *. 0.5)); (* Expected output: true *)

  (* Test Case 4: Scaling with negative scalar *)
    let v4 = [1.0; -2.0; 3.0; -4.0; 5.0] in
    let result4 = Vectors.scale (-2.0) v4 in
    Printf.printf "Test Case 4 - Scaling with negative scalar: %b\n"
      (result4 = [-2.0; 4.0; -6.0; 8.0; -10.0]);

  (* Test Case 5: Empty vector (should raise DimensionError) *)
    try
      let _ = Vectors.scale 1.0 [] in
      Printf.printf "Test Case 5 - Empty vector: %b\n" false
    with DimensionError ->
      Printf.printf "Test Case 5 - Empty vector raised DimensionError as expected: %b\n" true;
    
      Printf.printf "Testing scale Ends\n";
  
(* -------------------------------- ADDV TESTS -------------------------------*)

      Printf.printf "Testing addv function...\n";

  (* Test Case 1: Basic vector addition with positive numbers *)
      let v1 = [5.0; 3.0; 3.0] in
      let v2 = [4.0; 5.0; 16.0] in
      let result1 = Vectors.addv v1 v2 in
      Printf.printf "Test Case 1 - Basic addition: %b\n"
        (result1 = [9.0; 8.0; 19.0]); (* Expected output: true *)

  (* Test Case 2: Addition with negative numbers *)
      let v3 = [1.0; -2.0; 3.0] in
      let v4 = [-1.0; 2.0; -3.0] in
      let result2 = Vectors.addv v3 v4 in
      Printf.printf "Test Case 2 - Addition with negatives: %b\n"
        (result2 = [0.0; 0.0; 0.0]); (* Expected output: true *)
    
  (* Test Case 3: Mismatched dimensions (should raise DimensionError) *)
      let v5 = [5.0; 3.0; 2.0] in
      let v6 = [4.0; 5.0; 16.0] in
      let result3 = Vectors.addv v5 v6 in
      Printf.printf "Test Case 3 - Addition with large number: %b\n"
        (result3 = [9.0; 8.0; 18.0]); (* Expected output: true *)
                                   
                                    

  (* Test Case 5: Single element vectors *)
      let v9 = [3.0] in
      let v10 = [2.0] in
      let result5 = Vectors.addv v9 v10 in
      Printf.printf "Test Case 4 - Single element vectors: %b\n"
        (result5 = [5.0]); (* Expected output: true *)

      Printf.printf "Testing addv Ends\n";
  
(* -------------------------------- DOT_PROD TESTS -------------------------------*)

      Printf.printf "Testing dot_prod function...\n";

  (* Test Case 1: Basic dot product of small vectors *)
      let v1 = [1.0; 2.0; 3.0] in
      let v2 = [4.0; 5.0; 6.0] in
      let result1 = Vectors.dot_prod v1 v2 in
      Printf.printf "Test Case 1 - Basic dot product: %b\n"
        (result1 = 32.0); (* Expected: 1*4 + 2*5 + 3*6 = 32 *)

  (* Test Case 2: Dot product with negative values *)
      let v3 = [1.0; -2.0; 3.0] in
      let v4 = [-1.0; 2.0; -3.0] in
      let result2 = Vectors.dot_prod v3 v4 in
      Printf.printf "Test Case 2 - Dot product with negatives: %b\n"
        (result2 = -14.0); (* Expected: 1*(-1) + (-2)*2 + 3*(-3) = -14 *)

  (* Test Case 3: Dot product of two single-element vectors *)
      let v5 = [3.14] in
      let v6 = [2.0] in
      let result3 = Vectors.dot_prod v5 v6 in
      Printf.printf "Test Case 3 - Single-element dot product: %b\n"
        (result3 = 6.28); (* Expected: 3.14 * 2 = 6.28 *)

  (* Test Case 4: Dot product with a vector containing zeros *)
      let v5 = [0.0; 2.0; 4.0] in
      let v6 = [1.0; 0.0; 3.0] in
      let result4 = Vectors.dot_prod v5 v6 in
      Printf.printf "Test Case 4 - Dot product with zeros: %b\n"
        (result4 = 12.0); (* Expected: 0*1 + 2*0 + 4*3 = 12 *) 
                       
                       
      Printf.printf "Testing inv function...\n";

(* Test Case 1: Inverting a basic vector *)
      let v1 = [1.0; -2.0; 3.0] in
      let result1 = Vectors.inv v1 in
      Printf.printf "Test Case 1 - Basic inversion: %b\n"
        (result1 = [-1.0; 2.0; -3.0]); (* Expected: [-1.0, 2.0, -3.0] *)

(* Test Case 2: Inverting a vector with a single element *)
      let v2 = [5.0] in
      let result2 = Vectors.inv v2 in
      Printf.printf "Test Case 2 - Single element: %b\n"
        (result2 = [-5.0]); (* Expected: [-5.0] *)
  
    
      Printf.printf "Testing length function...\n";
    (* Test Case 1: Vector with positive values *)
      let v1 = [3.0; 4.0] in
      let result1 = Vectors.length v1 in
      Printf.printf "Test Case 1 - Positive values: %b\n"
        (result1 = 5.0); (* Expected: sqrt(3^2 + 4^2) = sqrt(9 + 16) = 5.0 *)

(* Test Case 2: Vector with negative values *)
      let v2 = [-3.0; -4.0] in
      let result2 = Vectors.length v2 in
      Printf.printf "Test Case 2 - Negative values: %b\n"
        (result2 = 5.0); (* Expected: sqrt((-3)^2 + (-4)^2) = sqrt(9 + 16) = 5.0 *)

(* Test Case 3: Vector with a single element *)
      let v3 = [7.0] in
      let result3 = Vectors.length v3 in
      Printf.printf "Test Case 3 - Single element: %b\n"
        (result3 = 7.0); (* Expected: sqrt(7^2) = 7.0 *)
                       
                       (* Test Case 4: Vector with mixed positive and zero values *)
      let v4 = [0.0; 6.0; 8.0] in
      let result4 = Vectors.length v4 in
      Printf.printf "Test Case 4 - Mixed positive and zero values: %b\n"
        (result4 = 10.0); (* Expected: sqrt(0^2 + 6^2 + 8^2) = sqrt(0 + 36 + 64) = 10.0 *)
                        
      Printf.printf "Testing angle function...\n";

(* Test Case 1: Angle between two orthogonal vectors *)
      let v1 = [1.0; 0.0] in
      let v2 = [0.0; 1.0] in
      let result1 = Vectors.angle v1 v2 in
      Printf.printf "Test Case 1 - Orthogonal vectors: %b\n"
        (result1 = (Float.pi /. 2.0)); (* Expected: π/2 radians (90 degrees) *)

(* Test Case 2: Angle between two parallel vectors *)
      let v3 = [1.0; 2.0; 3.0] in
      let v4 = [2.0; 4.0; 6.0] in
      let result2 = Vectors.angle v3 v4 in
      Printf.printf "Test Case 2 - Parallel vectors: %b\n"
        (result2 = 0.0); (* Expected: 0 radians (0 degrees) *)

(* Test Case 3: Angle when one vector is zero *)
      let v5 = [0.0; 0.0; 0.0] in
      let v6 = [1.0; 2.0; 3.0] in
      let result3 = Vectors.angle v5 v6 in
      Printf.printf "Test Case 3 - Zero vector: %b\n"
        (result3 = 0.0); (* Expected: 0 radians since angle is undefined with zero vector *)

(* Test Case 4: Angle between two arbitrary vectors *)
      let v7 = [1.0; 0.0; 0.0] in
      let v8 = [1.0; 1.0; 0.0] in
      let result4 = Vectors.angle v7 v8 in
      Printf.printf "Test Case 4 - Arbitrary vectors: %b\n"
        (abs_float (result4 -. (Float.pi /. 4.0)) < 0.0001); (* Expected: π/4 radians (45 degrees) *)

      Printf.printf "Testing angle Ends\n";

                          
                       
   *)
   
let test () =
  (* Test create *)
  let v1 = Vectors.create 3 2.5 in
  assert (Vectors.dim v1 = 3);
  assert (v1 = [2.5; 2.5; 2.5]);
  
  (* Test is_zero *)
  let zero_vec = Vectors.create 3 0.0 in
  let non_zero_vec = Vectors.create 3 1.0 in
  assert (Vectors.is_zero zero_vec);
  assert (not (Vectors.is_zero non_zero_vec));
  
  (* Test unit *)
  let u = Vectors.unit 4 2 in
  assert (u = [0.0; 1.0; 0.0; 0.0]);
  
  (* Test scale *)
  let scaled = Vectors.scale 2.0 [1.0; 2.0; 3.0] in
  assert (scaled = [2.0; 4.0; 6.0]);
  
  (* Test addv *)
  let sum = Vectors.addv [1.0; 2.0; 3.0] [4.0; 5.0; 6.0] in
  assert (sum = [5.0; 7.0; 9.0]);
  
  (* Test dot_prod *)
  let dot = Vectors.dot_prod [1.0; 2.0; 3.0] [4.0; 5.0; 6.0] in
  assert (dot = 32.0);
  
  (* Test inv *)
  let inv_vec = Vectors.inv [1.0; -2.0; 3.0] in
  assert (inv_vec = [-1.0; 2.0; -3.0]);
  
  (* Test length *)
  let vec_len = Vectors.length [3.0; 4.0] in
  assert (abs_float (vec_len -. 5.0) < 1e-10);
  
  (* Test angle *)
  let vec1 = [1.0; 0.0] in
  let vec2 = [0.0; 1.0] in
  let ang = Vectors.angle vec1 vec2 in
  assert (abs_float (ang -. (Float.pi /. 2.0)) < 1e-6);
  
  print_endline "All tests passed!"




;;


(* -------------------------------------- PROOF -------------------------------------*)

(* 
1. Commutativity of Vector Addition:

Given: u + v = addv u v
dimension of vector u = dimension of vector v

To Prove: u + v = v + u

Proof: 

Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
u = [a], v = [b]            - Since dimension of u = dimension of v = 1
addv u v = [a +. b]         - By the Definition of addv     
[a +. b] = [b +. a]         - By the Commutativity of Float Addition
[b +. a] = addv v u         - By the Definition of addv

So, addv u v = addv v u
=> u + v = v + u for the Base Case

Induction Hypothesis: Suppose for n = k, u + v = v + u
i.e. addv u v = addv v u

Induction Step: Let n = k + 1
u = a :: u', v = b :: v'                       - Where u' and v' are vectors of dimension k
addv u v = (a +. b) :: add u' v'               - By the Definition of addv
(a +. b) :: add u' v' = (b +. a) :: add u' v'  - By the Commutativity of Float Addition
(a +. b) :: add u' v' = (b +. a) :: add v' u'  - By the Induction Hypothesis
(b +. a) :: add v' u' = addv v u               - By the Definition of addv
(a +. b) :: add u' v' = addv v u               - By above two equations
So, addv u v = addv v u
=> u + v = v + u

Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, u + v = v + u

Hence Proved.
*)

(* 
2. Associativity of Vector Addition:

Given: u + v = addv u v
dimension of vector u = dimension of vector v = dimension of vector w

To Prove: u + (v + w) = (u + v) + w

Proof: 

u + (v + w) = addv u (addv v w)
(u + v) + w = addv (addv u v) w


Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
u = [a], v = [b], w = [c]             - Since dimension of u = dimension of v = dimension of w = 1
addv u (addv v w) = addv u [b +. c]   - By the Definition of addv
addv u (addv v w) = [a +. (b +. c)]   - By the Definition of addv
[a +. (b +. c)] = [(a +. b) + c]      - By the Associativity of Float Addition
[(a +. b) +. c] = addv [a +. b] w     - By the Definition of addv
[(a +. b) +. c] = addv (addv u v) w   - By the Definition of addv

So, addv u (addv v w) = addv (addv u v) w
=> u + (v + w) = (u + v) + w  for the Base Case

Induction Hypothesis: Suppose for n = k, u + (v + w) = (u + v) + w
i.e. addv u (addv v w) = addv (addv u v) w

Induction Step: Let n = k + 1
u = a :: u', v = b :: v', w = c :: w'                              - Where u',w' and v' are vectors of dimension k
addv u (addv v w) = addv u ((b +. c) :: addv v' w')                - By the Definition of addv
addv u (addv v w) = (a +. (b +. c)) :: (addv u' (addv v' w'))      - By the Definition of addv
(a +. (b +. c)) :: (addv u' (addv v' w')) = ((a +. b) +. c)) :: (addv u' (addv v' w'))       - By the Associativity of Float Addition
((a +. b) +. c)) :: (addv u' (addv v' w')) = ((a +. b) +. c)) :: (addv (addv u' v') w')      - By the Induction Hypothesis
((a +. b) +. c)) :: (addv (addv u' v') w') = addv (addv u v) w                      - By the Definition of addv
              
So, addv u (addv v w) = addv (addv u v) w
=> u + (v + w) = (u + v) + w
            

Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, u + (v + w) = (u + v) + w

Hence Proved.

*)

(* 
3. Identity of Vector Addition:

Given: v + O = addv v O
dimension of vector v = dimension of vector O

To Prove: v + O = v

Proof: 

Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
v = [a], O = [0]            - Since dimension of v = dimension of O = 1
addv v O = [a + 0]          - By the Definition of addv     
[a + 0] = [a]               - By the Identity of Float Addition

So, addv v O = v
=> v + O = v  for the Base Case

Induction Hypothesis: Suppose for n = k, v + O = v
i.e. addv v O = v

Induction Step: Let n = k + 1

v = a :: v', O = 0 :: O'          - Where v' and O' are vectors of dimension k
addv v O = (a + 0) :: addv v' O'  - By the Definition of addv
(a + 0) :: addv v' O' = a :: v'   - By the Induction Hypothesis
a :: v' = v                       - By the Definition of addv
  
So, addv v O = v
=> v + O = v
                
Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, v + O = v

Hence Proved.
*)

(* 
4. Identity Scalar:

Given: 1.v = scale 1 v

To Prove: 1.v = v

Proof: 

Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
v = [a]               - Since dimension of v = 1
scale 1 v = [1 * a]   - By the Definition of scale     
[1 * a] = [a]         - By the Identity of Float Multiplication

So, scale 1 v = v
=> 1.v = v  for the Base Case

Induction Hypothesis: Suppose for n = k, scale 1 v = v
i.e. 1.v = v

Induction Step: Let n = k + 1

v = a :: v'                         - Where v' is a vector of dimension k
scale 1 v = (1 * a) :: scale 1 v'   - By the Definition of scale
(1 * a) :: scale 1 v' = a :: v'     - By the Induction Hypothesis
and By the Identity of Float Multiplication
a :: v' = v                         - Since v = a :: v'
  
So, scale 1 v = v
=> 1.v = v

Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, 1.v = v

Hence Proved.
*)

(* 
5. Annihilator Scalar:

Given: 0.v = scale 0 v

To Prove: 0.v = O

Proof: 

Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
v = a :: []                   - Since dimension of v = 1
scale 0 v = (0 * a)  :: []    - By the Definition of scale     
(0 * a)  :: [] = 0 :: []      - By the Annihilator Property of Float Multiplication
0 :: [] = O                   - By the Definition of O
          
So, scale 0 v = O
=> 0.v = O  for the Base Case

Induction Hypothesis: Suppose for n = k, scale 0 v = O
i.e. 0.v = O

Induction Step: Let n = k + 1

v = a :: v'                                 - Where v' is a vector of dimension k
scale 0 v = (0 * a) :: scale 0 v'           - By the Definition of scale
(0 * a) :: scale 0 v' = 0 :: scale 0 v'     - By the Annihilator Property of Float Multiplication
0 :: scale 0 v' = 0 :: O'                   - By the Induction Hypothesis and By the Definition of O
(Since O' = scale 0 v' where dimension of vector O' is k)
0 :: O' = O                                 - By the Definition of O

So, scale 0 v = O
=> 0.v = O

Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, 0.v = O

Hence Proved.
*)

(* 
6. Additive Inverse:

To Prove: v + (- v) = O

Proof: 

Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
v = a :: []                                    - Since dimension of v = 1
inv v = -a :: []                               - By the Definition of inv     
addv v (inv v) = (a +. -a) :: [] = 0 :: []     - By the Definition of addv and 
                                                 By the Additive Inverse Property of Float Addition
0 :: [] = O                                    - By the Definition of O where dimension of vector O is 1
So, v + (- v) = O for the Base Case

Induction Hypothesis: Suppose for n = k, v + (- v) = O
i.e. addv v (inv v) = O

Induction Step: Let n = k + 1

v = a :: v', inv v = -a :: inv v'           - Where v' and inv v' are vectors of dimension k
addv v (inv v) = (a +. -a) :: addv v' inv v' - By the Definition of addv
(a +. -a) :: addv v' inv v' = 0 :: addv v' inv v' - By the Additive Inverse Property of Float Addition
0 :: addv v' inv v' = 0 :: O'                - By the Induction Hypothesis and By the Definition of O
(Since O' = addv v' inv v' where dimension of vector O' is k)
0 :: O' = O                                  - By the Definition of O where dimension of vector O is k

So, addv v (inv v) = O
=> v + (- v) = O

Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, v + (- v) = O

Hence Proved.
*)

(* 
7. Scalar Product Combination:

Given: b.(c.v) = scale b (scale c v)
(b.c).v = scale (b *. c) v

To Prove: b.(c.v) = (b.c).v

Proof: 

Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
v = [a]                                     - Since dimension of v = 1
scale b (scale c v) = scale b [c *. a]      - By the Definition of scale     
scale b [c *. a] = [b *. (c *. a)]          - By the Definition of scale
scale (b *. c) v = [(b *. c) *. a]          - By the Definition of scale
[(b *. c) *. a] = [b *. (c *. a)]           - By the Associativity of Float Multiplication
scale (b *. c) v = scale b (scale c v)      - From the above equations

So, b.(c.v) = (b.c).v for the Base Case

Induction Hypothesis: Suppose for n = k, b.(c.v) = (b.c).v
i.e. scale b (scale c v) = scale (b *. c) v

Induction Step: Let n = k + 1

v = a :: v'                                                                 - Where v' is a vector of dimension k
scale b (scale c v) = scale b (c *. a :: scale c v')                        - By the Definition of scale
scale b (c *. a :: scale c v') = b *. (c *. a) :: scale b (scale c v')      - By the Definition of scale
b *. (c *. a) :: scale b (scale c v') = b *. (c *. a) :: scale (b *. c) v'  - By the Induction Hypothesis
b *. (c *. a) :: scale (b *. c) v' = (b *. c) *. a :: scale (b *. c) v'     - By the Associativity of Float Multiplication
(b *. c) *. a :: scale (b *. c) v' = (b *. c) *. a :: scale b (scale c v')  // Equation 1  - By the Definition of Scale

Now, scale (b *. c) v = (b *. c) *. a :: scale (b *. c) v'                  - From the Definition of Scale
(b *. c) *. a :: scale (b *. c) v' = (b *. c) *. a :: scale b (scale c v')  // Equation 2- From the Induction Hypothesis

From above equations, on comparing the LHS and RHS of Equation 1 and Equation 2, we get
scale (b *. c) v = scale b (scale c v) 

So, b.(c.v) = (b.c).v

Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, b.(c.v) = (b.c).v

Hence Proved.
*)

(* 
8. Scalar Sum Product Distribution:

Given: (b + c).v = scale (b + c) v
b.v + c.v = addv (scale b v) (scale c v)

To Prove: (b + c).v = b.v + c.v

Proof: 

Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
v = [a]                                     - Since dimension of v = 1
scale (b + c) v = [(b + c) *. a]            - By the Definition of scale
[(b + c) *. a] = [(b *. a) + (c *. a)]     (1) - By the Distributive Property of Float Multiplication

addv (scale b v) (scale c v) = addv [b *. a] [c *. a]  - By the Definition of scale
addv [b *. a] [c *. a] = [(b *. a) + (c *. a)]        (2) - By the Definition of addv

From (1) and (2), we get
scale (b + c) v = addv (scale b v) (scale c v)            

So, (b + c).v = b.v + c.v  for the Base Case

Induction Hypothesis: Suppose for n = k, (b + c).v = b.v + c.v
i.e. scale (b + c) v = addv (scale b v) (scale c v)

Induction Step: Let n = k + 1

v = a :: v'                                                            - Where v' is a vector of dimension k

Left Hand Side:

scale (b + c) v = [(b +. c) *. a] :: scale (b +. c) v'                        - By the Definition of scale
[(b +. c) *. a] :: scale (b +. c) v' = [(b *. a) +. (c *. a)] :: addv (scale b v') (scale c v')  - By the Induction Hypothesis and Distributive Property of Float Multiplication

Right Hand Side:

addv (scale b v) (scale c v) = addv (b *. a :: scale b v') (c *. a :: scale c v')         - By the Definition of scale
addv (b *. a :: scale b v') (c *. a :: scale c v') = [(b *. a) +. (c *. a)] :: addv (scale b v') (scale c v')  - By the Definition of addv

Now, Left Hand Side = Right Hand Side
So, scale (b + c) v = addv (scale b v) (scale c v)
                
Hence, (b + c).v = b.v + c.v

Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, (b + c).v = b.v + c.v

Hence Proved.
*)

(* 
9. Scalar Distribution over Vector Sums:

Given: b.(u + v) = b.u + b.v
b.u + b.v = addv (scale b u) (scale b v)
Dimension of vector u = Dimension of vector v

To Prove: b.(u + v) = b.u + b.v

Proof: 

Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
u = x :: [], v = y :: []               - Since dimension of u = dimension of v = 1
addv u v = (x +. y) :: []              - By the Definition of addv
scale b u = (b *. x) :: []             - By the Definition of scale
scale b v = (b *. y) :: []             - By the Definition of scale

Left Hand Side:
addv (scale b u) (scale b v) = (b *. x) +. (b *. y) :: []  - By the Definition of addv
b *. (x +. y) :: [] = (b *. x) +. (b *. y) :: []           - By the Distributive Property of Float Multiplication

Right Hand Side:
scale b (addv u v) = b *. (x +. y) :: []  - By the Definition of scale
b *. (x +. y) :: [] = (b *. x) +. (b *. y) :: []  - By the Distributive Property of Float Multiplication

Now, Left Hand Side = Right Hand Side
So, addv (scale b u) (scale b v) = scale b (addv u v)

Hence, b.(u + v) = b.u + b.v  for the Base Case 

Induction Hypothesis: Suppose for n = k, b.(u + v) = b.u + b.v
i.e. addv (scale b u) (scale b v) = scale b (addv u v)

Induction Step: Let n = k + 1

u = x :: u', v = y :: v'                       - Where u' and v' are vectors of dimension k
addv u v = (x +. y) :: addv u' v'              - By the Definition of addv
scale b u = (b *. x) :: scale b u'              - By the Definition of scale
scale b v = (b *. y) :: scale b v'              - By the Definition of scale

Left Hand Side:
  addv (scale b u) (scale b v) = (b *. x) +. (b *. y) :: addv (scale b u') (scale b v')  - By the Definition of addv
    (b *. x) +. (b *. y) :: addv (scale b u') (scale b v') = b *. (x +. y) :: addv (scale b u') (scale b v')  - By the Distributive Property of Float Multiplication
    b *. (x +. y) :: addv (scale b u') (scale b v') = b *. (x +. y) :: scale b (addv u' v')  - By the Induction Hypothesis

Right Hand Side:                                                                                                                  
 scale b (addv u v) = b *. (x +. y) :: scale b (addv u' v')  - By the Definition of scale
    b *. (x +. y) :: scale b (addv u' v') = b *. (x +. y) :: addv (scale b u') (scale b v')  - By the Induction Hypothesis

Now, Left Hand Side = Right Hand Side
So, addv (scale b u) (scale b v) = scale b (addv u v)

Hence, b.(u + v) = b.u + b.v

Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, b.(u + v) = b.u + b.v

Hence Proved.
*)

(*  -----------------------------EXTRA PROPERTIES------------------------------------------*)

(* 
1. Commutativity of Dot Product:

Given: u.v = dot_prod u v
dimension of u = dimension of v

To Prove: u.v = v.u
i.e. dot_prod u v = dot_prod v u

Proof: 

Proof by Induction on n, where n = Dimension of vector v

Base Case: n = 1
u = [a], v = [b]            - Since dimension of u = dimension of v = 1
dot_prod u v = (a *. b)     - By the Definition of dot_prod

Now, dot_prod v u = (b *. a)     - By the Definition of dot_prod
(a *. b) = (b *. a)             - By the Commutativity of Float Multiplication

So, dot_prod u v = dot_prod v u  for the Base Case

Induction Hypothesis: Suppose for n = k, dot_prod u v = dot_prod v u

Induction Step: Let n = k + 1

u = a :: u', v = b :: v'                       - Where u' and v' are vectors of dimension k

Left Hand Side:
dot_prod u v = (a *. b) +. dot_prod u' v'      - By the Definition of dot_prod

Right Hand Side:
dot_prod v u = (b *. a) +. dot_prod v' u'      - By the Definition of dot_prod
dot_prod v u = (b *. a) +. dot_prod u' v'      - By the Induction Hypothesis
dot_prod v u = (a *. b) +. dot_prod u' v'      - By the Commutativity of Float Multiplication

Now, Left Hand Side = Right Hand Side

So, dot_prod u v = dot_prod v u

Therefore, by the Principle of Mathematical Induction on dimension of vector v = n, u.v = v.u

Hence Proved.

*)

(* 
2. Relationship between Dot Product and Length of a Vector:

To Prove: length of a vector = square root (dot product of vector with itself)
i.e. length v = sqrt (dot_prod v v)

Proof: 

v = a :: v' where v' is a vector of dimension k

Left Hand Side:
length v = sqrt(square_sum v)   -By definition of length
lenght v= sqrt((a *. a) +. square_sum v')   -By definition of square_sum

Right Hand Side:
sqrt(dot_prod v v) = sqrt((a *. a) +. dot_prod v' v')   -By definition of dot_prod

To show these are equal, we need to prove that square_sum v' = dot_prod v' v' for any vector v'.

Claim: square_sum u = dot_prod u u for any vector u

Proof by Induction on n, where n = Dimension of vector u

Base Case: n = 1
u = [b]            - Since dimension of u = 1
square_sum u = (b *. b)     - By the Definition of square_sum
dot_prod u u = (b *. b)     - By the Definition of dot_prod

So, square_sum u = dot_prod u u  for the Base Case

Induction Hypothesis: Suppose for n = k, square_sum u = dot_prod u u

Induction Step: Let n = k + 1

u = b :: u'                       - Where u' is a vector of dimension k
square_sum u = (b *. b) +. square_sum u'      - By the Definition of square_sum
square_sum u = (b *. b) +. dot_prod u' u'     - By the Induction Hypothesis

Now, square_sum u = dot_prod u u

Therefore, by the Principle of Mathematical Induction on dimension of vector u = n, square_sum u = dot_prod u u

Hence Proved.
*)

(*
3. Scalar product of any scalar with zero vector is zero vector:

Given: b.v = scale b v where b is a scalar and v is a vector
    O is a zero vector
      
    To Prove: b.O = O where O is a zero vector and b is a scalar
    i.e. scale b O = O

                                                     Proof: 

                                                     Proof by Induction on n, where n = Dimension of vector O

      Base Case: n = 1
                   O = 0 :: []            - Since dimension of O = 1
                                                                 scale b O = (b *. 0) :: []     - By the Definition of scale
      (b *. 0) :: [] = 0 :: []       - By the Annihilator Property of Float Multiplication
      0 :: [] = O                   - By the Definition of O

      So, scale b O = O  for the Base Case

              Induction Hypothesis: Suppose for n = k, scale b O = O

                                                         Induction Step: Let n = k + 1

                                                                                   O = 0 :: O'                                 - Where O' is a vector of dimension k
                                     scale b O = (b *. 0) :: scale b O'          - By the Definition of scale
                                     (b *. 0) :: scale b O' = 0 :: scale b O'    - By the Annihilator Property of Float Multiplication
                                     0 :: scale b O' = 0 :: O'                   - By the Induction Hypothesis and By the Definition of O
      (Since O' = scale b O' where dimension of vector O' is k)

      0 :: O' = O                                 - By the Definition of O where dimension of vector O is k + 1

                                                                                                So, scale b O = O
                                                                                                    => b.O = O

                                                                                                      Therefore, by the Principle of Mathematical Induction on dimension of vector O = n, b.O = O

                                                                                                                                                                                            Hence Proved.
                                                                                                                                                                                                    *)

(*
4. For any vector v, v = inv(inv v)
*)
