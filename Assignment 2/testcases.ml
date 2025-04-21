(* Aditya Anand : 2023CS50284 *)
open A2 
                        
    (* --------------------------------------------- TYPE CHECK TESTCASES -------------------------------------------------- *)

let%test "type_of T" = (type_of T = Bool)
let%test "type_of F" = (type_of F = Bool)

let%test "type_of (ConstS 3.14)" = (type_of (ConstS 3.14) = Scalar)
let%test "type_of (ConstS (-2.5))" = (type_of (ConstS (-2.5)) = Scalar)

let%test "type_of (ConstV [1.0; 2.0; 3.0])" = (type_of (ConstV [1.0; 2.0; 3.0]) = Vector 3)
let%test "type_of (ConstV [2.0])" = (type_of (ConstV [2.0]) = Vector 1)

let%test "type_of (Add (T, F))" = (type_of (Add (T, F)) = Bool)
let%test "type_of (Add (ConstS 1.0, ConstS 2.0))" = (type_of (Add (ConstS 1.0, ConstS 2.0)) = Scalar)
let%test "type_of (Add (ConstV [1.0; 2.0], ConstV [3.0; 4.0]))" = (type_of (Add (ConstV [1.0; 2.0], ConstV [3.0; 4.0])) = Vector 2)

let%test "type_of (Inv T)" = (type_of (Inv T) = Bool)
let%test "type_of (Inv (ConstS (-2.5)))" = (type_of (Inv (ConstS (-2.5))) = Scalar)
let%test "type_of (Inv (ConstV [1.0; 3.0]))" = (type_of (Inv (ConstV [1.0; 3.0])) = Vector 2)

let%test "type_of (ScalProd (ConstS 2.0, ConstV [1.0; 2.0]))" = (type_of (ScalProd (ConstS 2.0, ConstV [1.0; 2.0])) = Vector 2)
let%test "type_of (ScalProd (ConstV [1.0; 2.0], ConstS 3.0))" = (type_of (ScalProd (ConstV [1.0; 2.0], ConstS 3.0)) = Vector 2) 
let%test "type_of (ScalProd (T, F))" = (type_of (ScalProd (T, F)) = Bool) 
let%test "type_of (ScalProd (ConstS 2.0, ConstS 3.0))" = (type_of (ScalProd (ConstS 2.0, ConstS 3.0)) = Scalar)

let%test "type_of (DotProd (ConstV [1.0; 2.0], ConstV [3.0; 4.0]))" = (type_of (DotProd (ConstV [1.0; 2.0], ConstV [3.0; 4.0])) = Scalar)
let%test "type_of (DotProd (ConstV [2.0; 1.0; 3.0], ConstV [1.0; 3.0; 4.0]))" = (type_of (DotProd (ConstV [2.0; 1.0; 3.0], ConstV [1.0; 3.0; 4.0])) = Scalar)

let%test "type_of (Mag (ConstV [3.0; 4.0]))" = (type_of (Mag (ConstV [3.0; 4.0])) = Scalar)
let%test "type_of (Mag (ConstS 5.0))" = (type_of (Mag (ConstS 5.0)) = Scalar)

let%test "type_of (Angle (ConstV [1.0; 0.0], ConstV [0.0; 1.0]))" = (type_of (Angle (ConstV [1.0; 0.0], ConstV [0.0; 1.0])) = Scalar)
let%test "type_of (Angle (ConstV [1.0; 1.0], ConstV [2.0; 2.0]))" = (type_of (Angle (ConstV [1.0; 1.0], ConstV [2.0; 2.0])) = Scalar)

let%test "type_of (IsZero (ConstS 0.0))" = (type_of (IsZero (ConstS 0.0)) = Bool)
let%test "type_of (IsZero T)" = (type_of (IsZero T) = Bool)
let%test "type_of (IsZero (ConstV [0.0; 0.0]))" = (type_of (IsZero (ConstV [0.0; 0.0])) = Bool)
  

(* ------------------------------------- EXCEPTIONS ---------------------------------------- *)                                       
(* ConstV Exception Test *)
let%test "type_of (ConstV []) raises Wrong (ConstV [])" = 
  (try let _ = type_of (ConstV []) in false 
   with | Wrong e -> e = ConstV [] | _ -> false)

(* Add Exception Tests *)
let%test "type_of (Add (T, ConstS 1.0)) raises Wrong (Add (T, ConstS 1.0))" = 
  (try let _ = type_of (Add (T, ConstS 1.0)) in false 
   with | Wrong e -> e = Add (T, ConstS 1.0) | _ -> false)

let%test "type_of (Add (ConstV [1.0; 2.0], ConstV [1.0])) raises Wrong (Add (ConstV [1.0; 2.0], ConstV [1.0]))" = 
  (try let _ = type_of (Add (ConstV [1.0; 2.0], ConstV [1.0])) in false 
   with | Wrong e -> e = Add (ConstV [1.0; 2.0], ConstV [1.0]) | _ -> false)

(* ScalProd Exception Tests *)
let%test "type_of (ScalProd (ConstV [1.0], ConstV [2.0])) raises Wrong (ScalProd (ConstV [1.0], ConstV [2.0]))" = 
  (try let _ = type_of (ScalProd (ConstV [1.0], ConstV [2.0])) in false 
   with | Wrong e -> e = ScalProd (ConstV [1.0], ConstV [2.0]) | _ -> false)

let%test "type_of (ScalProd (T, ConstS 1.0)) raises Wrong (ScalProd (T, ConstS 1.0))" = 
  (try let _ = type_of (ScalProd (T, ConstS 1.0)) in false 
   with | Wrong e -> e = ScalProd (T, ConstS 1.0) | _ -> false)

(* DotProd Exception Tests *)
let%test "type_of (DotProd (ConstV [1.0; 2.0], ConstV [1.0])) raises Wrong (DotProd (ConstV [1.0; 2.0], ConstV [1.0]))" = 
  (try let _ = type_of (DotProd (ConstV [1.0; 2.0], ConstV [1.0])) in false 
   with | Wrong e -> e = DotProd (ConstV [1.0; 2.0], ConstV [1.0]) | _ -> false)

let%test "type_of (DotProd (ConstS 1.0, ConstS 2.0)) raises Wrong (DotProd (ConstS 1.0, ConstS 2.0))" = 
  (try let _ = type_of (DotProd (ConstS 1.0, ConstS 2.0)) in false 
   with | Wrong e -> e = DotProd (ConstS 1.0, ConstS 2.0) | _ -> false)

(* Mag Exception Test *)
let%test "type_of (Mag T) raises Wrong (Mag T)" = 
  (try let _ = type_of (Mag T) in false 
   with | Wrong e -> e = Mag T | _ -> false)

(* Angle Exception Tests *)
let%test "type_of (Angle (ConstV [1.0; 2.0], ConstV [1.0])) raises Wrong (Angle (ConstV [1.0; 2.0], ConstV [1.0]))" = 
  (try let _ = type_of (Angle (ConstV [1.0; 2.0], ConstV [1.0])) in false 
   with | Wrong e -> e = Angle (ConstV [1.0; 2.0], ConstV [1.0]) | _ -> false)

let%test "type_of (Angle (ConstS 1.0, ConstS 2.0)) raises Wrong (Angle (ConstS 1.0, ConstS 2.0))" = 
  (try let _ = type_of (Angle (ConstS 1.0, ConstS 2.0)) in false 
   with | Wrong e -> e = Angle (ConstS 1.0, ConstS 2.0) | _ -> false)

(* Cond Exception Tests *)
let%test "type_of (Cond (ConstS 1.0, T, F)) raises Wrong (Cond (ConstS 1.0, T, F))" = 
  (try let _ = type_of (Cond (ConstS 1.0, T, F)) in false 
   with | Wrong e -> e = Cond (ConstS 1.0, T, F) | _ -> false)

let%test "type_of (Cond (T, ConstS 1.0, ConstV [1.0])) raises Wrong (Cond (T, ConstS 1.0, ConstV [1.0]))" = 
  (try let _ = type_of (Cond (T, ConstS 1.0, ConstV [1.0])) in false 
   with | Wrong e -> e = Cond (T, ConstS 1.0, ConstV [1.0]) | _ -> false)
  
    (* --------------------------------------- EVAL TESTCASES ----------------------------------------------------------- *)

let%test "eval T" = (eval T = B true)
let%test "eval F" = (eval F = B false)

let%test "eval (ConstS 3.14)" = (eval (ConstS 3.14) = S 3.14)
let%test "eval (ConstS (-2.5))" = (eval (ConstS (-2.5)) = S (-2.5))

let%test "eval (ConstV [1.0; 2.0; 3.0])" = (eval (ConstV [1.0; 2.0; 3.0]) = V [1.0; 2.0; 3.0])
let%test "eval (ConstV [2.0])" = (eval (ConstV [2.0]) = V [2.0])

let%test "eval (Add (T, F))" = (eval (Add (T, F)) = B true)
let%test "eval (Add (ConstS 1.0, ConstS 2.0))" = (eval (Add (ConstS 1.0, ConstS 2.0)) = S 3.0)
let%test "eval (Add (ConstV [1.0; 2.0], ConstV [3.0; 4.0]))" = (eval (Add (ConstV [1.0; 2.0], ConstV [3.0; 4.0])) = V [4.0; 6.0])

let%test "eval (Inv T)" = (eval (Inv T) = B false)
let%test "eval (Inv (ConstS (-2.5)))" = (eval (Inv (ConstS (-2.5))) = S 2.5)
let%test "eval (Inv (ConstV [1.0; 3.0]))" = (eval (Inv (ConstV [1.0; 3.0])) = V [-1.0; -3.0])

let%test "eval (ScalProd (ConstS 2.0, ConstV [1.0; 2.0]))" = (eval (ScalProd (ConstS 2.0, ConstV [1.0; 2.0])) = V [2.0; 4.0])
let%test "eval (ScalProd (ConstV [1.0; 2.0], ConstS 3.0))" = (eval (ScalProd (ConstV [1.0; 2.0], ConstS 3.0)) = V [3.0; 6.0])
let%test "eval (ScalProd (T, F))" = (eval (ScalProd (T, F)) = B false)
let%test "eval (ScalProd (ConstS 2.0, ConstS 3.0))" = (eval (ScalProd (ConstS 2.0, ConstS 3.0)) = S 6.0)

let%test "eval (DotProd (ConstV [1.0; 2.0], ConstV [3.0; 4.0]))" = (eval (DotProd (ConstV [1.0; 2.0], ConstV [3.0; 4.0])) = S 11.0)
let%test "eval (DotProd (ConstV [2.0; 1.0; 3.0], ConstV [1.0; 3.0; 4.0]))" = (eval (DotProd (ConstV [2.0; 1.0; 3.0], ConstV [1.0; 3.0; 4.0])) = S 17.0)

let%test "eval (Mag (ConstV [3.0; 4.0]))" = (eval (Mag (ConstV [3.0; 4.0])) = S 5.0)
let%test "eval (Mag (ConstS 5.0))" = (eval (Mag (ConstS 5.0)) = S 5.0)

let%test "eval (Angle (ConstV [1.0; 1.0], ConstV [2.0; 2.0]))" = (eval (Angle (ConstV [1.0; 1.0], ConstV [2.0; 2.0])) = S 0.0)

let%test "eval (IsZero (ConstS 0.0))" = (eval (IsZero (ConstS 0.0)) = B true)
let%test "eval (IsZero T)" = (eval (IsZero T) = B false)
let%test "eval (IsZero (ConstV [0.0; 0.0]))" = (eval (IsZero (ConstV [0.0; 0.0])) = B true) 
                                               
    (* ------------------------------------- EXCEPTIONS ---------------------------------------- *)
 (* Empty Vector Test *)
let%test "eval (ConstV []) raises Wrong (ConstV [])" = 
  (try let _ = eval (ConstV []) in false 
   with | Wrong e -> e = ConstV [] | _ -> false)

(* Add - Type Mismatch Tests *)
let%test "eval (Add (T, ConstS 1.0)) raises Wrong (Add (T, ConstS 1.0))" = 
  (try let _ = eval (Add (T, ConstS 1.0)) in false 
   with | Wrong e -> e = Add (T, ConstS 1.0) | _ -> false)

let%test "eval (Add (ConstV [1.0], ConstS 1.0)) raises Wrong (Add (ConstV [1.0], ConstS 1.0))" = 
  (try let _ = eval (Add (ConstV [1.0], ConstS 1.0)) in false 
   with | Wrong e -> e = Add (ConstV [1.0], ConstS 1.0) | _ -> false)

let%test "eval (Add (ConstV [1.0; 2.0], ConstV [1.0])) raises Wrong (Add (ConstV [1.0; 2.0], ConstV [1.0]))" = 
  (try let _ = eval (Add (ConstV [1.0; 2.0], ConstV [1.0])) in false 
   with | Wrong e -> e = Add (ConstV [1.0; 2.0], ConstV [1.0]) | _ -> false)

(* ScalProd - Type Mismatch Tests *)
let%test "eval (ScalProd (ConstV [1.0], ConstV [2.0])) raises Wrong (ScalProd (ConstV [1.0], ConstV [2.0]))" = 
  (try let _ = eval (ScalProd (ConstV [1.0], ConstV [2.0])) in false 
   with | Wrong e -> e = ScalProd (ConstV [1.0], ConstV [2.0]) | _ -> false)

let%test "eval (ScalProd (T, ConstS 1.0)) raises Wrong (ScalProd (T, ConstS 1.0))" = 
  (try let _ = eval (ScalProd (T, ConstS 1.0)) in false 
   with | Wrong e -> e = ScalProd (T, ConstS 1.0) | _ -> false)

(* DotProd - Dimension and Type Mismatch Tests *)
let%test "eval (DotProd (ConstV [1.0], ConstV [1.0; 2.0])) raises Wrong (DotProd (ConstV [1.0], ConstV [1.0; 2.0]))" = 
  (try let _ = eval (DotProd (ConstV [1.0], ConstV [1.0; 2.0])) in false 
   with | Wrong e -> e = DotProd (ConstV [1.0], ConstV [1.0; 2.0]) | _ -> false)

let%test "eval (DotProd (ConstS 1.0, ConstV [1.0])) raises Wrong (DotProd (ConstS 1.0, ConstV [1.0]))" = 
  (try let _ = eval (DotProd (ConstS 1.0, ConstV [1.0])) in false 
   with | Wrong e -> e = DotProd (ConstS 1.0, ConstV [1.0]) | _ -> false)

(* Mag - Invalid Type Test *)
let%test "eval (Mag T) raises Wrong (Mag T)" = 
  (try let _ = eval (Mag T) in false 
   with | Wrong e -> e = Mag T | _ -> false)

(* Angle - Various Error Cases *)
let%test "eval (Angle (ConstS 1.0, ConstS 2.0)) raises Wrong (Angle (ConstS 1.0, ConstS 2.0))" = 
  (try let _ = eval (Angle (ConstS 1.0, ConstS 2.0)) in false 
   with | Wrong e -> e = Angle (ConstS 1.0, ConstS 2.0) | _ -> false)

let%test "eval (Angle (ConstV [1.0], ConstV [1.0; 2.0])) raises Wrong (Angle (ConstV [1.0], ConstV [1.0; 2.0]))" = 
  (try let _ = eval (Angle (ConstV [1.0], ConstV [1.0; 2.0])) in false 
   with | Wrong e -> e = Angle (ConstV [1.0], ConstV [1.0; 2.0]) | _ -> false)

let%test "eval (Angle (ConstV [0.0; 0.0], ConstV [1.0; 1.0])) raises Wrong (Angle (ConstV [0.0; 0.0], ConstV [1.0; 1.0]))" = 
  (try let _ = eval (Angle (ConstV [0.0; 0.0], ConstV [1.0; 1.0])) in false 
   with | Wrong e -> e = Angle (ConstV [0.0; 0.0], ConstV [1.0; 1.0]) | _ -> false)

(* IsZero - Type Related Tests *)
let%test "eval (IsZero (ConstV [])) raises Wrong (ConstV [])" = 
  (try let _ = eval (IsZero (ConstV [])) in false 
   with | Wrong e -> e = ConstV [] | _ -> false)

(* Cond - Various Error Cases *)
let%test "eval (Cond (ConstS 1.0, T, F)) raises Wrong (Cond (ConstS 1.0, T, F))" = 
  (try let _ = eval (Cond (ConstS 1.0, T, F)) in false 
   with | Wrong e -> e = Cond (ConstS 1.0, T, F) | _ -> false)

let%test "eval (Cond (T, ConstS 1.0, ConstV [1.0])) raises Wrong (Cond (T, ConstS 1.0, ConstV [1.0]))" = 
  (try let _ = eval (Cond (T, ConstS 1.0, ConstV [1.0])) in false 
   with | Wrong e -> e = Cond (T, ConstS 1.0, ConstV [1.0]) | _ -> false)

(* Nested Expression Tests *)
let%test "eval (Add (Add (T, F), ConstS 1.0)) raises Wrong (Add (Add (T, F), ConstS 1.0))" = 
  (try let _ = eval (Add (Add (T, F), ConstS 1.0)) in false 
   with | Wrong e -> e = Add (Add (T, F), ConstS 1.0) | _ -> false)

let%test "eval (ScalProd (DotProd (ConstV [1.0], ConstV [1.0]), T)) raises Wrong (ScalProd (DotProd (ConstV [1.0], ConstV [1.0]), T))" = 
  (try let _ = eval (ScalProd (DotProd (ConstV [1.0], ConstV [1.0]), T)) in false 
   with | Wrong e -> e = ScalProd (DotProd (ConstV [1.0], ConstV [1.0]), T) | _ -> false)