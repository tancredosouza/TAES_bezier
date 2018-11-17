(*
              IF722

  BEZIER CURVE DEFINITIONS
  Authors: NETO, Divino and SOUZA, Tancredo
  
  
  This file contains the following definitions:
  1. Purely recursive definition
  2. Polynomial definition
  3. Binomial definition
  
  Reference:
    https://en.wikipedia.org/wiki/B%C3%A9zier_curve
*)

Add LoadPath "~/Desktop/TAES_bezier".
Require Export primitivedefs.

Require Export List.
Import ListNotations.

Definition bezier_curve := list point.

(* AUXILIARY FUNCTIONS *)

(* 
  init: Given a list of type X,
  this function returns the whole 
  list except for the last element.
 *)
Fixpoint init {X: Type} (l: list X): list X :=
  match l with
  | []      => []
  | h :: [] => []
  | h :: t  => h :: (init t)
  end.

Compute (init [1 # 2; 3 # 2; 3 # 6]).


(*
  inner_calc_point_at: This function implements
  the formal recursive definition of a bezier curve.
  
  Let b = [P0; P1; P2; P3; P4 ... ; Pn]
  B(P0, t) = P0,
  B(t) = (1 - t) * B(init b, t) + t * B(tail b, t) 
  
*)
Fixpoint inner_calc_point_at (b: bezier_curve) (t: Q) (n: nat): point :=
  match b, n with
  | _, 0%nat      => (0 , 0)
  | h :: _, 1%nat => h
  | b', S n'      =>
     ((1 - t) qp* (inner_calc_point_at (init b') t n')) pp+ (t qp* (inner_calc_point_at (tl b') t n'))
  end.

(* 1. PURELY RECURSIVE DEFINITION *)
Definition calc_bezier_recursive (b: bezier_curve) (t: Q): (point) :=
  inner_calc_point_at b t (length b).

Compute (calc_bezier_recursive [(0, 1); (0, 0); (1, 0)] (1 # 2)).

(* --------------------------- *)


(* AUXILIARY FUNCTIONS *)

(*
  fact_pos : Given a natural n,
              returns n! as a positive
              
  This function is necessary due to Coq's
  recursive definition of a natural number,
  which easily causes a 'stack overflow'
  for larger computations.
*)
Fixpoint fact_pos (n : nat) : positive :=
  match n with
    | O => 1
    | S n' => (Pos.of_nat n) * (fact_pos n')
  end.

(*
  pow : Given a natural n and a rational q,
              returns q^n as a rational.
*)
Fixpoint pow (x : Q) (n : nat) : Q :=
  match n with
    | O => 1
    | S n' => Qmult x (pow x n')
  end.

(*
  minus_1_sgn : Given a natural exp,
              returns (-1)^exp.
*)
Definition minus_1_sgn (exp : nat) : Q := 
  match (Nat.even exp) with
    | true => 1
    | false => inject_Z (-1)
  end.


(*
  calc_summ_pts : Given a list of points,
      calculate the summation for a Cj.
      This is necessary for the polynomial
      definition.
      
              j
            ----
            \     (-1)^(i + j) * Pi
     Sj =    >    -----------------
            /        i! (j - i)!
            ----
            i = 0
*)
Fixpoint calc_summ_pts (i j iter_left : nat) (b : bezier_curve) : (point) :=
  match iter_left with
    | O => (0, 0)
    | 1%nat => 
        match b with
          | [] => (0,0)
          | Pi :: _ => 
              (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi))
        end
    | S iter_left' => 
        match b with
          | [] => (0,0)
          | Pi :: b' => 
            match (calc_summ_pts (S i) j iter_left' b') with
              | Sj => 
                  (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi) pp+ Sj)
            end
        end
    end.

(*
   calc_fact_div : Given two naturals n j,
    returns 
               n!
       Mj  = --------
             (n - j)!
    This is necessary for the polynomial
      definition.
*)
Definition calc_fact_div (n j : nat) : Q :=
  ((Z.of_nat (Pos.to_nat (fact_pos n))) # (fact_pos (n - j))).


(*
  calc_Cj : This function returns Cj, 
  necessary for the polynomial definition.
  
  
          Cj = Mj * Sj
*)
Fixpoint calc_Cj (n j : nat) (b : bezier_curve) : (point) :=
  match (calc_summ_pts 0 j (S j) b) with
    | Sj => ((calc_fact_div n j) qp* Sj)
  end.

(*
  calc_polynomial : This function returns a point
  in a bezier curve defined polynomially.
  
  
              n
            ----
            \
     B(t) =  >    t^j * Cj
            /
            ----
            j = 0
*)
Fixpoint calc_polynomial (b : bezier_curve) (j n deg_left: nat) (t : Q) : (point) :=
  match deg_left with
    | O => (0,0)
    | 1%nat =>
        match (calc_Cj n j b) with
          | Cn => ((pow t j) qp* Cn)
        end
    | S deg_left' =>
        match (calc_Cj n j b) with
          | Ci =>
              match (calc_polynomial b (S j) n deg_left' t) with
                | Ck => (((pow t j) qp* Ci) pp+ Ck)
              end
        end
  end.


(* 2. POLYNOMIAL DEFINITION *)
Definition calc_bezier_polynomial (b : bezier_curve) (t : Q) :=
  calc_polynomial b 0 (Nat.pred (length b)) (length b) t.

Compute (calc_bezier_polynomial [(0, 1); (0, 0); (1, 0)] (1 # 2)).


Definition l1 := [(1 # 2, 4 # 8); (1 # 2, 4 # 8); (3 # 4, 4 # 7); (8 # 7, 10 # 11)].

Compute (calc_bezier_polynomial [(0, 1); (0, 0); (1, 0)] (1 # 2)).
Compute (calc_bezier_recursive [(0, 1); (0, 0); (1, 0)] (1 # 2)).

Compute (calc_bezier_polynomial l1 (1 # 2)).
Compute (calc_bezier_polynomial (rev l1) (1 # 2)).

Compute ( beq_pt (4275044352 # 6341787648, 288982579544064 # 500037272469504) (366585053184 # 543808290816, 657336595120128 # 1137413883691008)).