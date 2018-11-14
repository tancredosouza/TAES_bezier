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
Fixpoint inner_calc_point_at (b: bezier_curve) (t: Q) (n: nat): option (point) :=
  match b, n with
  | _, 0%nat      => None
  | h :: _, 1%nat => Some h
  | b', S n'      =>
    match inner_calc_point_at (init b') t n', inner_calc_point_at (tl b') t n' with
    | None, _ => None
    | _, None => None
    | Some vl, Some vr => Some (((1 - t) qp* vl) pp+ (t qp* vr))
    end
  end.

(* 1. PURELY RECURSIVE DEFINITION *)
Definition calc_bezier_recursive (b: bezier_curve) (t: Q): option (point) :=
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
Fixpoint calc_summ_pts (i j iter_left : nat) (b : bezier_curve) : option (point) :=
  match iter_left with
    | O => None
    | 1%nat => 
        match b with
          | [] => None
          | Pi :: _ => 
              Some (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi))
        end
    | S iter_left' => 
        match b with
          | [] => None
          | Pi :: b' => 
            match (calc_summ_pts (S i) j iter_left' b') with
              | None => None
              | Some Sj => 
                  Some (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi) pp+ Sj)
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
Fixpoint calc_Cj (n j : nat) (b : bezier_curve) : option (point) :=
  match (calc_summ_pts 0 j (S j) b) with
    | None => None
    | Some Sj => Some ((calc_fact_div n j) qp* Sj)
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
Fixpoint calc_polynomial (b : bezier_curve) (j n deg_left: nat) (t : Q) : option (point) :=
  match deg_left with
    | O => None
    | 1%nat =>
        match (calc_Cj n j b) with
          | None => None
          | Some Cn => Some ((pow t j) qp* Cn)
        end
    | S deg_left' =>
        match (calc_Cj n j b) with
          | None => None
          | Some Ci =>
              match (calc_polynomial b (S j) n deg_left' t) with
                | None => None
                | Some Ck => Some (((pow t j) qp* Ci) pp+ Ck)
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

Example t1 :
(eq_opt_pt (calc_bezier_polynomial l1 (1 # 2)) (calc_bezier_polynomial (rev l1) (1 # 2))).
Proof.
  simpl. unfold calc_fact_div. unfold minus_1_sgn. simpl.
  unfold inject_Z. simpl. split.
  + ring.
  + ring.
Qed.

Compute ( beq_pt (4275044352 # 6341787648, 288982579544064 # 500037272469504) (366585053184 # 543808290816, 657336595120128 # 1137413883691008)).