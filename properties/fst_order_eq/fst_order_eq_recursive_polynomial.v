Add LoadPath "bezier-functions".

Require Import polynomial.
Require Import recursive.
Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Theorem bezier_curve_recursive_polynomial_eq_fstorder : 
  forall (b : bezier_curve) (P0 P1 : point) (q : Q),
    b = P0 :: [P1] -> calc_bezier_recursive b q == (calc_bezier_polynomial b q).
Proof.
  intros b P0 P1 q H.
  rewrite H. unfold calc_bezier_recursive. unfold calc_bezier_polynomial.
  - assert (calc_bezier_recursive b q == (((1 - q) qp* P0) pp+ (q qp* P1))).
    {
      destruct P0 as [ x0 y0 ]. destruct P1 as [ x1 y1 ].
      rewrite H. unfold calc_bezier_recursive. simpl.
    }
  
  
Qed.