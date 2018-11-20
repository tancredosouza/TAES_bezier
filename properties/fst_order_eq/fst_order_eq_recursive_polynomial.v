Add LoadPath "bezier-functions".
Add LoadPath "properties/fst_order_interpolation".

Require Import polynomial.
Require Import fst_order_interpolation_polynomial.
Require Import recursive.
Require Import fst_order_interpolation_recursive.
Import ListNotations.
Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Theorem bezier_curve_recursive_polynomial_eq_fstorder : 
  forall (b : bezier_curve) (P0 P1 : point) (q : Q),
    b = [P0; P1] -> calc_bezier_recursive b q == (calc_bezier_polynomial b q).
Proof.
  intros b P0 P1 q H. 
  rewrite H.
  unfold calc_bezier_recursive. simpl.
  unfold calc_bezier_polynomial. simpl.
  unfold calc_fact_div. simpl. 
  unfold minus_1_sgn. simpl.
  unfold inject_Z.
  destruct P0 as [ x0 y0 ]. destruct P1 as [ x1 y1 ].
  unfold "==". simpl. split.
  - ring.
  - ring.
Qed.