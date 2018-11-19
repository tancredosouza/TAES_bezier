Add LoadPath "bezier-functions".

Require Import polynomial.
Require Import binomial.
Import ListNotations.
Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Theorem bezier_curve_polynomial_binomial_eq_fstorder : 
  forall (b : bezier_curve) (P0 P1 : point) (q : Q),
    b = [P0; P1] -> (calc_bezier_polynomial b q) == (calc_bezier_binomial b q).
Proof.
  intros b P0 P1 q eq1.
  rewrite -> eq1. destruct P0 as (x0, y0). destruct P1 as (x1, y1). unfold calc_bezier_polynomial. unfold calc_bezier_binomial. simpl.
  unfold calc_fact_div. unfold minus_1_sgn.  unfold inject_Z. simpl.
  unfold "==". simpl. split.
  + ring.
  + ring.
Qed.