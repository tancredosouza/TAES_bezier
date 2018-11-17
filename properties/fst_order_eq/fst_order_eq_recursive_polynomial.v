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
  apply (bezier_curve_fst_order_interpolation_recursive b P0 P1 q) in H as H1.
  apply (bezier_curve_fst_order_interpolation_polynomial b P0 P1 q) in H as H2.
  destruct (calc_bezier_polynomial b q) as [ x3 y3 ].
  destruct (calc_bezier_recursive b q) as [ x4 y4 ].
  destruct P0 as [ x0 y0 ]. destruct P1 as [ x1 y1 ].
  assert (HX3 : Qeq x3 ((1 - q) * x0 + q * x1)).
  {
    unfold "==" in H2. destruct H2 as [H2a H2b].
    simpl in H2a. apply H2a.
  }
  assert (HX4 : Qeq x4 ((1 - q) * x0 + q * x1)).
  {
    unfold "==" in H1. destruct H1 as [H1a H1b].
    simpl in H1a. apply H1a.
  }
  assert (HY3 : Qeq y3 ((1 - q) * y0 + q * y1)).
  {
    unfold "==" in H2. destruct H2 as [H2a H2b].
    simpl in H2b. apply H2b.
  }
  assert (HY4 : Qeq y4 ((1 - q) * y0 + q * y1)).
  {
    unfold "==" in H1. destruct H1 as [H1a H1b].
    simpl in H1b. apply H1b.
  }
  unfold "==". simpl. split.
  {
    rewrite HX3. rewrite HX4. apply Qeq_refl.
  }
  {
    rewrite HY3. rewrite HY4. apply Qeq_refl.
  }
Qed.