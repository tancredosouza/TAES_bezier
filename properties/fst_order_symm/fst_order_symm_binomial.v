Add LoadPath "bezier-functions".
Add LoadPath "properties/fst_order_interpolation".

Require Import binomial.
Require Import fst_order_interpolation_recursive.
Import ListNotations.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Lemma bezier_curve_polynomial_symm_fstorder : 
  forall (b : bezier_curve) (P0 P1 : point) (q : Q),
    b = [P0; P1] -> 
      calc_bezier_binomial b q == calc_bezier_binomial (rev b) (1 - q).
Proof.
  intros b P0 P1 q H.
  apply (bezier_curve_fst_order_interpolation_polynomial b P0 P1 q) in H as H1.
  apply (bezier_curve_fst_order_interpolation_polynomial_rev b P0 P1 q) in H as H2.
  
  destruct (calc_bezier_polynomial b q) as [ x3 y3 ].
  destruct (calc_bezier_polynomial (rev b) (1 - q)) as [ x4 y4 ].
  
  destruct P0 as [ x0 y0 ]. destruct P1 as [ x1 y1 ].
  assert (HX3 : Qeq x3 ((1 - q) * x0 + q * x1)).
  {
    unfold "==" in H1. destruct H1 as [Ha Hb].
    simpl in Ha. apply Ha.
  }
  assert (HX4 : Qeq x4 ((1 - q) * x0 + q * x1)).
  {
    unfold "==" in H2. destruct H2 as [Ha Hb].
    simpl in Ha. apply Ha.
  }
  assert (HY3 : Qeq y3 ((1 - q) * y0 + q * y1)).
  {
    unfold "==" in H1. destruct H1 as [Ha Hb].
    simpl in Hb. apply Hb.
  }
  assert (HY4 : Qeq y4 ((1 - q) * y0 + q * y1)).
  {
    unfold "==" in H2. destruct H2 as [Ha Hb].
    simpl in Hb. apply Hb.
  }
  
  unfold "==". simpl. split.
  {
    rewrite HX3. rewrite HX4. apply Qeq_refl.
  }
  {
    rewrite HY3. rewrite HY4. apply Qeq_refl.
  }
Qed.