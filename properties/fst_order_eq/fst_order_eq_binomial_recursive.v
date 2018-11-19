Add LoadPath "bezier-functions".

Require Import binomial.
Require Import recursive.
Import ListNotations.
Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Theorem bezier_curve_recursive_binomial_eq_fstorder : 
  forall (b : bezier_curve) (P0 P1 : point) (q : Q),
    b = [P0; P1] -> (calc_bezier_recursive b q) == (calc_bezier_binomial b q).
Proof.
  intros b P0 P1 q eq1.
  rewrite -> eq1. destruct P0 as (x0, y0). destruct P1 as (x1, y1). 
  unfold calc_bezier_recursive. unfold calc_bezier_binomial.
  unfold "==". simpl. split.
  + ring.
  + ring.
Qed.