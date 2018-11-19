Add LoadPath "bezier-functions".

Require Import binomial.
Import ListNotations.
Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Theorem bezier_curve_fst_order_binomial : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> (calc_bezier_binomial b q) == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  rewrite H.
  unfold calc_bezier_binomial. simpl.
  destruct P0 as (x0, y0). destruct P1 as (x1, y1). simpl.
  unfold "==". simpl. split.
  + ring.
  + ring.
Qed.

Theorem bezier_curve_fst_order_binomial_rev : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> (calc_bezier_binomial (rev b) (1 - q)) == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  rewrite H.
  unfold calc_bezier_binomial. simpl.
  destruct P0 as (x0, y0). destruct P1 as (x1, y1). simpl.
  unfold "==". simpl. split.
  + ring.
  + ring.
Qed.