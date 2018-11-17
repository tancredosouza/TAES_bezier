Add LoadPath "bezier-functions".

Require Import binomial.
Import ListNotations.
Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Theorem bezier_curve_fst_order_binomial : forall (P0 P1 : point) (q : Q), 
  (calc_bezier_binomial [P0; P1] q) == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros P0 P1 q.
  unfold calc_bezier_binomial. simpl.
  destruct P0 as (x0, y0). destruct P1 as (x1, y1). simpl.
  unfold "==". simpl. split.
  + ring.
  + ring.
Qed.
