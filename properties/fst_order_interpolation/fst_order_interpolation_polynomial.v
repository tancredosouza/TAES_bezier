Add LoadPath "bezier-functions".

Require Import polynomial.
Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Theorem bezier_curve_fst_order_interpolation_polynomial : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = P0 :: [P1] -> calc_bezier_polynomial b q == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  rewrite H. unfold calc_bezier_polynomial. unfold calc_polynomial. simpl.
  unfold calc_fact_div. simpl. unfold minus_1_sgn. simpl. unfold inject_Z.
  Search (_ qp* _). try rewrite qp_1_l.
  destruct P0 as [x0 y0]. destruct P1 as [x1 y1]. unfold "==". split.
  - simpl. ring.
  - simpl. ring. 
Qed.

Theorem bezier_curve_fst_order_interpolation_polynomial_rev : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = P0 :: [P1] -> calc_bezier_polynomial (rev b) (1 - q) == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  rewrite H. unfold calc_bezier_polynomial. unfold calc_polynomial. simpl.
  unfold calc_fact_div. simpl. unfold minus_1_sgn. simpl. unfold inject_Z.
  Search (_ qp* _). try rewrite qp_1_l.
  destruct P0 as [x0 y0]. destruct P1 as [x1 y1]. unfold "==". split.
  - simpl. ring.
  - simpl. ring. 
Qed.