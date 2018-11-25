Add LoadPath "bezier-functions".

Require Import polynomial.
Require Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Lemma bezier_curve_polynomial_symm_fstdegree : 
  forall (P0 P1 : point) (q : Q),
      calc_bezier_polynomial (P0 :: [P1]) q == calc_bezier_polynomial (rev (P0 :: [P1])) (1 - q).
Proof.
  intros P0 P1 q.
  unfold calc_bezier_polynomial. unfold rev. simpl.
  unfold calc_fact_div. unfold minus_1_sgn. unfold inject_Z. simpl.
  destruct P0 as [x0 y0]. destruct P1 as [x1 y1].
  unfold "==". simpl. split.
  { ring. }
  { ring. }
Qed.

