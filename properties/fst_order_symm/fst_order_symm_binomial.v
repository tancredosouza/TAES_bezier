Add LoadPath "bezier-functions".

Require Import binomial.
Require Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Lemma bezier_curve_binomial_symm_fstorder : 
  forall (P0 P1 : point) (q : Q),
    calc_bezier_binomial (P0 :: [P1]) q == calc_bezier_binomial (rev (P0 :: [P1])) (1 - q).
Proof.
  intros P0 P1 q.
  unfold calc_bezier_binomial. unfold rev. simpl.
  destruct P0 as [x0 y0]. destruct P1 as [x1 y1].
  unfold "==". simpl. split.
  { ring. }
  { ring. }
Qed.