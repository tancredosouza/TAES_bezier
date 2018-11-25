Add LoadPath "bezier-functions".

Require Import recursive.
Require Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Lemma bezier_curve_recursive_symm_fstdegree : 
  forall (P0 P1 : point) (q : Q),
    calc_bezier_recursive (P0 :: [P1]) q == calc_bezier_recursive (rev (P0 :: [P1])) (1 - q).
Proof.
  intros P0 P1 q.
  unfold calc_bezier_recursive. unfold rev. simpl.
  destruct P0 as [x0 y0]. destruct P1 as [x1 y1].
  unfold "==". simpl. split.
  { ring. }
  { ring. }
Qed.

Theorem bezier_curve_recursive_symm : forall (b : bezier_curve) (q : Q),
  calc_bezier_recursive b q == calc_bezier_recursive (rev b) (1 - q).
Proof.
  intros b Qed.
  induction b as [h| h b'].
  {
    unfold calc_bezier_recursive. unfold rev. simpl.
    destruct h as [xh yh]. unfold "==". simpl.
    split.
    { ring. }
    { ring. }
  }
  {
    unfold calc_bezier_recursive in IHb'. unfold rev in IHb'. simpl.
    unfold calc_bezier_recursive. unfold rev. simpl.
    admit.
  }
Admitted.