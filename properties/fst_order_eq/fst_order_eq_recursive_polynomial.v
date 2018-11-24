Add LoadPath "bezier-functions".

Require Import polynomial.
Require Import recursive.
Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Lemma bezier_curve_recursive_polynomial_app_eq :
  forall (b : bezier_curve) (p : point) (q : Q),
    (calc_bezier_recursive b q) == (calc_bezier_polynomial b q) ->
      (calc_bezier_recursive (p :: b) q) == (calc_bezier_polynomial (p :: b) q).
Proof.
  intros b.
  induction b.
  {
    admit.
  }
  {
    intros p' q' IHp.
    unfold calc_bezier_polynomial. 
    unfold calc_bezier_recursive.
    induction bezier_curve_length.
    {
      simpl. apply eq_pt_refl.
    }
    {
      simpl calc_polynomial.
    }
  }
Admitted.

Theorem bezier_curve_recursive_polynomial_eq_fstorder : 
  forall (b : bezier_curve) (q : Q),
    (calc_bezier_recursive b q) == (calc_bezier_polynomial b q).
Proof.
  intros b.
  induction b.
  {
    intros q. unfold calc_bezier_recursive. unfold calc_bezier_polynomial.
    simpl. unfold calc_fact_div. unfold minus_1_sgn. simpl.
    unfold "==". destruct p as [ x y ]. simpl. split.
    {
      ring.
    }
    {
      ring.
    }
  }
  {
    intros q.
    apply bezier_curve_recursive_polynomial_app_eq.
    apply IHb.
  }
Qed.