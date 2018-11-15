Require Export bezier_curve_functiondefs.

Import ListNotations.
Check calc_bezier_polynomial.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
(*
  Teorema 1 desse documento aqui

  http://www.ursoswald.ch/metapost/tutorial/BezierDoc/BezierDoc.pdf
*)

Theorem bezier_curve_fst_order_recursive : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_recursive b q = (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  unfold calc_bezier_recursive. 
  rewrite H. 
  simpl. reflexivity.
Qed.

Theorem bezier_curve_fst_order_recursive_rev : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_recursive (rev b) q = (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  rewrite H. simpl. unfold calc_bezier_recursive. simpl.
Admitted.

Theorem bezier_curve_fst_order_polynomial : forall (b : bezier_curve) (P0 P1 p : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_polynomial b q = Some p -> p == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 p q eq1 eq2.
  unfold calc_bezier_polynomial in eq2. 
  rewrite eq1 in eq2. simpl in eq2.
  inversion eq2. 
  unfold calc_fact_div. simpl. unfold minus_1_sgn. simpl.
  unfold inject_Z.
  unfold "==". split.
  + destruct P0 as (x0, y0). destruct P1 as (x1, y1).
    simpl. repeat rewrite Qmult_1_l. ring.
  + destruct P0 as (x0, y0). destruct P1 as (x1, y1).
    simpl. repeat rewrite Qmult_1_l. ring.
Qed.

Definition l2 := [(1 # 2, 1 # 4); (3 # 4, 8 # 4)].
Compute (calc_bezier_recursive l2 (33 # 17)).

Theorem bezier_curve_recursive_symm_firsttry : forall (b b' : bezier_curve) (P0 P1 : point) (q : Q),
  b = [P0; P1] ++ b' -> calc_bezier_recursive b q == calc_bezier_recursive (rev b) (1 - q).
Proof.
  intros b b' P0 P1 q eq1. 
  induction b'.
  {
    simpl in eq1. 
    apply (bezier_curve_fst_order_recursive b P0 P1 q) in eq1 as H0.
    simpl. 
    assert (rev_eq1: rev b = [P1; P0]).
    {
      rewrite eq1. reflexivity.
    }
    apply (bezier_curve_fst_order_recursive (rev b) P1 P0 (1 - q)) in rev_eq1 as H1.
    rewrite H0. rewrite H1.
    unfold "==". split.
    {
      destruct P0 as [x0 y0]. destruct P1 as [x1 y1].
      simpl. ring. 
    }
    {
      destruct P0 as [x0 y0]. destruct P1 as [x1 y1].
      simpl. ring.
    }
  }
Admitted.

Lemma eq_pt_refl : forall (p : point),
  p == p.
Proof.
  intros p. destruct p as [x y].
  unfold "==". split.
  - simpl. apply Qeq_refl.
  - simpl. apply Qeq_refl.
Qed.

Lemma qp_mult_pt : forall (p : point) (q : Q),
  (q qp* p) = (0, 0).
Proof.
Admitted. 

Lemma inner_calc_point_at_empty_eq : forall (n : nat) (q : Q),
  (inner_calc_point_at [] q n) = (0,0).
Proof.
  intros n q.
  induction n.
  {
    simpl. reflexivity.
  }
  {
    simpl. rewrite IHn. repeat rewrite qp_mult_pt.
    simpl. reflexivity.
  }
Qed.

Lemma inner_calc_point_at_empty : forall (n : nat) (q : Q),
  (inner_calc_point_at [] q n) = (0,0).
Proof.
  intros n q.
  induction n.
  {
    simpl. reflexivity.
  }
  {
    simpl. inversion IHn. 
    simpl. rewrite inner_calc_point_at_empty_eq. repeat rewrite qp_mult_pt.
    simpl. reflexivity.
  }
Qed.

Theorem inner_calc_point_at_app : forall (x' : bezier_curve) (P0 : point) (n n' : nat) (q : Q),
  n = S n' -> (inner_calc_point_at (P0 :: x') q n) ==
  (((1 - q) qp* (inner_calc_point_at (P0 :: (init x')) q (Nat.pred n))) 
    pp+ (q qp* (inner_calc_point_at (x') q (Nat.pred n)))).
Proof.
  intros x' P0 n n' q H1. induction x'.
  { 
    simpl. rewrite H1.
    simpl. 
    {
      simpl. Search (_ * 0). unfold "==". split.
      {
        simpl. repeat rewrite Qmult_0_r. reflexivity.
      }
      {
        simpl. repeat rewrite Qmult_0_r. reflexivity.
      }
    }
    {
      Search (Nat.pred (S _)). rewrite Nat.pred_succ.
      simpl. repeat rewrite inner_calc_point_at_empty.
      inversion H1.
    }
  }
  {}
Qed.

Theorem bezier_curve_recursive_symm : forall (b : bezier_curve) (q : Q),
  calc_bezier_recursive b q = calc_bezier_recursive (rev b) (1 - q).
Proof.
  intros b q.
  unfold calc_bezier_recursive.
  induction b as [ | h b'].
  {
    simpl. reflexivity.
  }
  {
    simpl. destruct (length b').
    {
      
    }
  }
  
Admitted.
