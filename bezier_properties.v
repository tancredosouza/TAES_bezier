Require Export bezier_curve_functiondefs.

Import ListNotations.
Check calc_bezier_polynomial.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.
(*
  Teorema 1 desse documento aqui

  http://www.ursoswald.ch/metapost/tutorial/BezierDoc/BezierDoc.pdf
*)


Lemma eq_pt_refl : forall (p : point),
  p == p.
Proof.
  intros p. destruct p as [x y].
  unfold "==". split.
  - simpl. apply Qeq_refl.
  - simpl. apply Qeq_refl.
Qed.

Theorem bezier_curve_fst_order_recursive : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_recursive b q == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  unfold calc_bezier_recursive. 
  rewrite H. 
  simpl. apply eq_pt_refl.
Qed.

Theorem bezier_curve_fst_order_recursive_rev : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_recursive (rev b) (1 - q) 
    == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  rewrite H. simpl. unfold calc_bezier_recursive. simpl.
  destruct P1 as [x1 y1]. destruct P0 as [x0 y0]. unfold "==". 
  simpl. split. 
  - ring.
  - ring.
Qed.



Theorem bezier_curve_fst_order_polynomial : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_polynomial b q == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  rewrite H. unfold calc_bezier_polynomial. unfold calc_polynomial. simpl.
  unfold calc_fact_div. simpl. unfold minus_1_sgn. simpl. unfold inject_Z.
  Search (_ qp* _). try rewrite qp_1_l.
  destruct P0 as [x0 y0]. destruct P1 as [x1 y1]. unfold "==". split.
  - simpl. ring.
  - simpl. ring. 
Qed.

Theorem bezier_curve_recursive_polynomial_eq_fstorder : 
  forall (b : bezier_curve) (P0 P1 : point) (q : Q),
    b = [P0; P1] -> calc_bezier_recursive b q == (calc_bezier_polynomial b q).
Proof.
  intros b P0 P1 q H. 
  apply (bezier_curve_fst_order_recursive b P0 P1 q) in H as H1.
  apply (bezier_curve_fst_order_polynomial b P0 P1 q) in H as H2.
  destruct (calc_bezier_polynomial b q) as [ x3 y3 ].
  destruct (calc_bezier_recursive b q) as [ x4 y4 ].
  destruct P0 as [ x0 y0 ]. destruct P1 as [ x1 y1 ].
  assert (HX3 : Qeq x3 ((1 - q) * x0 + q * x1)).
  {
    unfold "==" in H2. destruct H2 as [H2a H2b].
    simpl in H2a. apply H2a.
  }
  assert (HX4 : Qeq x4 ((1 - q) * x0 + q * x1)).
  {
    unfold "==" in H1. destruct H1 as [H1a H1b].
    simpl in H1a. apply H1a.
  }
  assert (HY3 : Qeq y3 ((1 - q) * y0 + q * y1)).
  {
    unfold "==" in H2. destruct H2 as [H2a H2b].
    simpl in H2b. apply H2b.
  }
  assert (HY4 : Qeq y4 ((1 - q) * y0 + q * y1)).
  {
    unfold "==" in H1. destruct H1 as [H1a H1b].
    simpl in H1b. apply H1b.
  }
  
  unfold "==". simpl. split.
  {
    rewrite HX3. rewrite HX4. apply Qeq_refl.
  }
  {
    rewrite HY3. rewrite HY4. apply Qeq_refl.
  }
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
