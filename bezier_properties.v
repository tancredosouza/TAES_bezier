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

Lemma bezier_curve_recursive_symm_fstdegree : 
  forall (b : bezier_curve) (P0 P1 : point) (q : Q),
    b = [P0; P1] -> 
      calc_bezier_recursive b q == calc_bezier_recursive (rev b) (1 - q).
Proof.
  intros b P0 P1 q H.
  apply (bezier_curve_fst_order_recursive b P0 P1 q) in H as H1.
  apply (bezier_curve_fst_order_recursive_rev b P0 P1 q) in H as H2.
  
  destruct (calc_bezier_recursive b q) as [ x3 y3 ].
  destruct (calc_bezier_recursive (rev b) (1 - q)) as [ x4 y4 ].
  
  destruct P0 as [ x0 y0 ]. destruct P1 as [ x1 y1 ].
  assert (HX3 : Qeq x3 ((1 - q) * x0 + q * x1)).
  {
    unfold "==" in H1. destruct H1 as [Ha Hb].
    simpl in Ha. apply Ha.
  }
  assert (HX4 : Qeq x4 ((1 - q) * x0 + q * x1)).
  {
    unfold "==" in H2. destruct H2 as [Ha Hb].
    simpl in Ha. apply Ha.
  }
  assert (HY3 : Qeq y3 ((1 - q) * y0 + q * y1)).
  {
    unfold "==" in H1. destruct H1 as [Ha Hb].
    simpl in Hb. apply Hb.
  }
  assert (HY4 : Qeq y4 ((1 - q) * y0 + q * y1)).
  {
    unfold "==" in H2. destruct H2 as [Ha Hb].
    simpl in Hb. apply Hb.
  }
  
  unfold "==". simpl. split.
  {
    rewrite HX3. rewrite HX4. apply Qeq_refl.
  }
  {
    rewrite HY3. rewrite HY4. apply Qeq_refl.
  }
Qed.

Theorem bezier_curve_recursive_symm : forall (b b' : bezier_curve) (P0 P1 : point) (q : Q),
  b = [P0; P1] ++ b' -> calc_bezier_recursive b q == calc_bezier_recursive (rev b) (1 - q).
Proof.
  intros b b'.
  induction b'.
  {
    intros P0 P1 q H1.
    simpl in H1.
    apply (bezier_curve_recursive_symm_fstdegree b P0 P1 q) in H1 as Hsymm_basecase.
    assumption. 
  }
  {
    intros P0 P1 q H1. rewrite H1. simpl. 
    unfold calc_bezier_recursive.
  }
Admitted.
