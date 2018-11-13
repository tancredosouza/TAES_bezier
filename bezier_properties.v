Require Export bezier_curve_functiondefs.

Import ListNotations.
Check calc_bezier_polynomial.

(*
  Teorema 1 desse documento aqui

  http://www.ursoswald.ch/metapost/tutorial/BezierDoc/BezierDoc.pdf
*)

Theorem bezier_curve_fst_order_recursive : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_recursive b q = Some (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  unfold calc_bezier_recursive. 
  rewrite H. 
  simpl. reflexivity.
Qed.

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

Lemma aux : forall (h p2: point) (b : bezier_curve) (q : Q),
  calc_polynomial b 0 (Nat.pred (length b)) (length b) q = Some p2 ->
  calc_polynomial (h::b) 0 (Nat.pred (length (h::b))) (length (h::b)) q = Some (h pp+ p2).
Proof.
  intros h p2 b q H1.
  
Qed.
Theorem bezier_polynomial_recursive_eq : forall (b : bezier_curve) (q : Q),
  calc_bezier_recursive b q = calc_bezier_polynomial b q.
Proof. 
  intros b q. 
  unfold calc_bezier_recursive. unfold calc_bezier_polynomial.
  induction b as [ | h b' IHb'].
  + auto.
  + 
Qed.