Require Export functions_01.

Import ListNotations.
Check calc_bezier_polynomial.

(*
  Teorema 1 desse documento aqui

  http://www.ursoswald.ch/metapost/tutorial/BezierDoc/BezierDoc.pdf
*)

Theorem bezier_curve_order_1 : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_recursive b q = Some (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  unfold calc_bezier_recursive. rewrite H. simpl. reflexivity.
Qed.



Theorem bezier_polynomial_recursive_eq : forall (b : bezier_curve) (q : Q),
  calc_bezier_recursive b q = calc_bezier_polynomial b q.
Proof.
  intros b q.
  induction b as [ | h b' ].
  - unfold calc_point_at. unfold calc_bezier_polynomial.
    simpl. reflexivity.
  - unfold calc_bezier_polynomial. unfold calc_point_at. simpl. simpl. destruct (length b').
    +  simpl. unfold minus_1_sgn. simpl. unfold calc_fact_div. simpl.
       repeat (rewrite product_id). reflexivity.
    +  
Admitted.