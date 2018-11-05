Require Export functions_01.

Import ListNotations.
Check calc_bezier_polynomial.
Check calc_point_at.


Theorem bezier_polynomial_recursive_eq : forall (b : bezier_curve) (q : Q),
  calc_point_at b q = calc_bezier_polynomial b q.
Proof.
  intros b q.
  induction b as [ | h b' ].
  - unfold calc_point_at. unfold calc_bezier_polynomial.
    simpl. reflexivity.
  - unfold calc_bezier_polynomial. unfold calc_point_at. simpl. simpl. destruct (length b').
    +  simpl. unfold minus_1_sgn. simpl. unfold calc_fact_div. simpl.
       repeat (rewrite product_id). reflexivity.
    +  
       
       

Qed.