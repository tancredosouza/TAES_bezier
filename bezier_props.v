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
  -  
    

Qed.