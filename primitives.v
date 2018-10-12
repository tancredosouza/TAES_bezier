Require Export Reals.

Module Primitives.
Local Open Scope R.
  
Inductive coord (X Y : Type) : Type :=
  | point : X -> Y -> coord X Y.

Arguments point {X} {Y} _ _.

Notation "( x , y )" := (point x y).
Notation " X * Y" := (prod X Y) : type_scope.

Compute (point (3/5) (5/7)).

Compute ( 3/5 , 5/7 ).

Definition get_x (p : coord R R) : R := 
  match p with
    | ( a , b ) => a
  end.

Definition get_y (p : coord R R) : R := 
  match p with
    | ( a , b ) => b
  end.

Example test_coord_eq1 :
  get_x (3/5 , 7/2) = 3/5.
Proof. simpl. reflexivity. Qed.

Example test_coord_eq2 :
  get_y (3/5 , 0) = 0.
Proof. simpl. reflexivity. Qed.

Definition sum_pts (p q : coord R R) : (coord R R) :=
  match p, q with
    | (a , b) , (c , d) => (a + c, b + d)
  end.
  
Notation " x p+ y " := (sum_pts x y) (at level 60, right associativity).

(* Não consegui somar os valores de R.. Que biblioteca estranha :S *)
Example test_sum1 :
  (3/5 , 7/2) p+ (1/5 , 1) = (4/5, 9/2).
Proof. simpl. try reflexivity. Abort.

Example test_sum2 :
  (3/5 , 7/2) p+ (1/5 , 2/2) = (4/5, 9/2).
Proof. simpl. reflexivity. Qed.


End Primitives.