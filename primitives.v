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

End Primitives.