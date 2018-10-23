Require Export QArith_base.

Module Primitives.
  
Inductive prod (X Y : Type) : Type :=
  | pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Definition point (x y: Q) := pair x y.

Notation "( x , y )" := (point x y).

Definition bezier_curve := list (prod Q Q).

End Primitives.