Module Primitives.
Require Export Reals.

Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.
  
Inductive point (x : R) (y : R) : Type :=
  | coord : R -> R -> point x y.

Notation "( x , y )" := (point x y).

Compute (point (3/5) (5/7)).

Compute ((3/5),(5/7)).

End Primitives.