Require Export Reals.

Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Definition point (x y: R): prod R R := pair x y.
Check 1/2.
Check (point (1/2) (2/4)).