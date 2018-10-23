Require Export QArith.

Inductive prod (X Y : Type) : Type :=
  | pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Definition point (x y: Q) := pair x y.

Notation "( x , y )" := (point x y).


Definition mul_q_pt (l: Q) (r: prod Q Q): prod Q Q :=
match r with
| pair x y => (Qred (l * x), Qred(l * y))
end.

Definition sum_pt (l: prod Q Q) (r: prod Q Q): prod Q Q :=
  match l, r with
  | pair xl yl, pair xr yr => (Qred(xl + xr), Qred(yl + yr))
  end.

Notation "l qp* r" := (mul_q_pt l r) (at level 76, left associativity).

Notation "l pp+ r" := (sum_pt l r) (at level 24, left associativity).

Definition bezier_curve := list (prod Q Q).