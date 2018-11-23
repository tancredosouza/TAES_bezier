Require Import auxiliary.
Require Export primitives.

Fixpoint inner_calc_bezier_binomial (b : bezier_curve) (q : Q) (j n : nat) : point :=
  match b with
  | [h] => ((Zpos (calc_binomial_pos n j)) # 1) * (pow (1 - q) (n - j)) * (pow q j) qp* h
  | h :: t => (inner_calc_bezier_binomial t q (j + 1) n) pp+ ((Zpos (calc_binomial_pos n j)) # 1) * (pow (1 - q) (n - j)) * (pow q j) qp* h
  end.

(* 3. BINOMIAL DEFINITION *)
Definition calc_bezier_binomial (b : bezier_curve) (t: Q) : point :=
  inner_calc_bezier_binomial b t 0 (Nat.pred (bezier_curve_length b)).

Compute (calc_bezier_binomial [(0, 1); (0, 0); (1, 0)] (1 # 2)).
Compute (calc_bezier_binomial [(3 # 4, 1 # 3); (3 # 9, 8 # 7); (36 # 72, 40 # 41)] (30 # 42)).
