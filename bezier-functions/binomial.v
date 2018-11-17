Require Import auxiliary.
Require Export primitivedefs.

Require Export List.
Import ListNotations.

Fixpoint inner_calc_bezier_binomial (b : bezier_curve) (q : Q) (j n : nat) : point :=
  match b with
  | [] => (0, 0)
  | h :: [] => ((Zpos (calc_binomial_pos n j)) # 1) * (pow (1 - q) (n - j)) * (pow q j) qp* h
  | h :: t => (inner_calc_bezier_binomial t q (j + 1) n) pp+ ((Zpos (calc_binomial_pos n j)) # 1) * (pow (1 - q) (n - j)) * (pow q j) qp* h
  end.

(* 3. BINOMIAL DEFINITION *)
Definition calc_bezier_binomial (b : bezier_curve) (t: Q) : point :=
  inner_calc_bezier_binomial b t 0 (Nat.pred (length b)).

Compute (calc_bezier_binomial [(0, 1); (0, 0); (1, 0)] (1 # 2)).
