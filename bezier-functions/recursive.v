Require Import auxiliary.
Require Export primitives.

(*
  inner_calc_point_at: This function implements
  the formal recursive definition of a bezier curve.
  
  Let b = [P0; P1; P2; P3; P4 ... ; Pn]
  B(P0, t) = P0,
  B(t) = (1 - t) * B(init b, t) + t * B(tail b, t) 
  
*)
Fixpoint inner_calc_point_at (b: bezier_curve) (t: Q) (n: nat): point :=
  match b, n with
  | _, 0%nat      => (0 , 0)
  | [h], _ => h
  | h :: b', S n'      =>
     ((1 - t) qp* (inner_calc_point_at (bezier_curve_init b) t n')) pp+ (t qp* (inner_calc_point_at b' t n'))
  end.

(* 1. PURELY RECURSIVE DEFINITION *)
Definition calc_bezier_recursive (b: bezier_curve) (t: Q): (point) :=
  inner_calc_point_at b t (bezier_curve_length b).

Compute (calc_bezier_recursive [(3 # 4, 1 # 3); (3 # 9, 8 # 7); (36 # 72, 40 # 41)] (30 # 42)).

(* --------------------------- *)