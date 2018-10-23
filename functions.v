Require Export primitives.
Require Export List.
Import ListNotations.

Fixpoint ant_tail {X: Type} (l: list X): list X :=
  match l with
  | []      => []
  | h :: [] => []
  | h :: t  => h :: (ant_tail t)
  end.
  
Compute (ant_tail [1 # 2; 3 # 2; 3 # 6]).

(*
  Firt approach: purely recursive approach
*)
Fixpoint inner_calc_point_at (b: bezier_curve) (t: Q) (n: nat): option (prod Q Q) :=
  match b, n with
  | _, 0%nat      => None
  | h :: _, 1%nat => Some h
  | b', S n'      =>
    match inner_calc_point_at (ant_tail b') t n', inner_calc_point_at (tl b') t n' with
    | None, _ => None
    | _, None => None
    | Some vl, Some vr => Some (((1 - t) qp* vl) pp+ (t qp* vr))
    end
  end.

Definition calc_point_at (b: bezier_curve) (t: Q): option (prod Q Q) :=
  inner_calc_point_at b t (length b).

Compute (calc_point_at [(0, 1); (0, 0); (1, 0)] (1 # 2)).