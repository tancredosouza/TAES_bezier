Add LoadPath "~/Desktop/TAES_bezier".
Require Export primitives.
Require Export List.
Import ListNotations.

(*
  
  
  
  
*)

Fixpoint init {X: Type} (l: list X): list X :=
  match l with
  | []      => []
  | h :: [] => []
  | h :: t  => h :: (init t)
  end.
  
Compute (init [1 # 2; 3 # 2; 3 # 6]).

(*
  Firt approach: purely recursive approach
*)
Fixpoint inner_calc_point_at (b: bezier_curve) (t: Q) (n: nat): option (point) :=
  match b, n with
  | _, 0%nat      => None
  | h :: _, 1%nat => Some h
  | b', S n'      =>
    match inner_calc_point_at (init b') t n', inner_calc_point_at (tl b') t n' with
    | None, _ => None
    | _, None => None
    | Some vl, Some vr => Some (((1 - t) qp* vl) pp+ (t qp* vr))
    end
  end.

Definition calc_bezier_recursive (b: bezier_curve) (t: Q): option (point) :=
  inner_calc_point_at b t (length b).
  
Fixpoint fact_pos (n : nat) : positive :=
  match n with
    | O => 1
    | S n' => (Pos.of_nat n) * (fact_pos n')
  end.

Fixpoint pow (x : Q) (n : nat) : Q :=
  match n with
    | O => 1
    | S n' => Qmult x (pow x n')
  end.

Definition minus_1_sgn (exp : nat) : Q := 
  match (Nat.even exp) with
    | true => 1
    | false => inject_Z (-1)
  end.

Fixpoint calc_summ_pts (i j iter_left : nat) (b : bezier_curve) : option (point) :=
  match iter_left with
    | O => None
    | 1%nat => 
        match b with
          | [] => None
          | Pi :: _ => 
              Some (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi))
        end
    | S iter_left' => 
        match b with
          | [] => None
          | Pi :: b' => 
            match (calc_summ_pts (S i) j iter_left' b') with
              | None => None
              | Some Sj => 
                  Some (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi) pp+ Sj)
            end
        end
    end.

Definition calc_fact_div (n j : nat) : Q :=
  ((Z.of_nat (Pos.to_nat (fact_pos n))) # (fact_pos (n - j))).

Fixpoint calc_Cj (n j : nat) (b : bezier_curve) : option (point) :=
  match (calc_summ_pts 0 j (S j) b) with
    | None => None
    | Some Sj => Some ((calc_fact_div n j) qp* Sj)
  end.

Fixpoint calc_polynomial (b : bezier_curve) (j n deg_left: nat) (t : Q) : option (point) :=
  match deg_left with
    | O => None
    | 1%nat =>
        match (calc_Cj n j b) with
          | None => None
          | Some Cn => Some ((pow t j) qp* Cn)
        end
    | S deg_left' =>
        match (calc_Cj n j b) with
          | None => None
          | Some Ci =>
              match (calc_polynomial b (S j) n deg_left' t) with
                | None => None
                | Some Ck => Some (((pow t j) qp* Ci) pp+ Ck)
              end
        end
  end.

Definition calc_bezier_polynomial (b : bezier_curve) (t : Q) :=
  calc_polynomial b 0 (Nat.pred (length b)) (length b) t.


Compute (calc_bezier_recursive [(0, 1); (0, 0); (1, 0)] (1 # 2)).