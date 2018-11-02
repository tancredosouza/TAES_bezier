Add LoadPath "~/Desktop/TAES_bezier".
Require Export functions.

Require Export List.
Import ListNotations.
Require Export Coq.Arith.Factorial.
Require Export BinNums BinPos Pnat.
Require Import BinNat Bool Equalities GenericMinMax
 OrdersFacts ZAxioms ZProperties.
Require BinIntDef.
(*

  https://coq.inria.fr/library/Coq.ZArith.Znat.html

*)

Local Open Scope Z_scope.

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

Fixpoint calc_summ_pts (i j iter_left : nat) (b : bezier_curve) : option (prod Q Q) :=
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

Fixpoint calc_Cj (n j : nat) (b : bezier_curve) : option (prod Q Q) :=
  match (calc_summ_pts 0 j (S j) b) with
    | None => None
    | Some Sj => Some ((calc_fact_div n j) qp* Sj)
  end.

Fixpoint calc_polynomial (b : bezier_curve) (j n deg_left: nat) (t : Q) : option (prod Q Q) :=
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

Compute (calc_point_at [(0, 1); (0, 0); (1, 0)] (1 # 2)).
Compute (calc_bezier_polynomial [(inject_Z 3, inject_Z 2); (inject_Z 4, inject_Z 4); (inject_Z 7, inject_Z 2)] (1 # 2)).