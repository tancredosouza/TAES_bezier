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
    | S n' => (Pos.of_nat n) * (fact_Z n')
  end.

Compute (fact_pos 13).

Definition get_sgn (k : Z) : Q :=
  match (Z.even k) with
    | true => 1%Q
    | false => inject_Z (Z.opp 1)
  end.

Fixpoint sum_pt_list (l : list (prod Q Q)) (i j count : nat) : (prod Q Q) := 
  match count with
    | O => (0,0) 
    | S count' =>
        match l with
        | [] => (0, 0)
        | h :: t => 
          (
            (1 # (fact_pos i * fact_pos (j-i)))
                                qp/ 
                      (get_sgn (Z.of_nat (i + j)) qp* h)
          )
          pp+
          (
            sum_pt_list t (S i) j count'
          )
        end
  end.
