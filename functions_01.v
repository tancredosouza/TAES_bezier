Add LoadPath "~/Desktop/TAES_bezier".
Require Export functions.

Require Export List.
Import ListNotations.
Require Export Coq.Arith.Factorial.
Require Export BinNums BinPos Pnat.
Require Import BinNat Bool Equalities GenericMinMax
 OrdersFacts ZAxioms ZProperties.
Require BinIntDef.


Local Open Scope Z_scope.

Fixpoint fact_Z (n : nat) : Z :=
  match n with
    | O => 1
    | S n' => (Z.of_nat n) * (fact_Z n')
  end.

Compute (fact_Z 13).

Definition get_sgn (k : nat) : Q :=
  match Nat.even k with
    | true => 1
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
            (1 # (Pos.of_nat (fact i * fact (j-i))))
                                qp/ 
                      (get_sgn (i + j) qp* h)
          )
          pp+
          (
            sum_pt_list t (S i) j count'
          )
        end
  end.
