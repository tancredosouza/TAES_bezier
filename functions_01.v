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

Fixpoint prod_pt_list (n m : nat) : Q :=
  match m with
    | O => inject_Z (Z.of_nat n)
    | S m' => (inject_Z (Z.of_nat (n - m))) * (prod_pt_list n m')
  end.

Fixpoint pow (x : Q) (n : nat) : Q :=
  match n with
    | O => 1
    | S n' => Qmult x (pow x n')
  end.

Definition get_cohefficient (j n : nat) (l : list (prod Q Q) ) : (prod Q Q) :=
  (prod_pt_list n (Nat.pred j)) qp* (sum_pt_list l O j (length l)).

Fixpoint polynomial (t : Q) (j : nat) (l : list (prod Q Q)) : (prod Q Q) :=
  match l with
    | [] => ( 0 , 0 )
    | [a] => a
    | h :: b => (pow t j) qp* h pp+ (polynomial t (S j) b)
  end.
