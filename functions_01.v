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

Fixpoint sum_pt_list (b : bezier_curve) (i j count : nat) : (prod Q Q) := 
  match count with
    | O => 
        match b with
        | [] => (0, 0)
        | h :: t => h
        end
    | S count' =>
        match b with
        | [] => (0, 0)
        | h :: t => 
          (
                                 1
                                 #
                  ((fact_pos i) * (fact_pos (j-i)))
                                  
                                 qp*
                                   
                  (get_sgn (Z.of_nat (i + j)) qp* h)
          )
          pp+
          (
            sum_pt_list t (S i) j count'
          )
        end
  end.

Fixpoint prod_n_m (n m : nat) : Q :=
  match m with
    | O => inject_Z (Z.of_nat n)
    | S m' => (inject_Z (Z.of_nat (n - m))) * (prod_n_m n m')
  end.
  
Definition get_cohefficient (n j : nat) (b : bezier_curve) : (prod Q Q) :=
  (prod_n_m n (Nat.pred j)) qp* (sum_pt_list b O j j).

Fixpoint pow (x : Q) (n : nat) : Q :=
  match n with
    | O => 1
    | S n' => Qmult x (pow x n')
  end.

Fixpoint polynomial (t : Q) (j n : nat) (b : bezier_curve) : (prod Q Q) :=
  match b with
    | [] => ( 0 , 0 )
    | h :: x => (pow t j) qp* (get_cohefficient n j b) pp+ (polynomial t (S j) n x)
  end.

Definition calc_bezier_polynomial (b : bezier_curve) (t : Q) :=
  polynomial t 0 (Nat.pred (length b)) b. 
  
Compute (calc_bezier_polynomial [(0, 1); (0, 0); (1, 0)] (1 # 2)).
