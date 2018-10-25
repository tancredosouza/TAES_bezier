Add LoadPath "~/Desktop/TAES_bezier".
Require Export primitives.
Require Export functions.

Require Export List.
Import ListNotations.
Require Export Coq.Arith.Factorial.

Fixpoint sum_pt_list (l : list (prod Q Q)) (i j : nat): (prod Q Q) := 
  if (beq_nat i j) 
    then (0,0) 
  else 
      match l with
        | [] => (0, 0)
        | h :: t => (div_q_pt h ((fact i) * (fact (j-i)))) pp+ (sum_pt_list t (S i) j)
      end.