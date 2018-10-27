Add LoadPath "~/Desktop/TAES_bezier".
Require Export functions.

Require Export List.
Import ListNotations.
Require Export Coq.Arith.Factorial.

Require Import PeanoNat.

Fixpoint sum_pt_list (l : list (prod Q Q)) (i j count : nat): (prod Q Q) := 
  match count with
    | O => (0,0) 
    | S count' =>
        match l with
        | [] => (0, 0)
        | h :: t => 
          (
            (
              1 # (Pos.of_nat (fact i * fact (j-i))))
                                qp/ 
                                h
          )
           
          pp+ 
          
          (
            sum_pt_list t (S i) j count'
          )
        end
  end.
  
  
