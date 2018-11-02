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

Fixpoint sum_pt_list (b : bezier_curve) (i j count : nat) :  option (prod Q Q) := 
  match count with
    | O => 
        match b with
        | [] => None
        | h :: _ => Some
        (
                                 1
                                 #
                  ((fact_pos i) * (fact_pos (j-i)))
                                  
                                 qp*
                                   
                  (get_sgn (Z.of_nat (i + j)) qp* h)
        )
        end
    | S count' =>
        match b with
        | [] => None
        | h :: t => 
            match sum_pt_list t (S i) j count' with
              | None => None
              | Some vr => Some (
                (
                                       1
                                       #
                        ((fact_pos i) * (fact_pos (j-i)))
                                        
                                       qp*
                                         
                        (get_sgn (Z.of_nat (i + j)) qp* h)
                )
                
                                      pp+
                                    
                                      vr
               )
           end
        end
  end.

Fixpoint prod_n_m (n m : nat) : Q :=
  match m with
    | O => inject_Z (Z.of_nat n)
    | S m' => (inject_Z (Z.of_nat (n - m))) * (prod_n_m n m')
  end.
  
Definition get_cohefficient (n j : nat) (b : bezier_curve) : option (prod Q Q) :=
  match (sum_pt_list b O j j) with
    | None => None
    | Some vr => Some ((prod_n_m n (Nat.pred j)) qp* vr)
  end.

Fixpoint pow (x : Q) (n : nat) : Q :=
  match n with
    | O => 1
    | S n' => Qmult x (pow x n')
  end.

Fixpoint polynomial (t : Q) (j n : nat) (b : bezier_curve) : option (prod Q Q) :=
  match b with
    | [] => None
    | [a] => 
        match get_cohefficient n j b with
          | None => None
          | Some x => Some ((pow t j) qp* x)
        end
    | h :: x => 
        match get_cohefficient n j b, polynomial t (S j) n x with
          | None, _ => None
          | _, None => None
          | Some vl, Some vr =>
              Some ((pow t j) qp* vl pp+ vr)
        end
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
              Some ((1 # (fact_pos i * fact_pos (j - i))) qp* (minus_1_sgn (i + j) qp* Pi))
        end
    | S iter_left' => 
        match b with
          | [] => None
          | Pi :: b' => 
            match (calc_summ_pts (S i) j iter_left' b') with
              | None => None
              | Some Sj => 
                  Some ((1 # (fact_pos i * fact_pos (j - i))) qp* (minus_1_sgn (i + j) qp* Pi))
            end
        end
    end.

Fixpoint calc_Cj (n j : nat) (b : bezier_curve) : option (prod Q Q) :=
  match (calc_summ_pts 0 j (S j) b) with
    | None => None
    | Some Sj => Some (prod_n_m n (Nat.pred j) qp* Sj)
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
                | Some Ck => Some ((pow t j) qp* Ci pp+ Ck)
              end
        end
  end.
  

Compute (calc_polynomial [(0,1)] 0 0 1 (1 # 2)).

Definition calc_bezier_polynomial (b : bezier_curve) (t : Q) :=
  polynomial t 0 (Nat.pred (length b)) b. 
  
Compute (calc_bezier_polynomial [(0, 1); (0, 0); (1, 0)] (1 # 2)).