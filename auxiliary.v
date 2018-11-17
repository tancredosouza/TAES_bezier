Require Import QArith.
Require Export List.
Import ListNotations.

(* AUXILIARY FUNCTIONS *)

(* 
  init: Given a list of type X,
  this function returns the whole 
  list except for the last element.
 *)
Fixpoint init {X: Type} (l: list X): list X :=
  match l with
  | []      => []
  | h :: [] => []
  | h :: t  => h :: (init t)
  end.

Compute (init [1 # 2; 3 # 2; 3 # 6]).

(*
  fact_pos : Given a natural n,
              returns n! as a positive
              
  This function is necessary due to Coq's
  recursive definition of a natural number,
  which easily causes a 'stack overflow'
  for larger computations.
*)
Fixpoint fact_pos (n : nat) : positive :=
  match n with
    | O => 1
    | S n' => (Pos.of_nat n) * (fact_pos n')
  end.

(*
  pow : Given a natural n and a rational q,
              returns q^n as a rational.
*)
Fixpoint pow (x : Q) (n : nat) : Q :=
  match n with
    | O => 1
    | S n' => Qmult x (pow x n')
  end.

(*
  minus_1_sgn : Given a natural exp,
              returns (-1)^exp.
*)
Definition minus_1_sgn (exp : nat) : Q := 
  match (Nat.even exp) with
    | true => 1
    | false => inject_Z (-1)
  end.

Fixpoint calc_binomial_pos (n p : nat) : positive :=
  match p with
  | O => 1%positive
  | S p' =>
      match Nat.eqb n p with
      | true => 1%positive
      | false =>
          match n with
          | S n' => (calc_binomial_pos n' p') + (calc_binomial_pos n' (S p'))
          | _ => 1%positive
          end
      end
  end.