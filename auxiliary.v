Require Import QArith.
Require Import primitives.

(* AUXILIARY FUNCTIONS *)

Fixpoint bezier_curve_init (b : bezier_curve) : bezier_curve :=
  match b with
    | [P0] => [P0]
    | Pi :: [P0] => [Pi]
    | Pi :: b' => Pi :: (bezier_curve_init b')
  end.
  
Fixpoint bezier_curve_tail (b : bezier_curve) : bezier_curve :=
  match b with
    | [P0] => [P0]
    | Pi :: b' => b'
  end.
  
Fixpoint bezier_curve_length (b : bezier_curve) : nat :=
  match b with
    | [P0] => 1%nat
    | P0 :: b' =>  S (bezier_curve_length b')
  end.
  
Fixpoint bezier_curve_head (b : bezier_curve) : point :=
  match b with
    | [P0] => P0
    | P0 :: _ => P0
  end.


(*
  TODO: add some examples
*)

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

Fixpoint app (l r : bezier_curve) : bezier_curve :=
  match l with
  | [h] => h :: r
  | h :: t => h :: app t r
  end.

Infix "++" := app (right associativity, at level 60).

Fixpoint rev (b : bezier_curve) : bezier_curve :=
  match b with
  | [h] => [h]
  | h :: t => (rev t) ++ [h]
  end.  