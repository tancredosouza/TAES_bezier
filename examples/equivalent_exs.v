Add LoadPath "bezier-functions".

Require Import polynomial.
Require Import binomial.
Require Import recursive.

Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Definition l1 := [(3 # 4, 1 # 3); (3 # 9, 8 # 7); (36 # 72, 40 # 41)].

Example ex1_1 : forall (t : Q),
  calc_bezier_recursive l1 t == calc_bezier_polynomial l1 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex1_2 : forall (t : Q),
  calc_bezier_polynomial l1 t == calc_bezier_binomial l1 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex1_3 : forall (t : Q),
  calc_bezier_recursive l1 t == calc_bezier_binomial l1 t.
Proof.
  try rewrite <- ex1_2. 
  (*Trying to use the previous example does not work with setoid...*)
  unfold calc_bezier_recursive.
  unfold calc_bezier_binomial.
  simpl. 
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Definition l2 := [(0, 1); (0, 0); (1, 0)].

Example ex2_1 : forall (t : Q),
  calc_bezier_recursive l2 t == calc_bezier_polynomial l2 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex2_2 : forall (t : Q),
  calc_bezier_polynomial l2 t == calc_bezier_binomial l2 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex2_3 : forall (t : Q),
  calc_bezier_recursive l2 t == calc_bezier_binomial l2 t.
Proof.
  try rewrite <- ex1_2. 
  (*Trying to use the previous example does not work with setoid...*)
  unfold calc_bezier_recursive.
  unfold calc_bezier_binomial.
  simpl. 
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Definition l3 := [(2 # 1, 2 # 1); (1 # 1, 3 # 1); (2 # 1, 4 # 1); (3 # 1, 3 # 1); (2 # 1, 2 # 1)].

Example ex3_1 : forall (t : Q),
  calc_bezier_recursive l3 t == calc_bezier_polynomial l3 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex3_2 : forall (t : Q),
  calc_bezier_polynomial l3 t == calc_bezier_binomial l3 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex3_3 : forall (t : Q),
  calc_bezier_recursive l3 t == calc_bezier_binomial l3 t.
Proof.
  try rewrite <- ex3_2. 
  (*Trying to use the previous example does not work with setoid...*)
  unfold calc_bezier_recursive.
  unfold calc_bezier_binomial.
  simpl. 
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Definition l4 := [(2 # 1, 2 # 1); (2 # 1, 2 # 1); (2 # 1, 2 # 1); (2 # 1, 2 # 1); (2 # 1, 2 # 1)].

Example ex4_1 : forall (t : Q),
  calc_bezier_recursive l4 t == calc_bezier_polynomial l4 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex4_2 : forall (t : Q),
  calc_bezier_polynomial l4 t == calc_bezier_binomial l4 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex4_3 : forall (t : Q),
  calc_bezier_recursive l4 t == calc_bezier_binomial l4 t.
Proof.
  try rewrite <- ex4_2. 
  (*Trying to use the previous example does not work with setoid...*)
  unfold calc_bezier_recursive.
  unfold calc_bezier_binomial.
  simpl. 
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Definition l5 := [(-4 # 1, 1 # 1); (-3 # 1, 2 # 1); (1 # 1, 2 # 1); (-2 # 1, -1 # 1); (1 # 1, -1 # 1); (2 # 1, -2 # 1); (2 # 1, -3 # 1); (-1 # 1, -3 # 1)].

Example ex5_1 : forall (t : Q),
  calc_bezier_recursive l5 t == calc_bezier_polynomial l5 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex5_2 : forall (t : Q),
  calc_bezier_polynomial l5 t == calc_bezier_binomial l5 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex5_3 : forall (t : Q),
  calc_bezier_recursive l5 t == calc_bezier_binomial l5 t.
Proof.
  try rewrite <- ex5_2. 
  (*Trying to use the previous example does not work with setoid...*)
  unfold calc_bezier_recursive.
  unfold calc_bezier_binomial.
  simpl. 
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Definition l6 := [(0, 0)].

Example ex6_1 : forall (t : Q),
  calc_bezier_recursive l6 t == calc_bezier_polynomial l6 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex6_2 : forall (t : Q),
  calc_bezier_polynomial l6 t == calc_bezier_binomial l6 t.
Proof.
  unfold calc_bezier_recursive.
  unfold calc_bezier_polynomial.
  simpl. 
  unfold calc_fact_div; unfold minus_1_sgn; unfold inject_Z; unfold fact_pos.
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

Example ex6_3 : forall (t : Q),
  calc_bezier_recursive l6 t == calc_bezier_binomial l6 t.
Proof.
  try rewrite <- ex6_2. 
  (*Trying to use the previous example does not work with setoid...*)
  unfold calc_bezier_recursive.
  unfold calc_bezier_binomial.
  simpl. 
  unfold "==".
  simpl. split. 
  {
    ring.
  }
  {
    ring.
  }
Qed.

