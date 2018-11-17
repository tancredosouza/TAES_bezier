(*
              IF722

  PRIMITIVE DEFINITIONS
  Authors: NETO, Divino and SOUZA, Tancredo
  
  This file defines cartesian products,
  points and some basic lemmas.
  
*)

Require Export QArith.
Require Import Coq.Setoids.Setoid.


(* 
  Cartesian product definition
*)
Inductive prod (X Y : Type) : Type :=
  | pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.


(*
   A point is defined as the
   cartesian product Q x Q
*)
Definition point := prod Q Q.

Notation "( x , y )" := (pair x y).

(*
  Divide a point by a (q : Q) constant
*)
Definition div_q_pt (l:Q) (r : point) : point := 
  match r with
    | (x, y) => ( (l / x),  (l / y))
  end.

(*
  Multiply a point by a (q : Q) constant
*)
Definition mul_q_pt (l: Q) (r: point): point :=
  match r with
    | (x, y) => ((l * x), (l * y))
  end.

(*
  Sum of two points
*)
Definition sum_pt (l: point) (r: point): point :=
  match l, r with
  | (xl, yl), (xr, yr) => ((xl + xr), (yl + yr))
  end.


(*
  Some notations
*)
Notation "l qp* r" := (mul_q_pt l r) (at level 74, left associativity).
Notation "l qp/ r" := (div_q_pt l r) (at level 74, left associativity).
Notation "l pp+ r" := (sum_pt l r) (at level 76, left associativity).

(*
  Accessing point coordinates
          (x, y)
*)
Definition pt_x (p : point) : Q :=
  match p with
    | (x, y) => x
  end.
Definition pt_y (p : prod Q Q) : Q :=
  match p with
    | (x, y) => y
  end.


(*
  Definition of point equality
*)
Definition eq_pt (p q : point) : Prop :=
  pt_x p == pt_x q /\ pt_y p == pt_y q.
  
Definition eq_opt_pt (opt_p opt_q : option point) : Prop :=
  match opt_p, opt_q with
    | None, None => True
    | None, _ => False
    | _, None => False
    | Some p, Some q => pt_x p == pt_x q /\ pt_y p == pt_y q
   end.

Definition beq_pt (p q : point) : bool :=
  match Qeq_bool (pt_x p) (pt_x q), Qeq_bool (pt_y p) (pt_y q) with
    | false, _ => false
    | _, false => false
    | true, true => true
  end.
  
Notation "p == q" := (eq_pt p q).
Notation "p ?= q" := (beq_pt p q).

  
(*

    PROOF OF SOME BASIC THEOREMS

*)

Theorem pp_0_l : forall (p : point),
  ((0,0) pp+ p) == p.
Proof.
  intros p. destruct p as [a b].
  unfold "==". split. 
  + simpl. Search (0 + _). apply Qplus_0_l.
  + simpl. Search (0 + _). apply Qplus_0_l.
Qed.

Theorem qp_1_l : forall (p : point),
  (1 qp* p) == p.
Proof.
  intros p. destruct p as [ a b ].
  unfold eq_pt. split.
  + simpl. apply Qmult_1_l.
  + simpl. apply Qmult_1_l.
Qed.

Theorem qp_0_l : forall (p : point),
  (0 qp* p) == (0, 0).
Proof. 
  intros p. destruct p as [a b].
  unfold eq_pt. split.
  + simpl. apply Qmult_0_l.
  + simpl. apply Qmult_0_l.
Qed.


Theorem qp_mult_null_pt : forall (q : Q),
  (q qp* (0, 0)) == (0, 0).
Proof.
  intros q.
  unfold "==". simpl. split.
  - apply Qmult_0_r.
  - apply Qmult_0_r.
Qed.


Theorem eq_pt_refl : forall (p : point),
  p == p.
Proof.
  intros p. destruct p as [x y].
  unfold "==". split.
  - simpl. apply Qeq_refl.
  - simpl. apply Qeq_refl.
Qed.

Definition bezier_curve := list point.
