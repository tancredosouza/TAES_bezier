Require Export QArith.
Require Import Coq.Setoids.Setoid.


Inductive prod (X Y : Type) : Type :=
  | pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Definition point := prod Q Q.

Notation "( x , y )" := (pair x y).

Definition div_q_pt (l:Q) (r : point) : point := 
  match r with
    | (x, y) => ( (l / x),  (l / y))
  end.

Definition mul_q_pt (l: Q) (r: point): point :=
  match r with
    | (x, y) => ((l * x), (l * y))
  end.

Definition sum_pt (l: point) (r: point): point :=
  match l, r with
  | (xl, yl), (xr, yr) => ((xl + xr), (yl + yr))
  end.

Notation "l qp* r" := (mul_q_pt l r) (at level 74, left associativity).

Notation "l qp/ r" := (div_q_pt l r) (at level 74, left associativity).

Notation "l pp+ r" := (sum_pt l r) (at level 76, left associativity).

Definition pt_x (p : point) : Q :=
  match p with
    | (x, y) => x
  end.

Definition pt_y (p : prod Q Q) : Q :=
  match p with
    | (x, y) => y
  end.
  
Definition eq_pt (p q : point) : Prop :=
  pt_x p == pt_x q /\ pt_y p == pt_y q.
  
Notation "p == q" := (eq_pt p q).

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

Definition bezier_curve := list point.