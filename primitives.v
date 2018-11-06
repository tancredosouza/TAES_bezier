Require Export QArith.

Inductive prod (X Y : Type) : Type :=
  | pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Definition point := prod Q Q.

Notation "( x , y )" := (pair x y).

Definition div_q_pt (l:Q) (r : point) : point := 
  match r with
    | (x, y) => ((Qred (l / x), Qred (l / y)))
  end.

Definition mul_q_pt (l: Q) (r: point): point :=
  match r with
    | (x, y) => ((l * x), (l * y))
  end.

Definition sum_pt (l: point) (r: point): point :=
  match l, r with
  | (xl, yl), (xr, yr) => (Qred(xl + xr), Qred(yl + yr))
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

Definition beq_pt (p q : point) : bool :=
  match Qeq_bool (pt_x p) (pt_x q), Qeq_bool (pt_y p) (pt_y q) with
    | false, _ => false
    | _, false => false
    | true, true => true
  end.

Lemma Qmult_1_l' : forall (q : Q), 1 * q = q.
Proof.
Admitted.

Theorem qp_1_l : forall (p : point),
  (1 qp* p) = p.
Proof.
  intros p. destruct p as [ a b ].
  simpl. 
  rewrite Qmult_1_l'. rewrite Qmult_1_l'.  
  reflexivity.
Qed.

Definition bezier_curve := list point.