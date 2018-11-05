Require Export QArith.

Inductive prod (X Y : Type) : Type :=
  | pair: X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Definition point (x y: Q) := pair x y.

Notation "( x , y )" := (point x y).

Definition div_q_pt (l:Q) (r : prod Q Q) : prod Q Q := 
  match r with
    | pair x y => ((Qred (l / x), Qred (l / y)))
  end.

Definition mul_q_pt (l: Q) (r: prod Q Q): prod Q Q :=
  match r with
    | pair x y => ((l * x), (l * y))
  end.

Definition sum_pt (l: prod Q Q) (r: prod Q Q): prod Q Q :=
  match l, r with
  | pair xl yl, pair xr yr => (Qred(xl + xr), Qred(yl + yr))
  end.

Notation "l qp* r" := (mul_q_pt l r) (at level 74, left associativity).

Notation "l qp/ r" := (div_q_pt l r) (at level 74, left associativity).

Notation "l pp+ r" := (sum_pt l r) (at level 76, left associativity).

Definition pt_fst (p : prod Q Q) : Q :=
  match p with
    | pair a b => a
  end.

Definition pt_snd (p : prod Q Q) : Q :=
  match p with
    | pair a b => b
  end.

Definition eq_pt (p q : prod Q Q) : bool :=
  match Qeq_bool (pt_fst p) (pt_fst q) with
    | false => false
    | true => 
      match Qeq_bool (pt_snd p) (pt_snd q) with
        | false => false
        | true => true
      end
  end.

Lemma Qmult_1_l' : forall (q : Q), 1 * q = q.
Proof.
Admitted.

Compute (Qeq_bool (1 * (inject_Z 3)) (inject_Z 3)).

Lemma product_id : forall (p : prod Q Q),
  eq_pt p (1 qp* p) = true.
Proof.
  intros p. destruct p as [ a b ].
  simpl. unfold point. rewrite Qmult_1_l'. rewrite Qmult_1_l'. unfold eq_pt. simpl.
  rewrite Qeq_bool_refl. rewrite Qeq_bool_refl. reflexivity.
Qed.


Definition bezier_curve := list (prod Q Q).