Add LoadPath "bezier-functions".

Require Import recursive.
Import ListNotations.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

(*
  Teorema 1 desse documento aqui

  http://www.ursoswald.ch/metapost/tutorial/BezierDoc/BezierDoc.pdf
*)

Theorem bezier_curve_fst_order_interpolation_recursive : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_recursive b q == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  unfold calc_bezier_recursive. 
  rewrite H. 
  simpl. (* apply eq_pt_refl. *)
Admitted.

Theorem bezier_curve_fst_order_interpolation_recursive_rev : forall (b : bezier_curve) (P0 P1 : point) (q : Q), 
  b = [P0; P1] -> calc_bezier_recursive (rev b) (1 - q) 
    == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros b P0 P1 q H.
  rewrite H. simpl. unfold calc_bezier_recursive. simpl.
  destruct P1 as [x1 y1]. destruct P0 as [x0 y0]. unfold "==". 
  simpl. split. 
  - ring.
  - ring.
Qed.