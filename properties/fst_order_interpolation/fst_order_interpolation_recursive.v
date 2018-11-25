Add LoadPath "bezier-functions".

Require Import recursive.
Require Import auxiliary.
Require Import QArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

(*
  Teorema 1 desse documento aqui

  http://www.ursoswald.ch/metapost/tutorial/BezierDoc/BezierDoc.pdf
*)

Theorem bezier_curve_fst_order_interpolation_recursive : forall (P0 P1 : point) (q : Q), 
  calc_bezier_recursive (P0 :: [P1]) q == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros P0 P1 q.
  unfold calc_bezier_recursive.
  simpl.
  apply eq_pt_refl.
Qed.

Theorem bezier_curve_fst_order_interpolation_recursive_rev : forall (P0 P1 : point) (q : Q), 
  calc_bezier_recursive (rev (P0 :: [P1])) (1 - q) == (((1 - q) qp* P0) pp+ (q qp* P1)).
Proof.
  intros P0 P1 q.
  simpl. unfold calc_bezier_recursive. simpl.
  destruct P1 as [x1 y1]. destruct P0 as [x0 y0]. unfold "==". 
  simpl. split. 
  - ring.
  - ring.
Qed.