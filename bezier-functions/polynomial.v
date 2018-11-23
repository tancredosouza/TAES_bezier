
Add LoadPath "bezier-functions".
Add LoadPath "properties/fst_order_interpolation".

Require Import auxiliary.
Require Export primitives.

(*
  calc_summ_pts : Given a list of points,
      calculate the summation for a Cj.
      This is necessary for the polynomial
      definition.
      
              j
            ----
            \     (-1)^(i + j) * Pi
     Sj =    >    -----------------
            /        i! (j - i)!
            ----
            i = 0
*)
Fixpoint calc_summ_pts (i j iter_left : nat) (b : bezier_curve) : (point) :=
  match iter_left with
    | O => (0, 0)
    | 1%nat => 
        match b with
          | [Pi] => 
              (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi))
          | Pi :: _ =>
              (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi))
        end
    | S iter_left' => 
        match b with
          | [Pi] => 
              (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi))
          | Pi :: b' => 
            match (calc_summ_pts (S i) j iter_left' b') with
              | Sj => 
                  (1 # (fact_pos i * fact_pos (j - i)) qp* (minus_1_sgn (i + j) qp* Pi) pp+ Sj)
            end
        end
    end.

(*
   calc_fact_div : Given two naturals n j,
    returns 
               n!
       Mj  = --------
             (n - j)!
    This is necessary for the polynomial
      definition.
*)
Definition calc_fact_div (n j : nat) : Q :=
  ((Z.of_nat (Pos.to_nat (fact_pos n))) # (fact_pos (n - j))).


(*
  calc_Cj : This function returns Cj, 
  necessary for the polynomial definition.
  
  
          Cj = Mj * Sj
*)
Fixpoint calc_Cj (n j : nat) (b : bezier_curve) : (point) :=
  match (calc_summ_pts 0 j (S j) b) with
    | Sj => ((calc_fact_div n j) qp* Sj)
  end.

(*
  calc_polynomial : This function returns a point
  in a bezier curve defined polynomially.
  
  
              n
            ----
            \
     B(t) =  >    t^j * Cj
            /
            ----
            j = 0
*)
Fixpoint calc_polynomial (b : bezier_curve) (j n deg_left: nat) (t : Q) : (point) :=
  match deg_left with
    | O => (0,0)
    | 1%nat =>
        match (calc_Cj n j b) with
          | Cn => ((pow t j) qp* Cn)
        end
    | S deg_left' =>
        match (calc_Cj n j b) with
          | Ci =>
              match (calc_polynomial b (S j) n deg_left' t) with
                | Ck => (((pow t j) qp* Ci) pp+ Ck)
              end
        end
  end.


(* 2. POLYNOMIAL DEFINITION *)
Definition calc_bezier_polynomial (b : bezier_curve) (t : Q) :=
  calc_polynomial b 0 (Nat.pred (bezier_curve_length b)) (bezier_curve_length b) t.

Compute (calc_bezier_polynomial [(0, 1); (0, 0); (1, 0)] (1 # 2)).


Definition l1 := [(1 # 2, 4 # 8); (1 # 2, 4 # 8); (3 # 4, 4 # 7); (8 # 7, 10 # 11)].

Compute (calc_bezier_polynomial [(0, 1); (0, 0); (1, 0)] (1 # 2)).

Compute (calc_bezier_polynomial l1 (1 # 2)).
Compute (calc_bezier_polynomial (rev l1) (1 # 2)).