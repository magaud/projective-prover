From Tuto0 Require Export Loader.
Require Import Ltac_utils.

(* Pappus -> DG *)

Lemma Pappus2DG : 
forall Oo A B C Ap Bp Cp X Y Z M N Sp T U V R,
 rk(Oo :: A :: nil) = 2 -> rk(Oo :: B :: nil) = 2 
-> rk(A :: B :: nil) = 2 -> rk(Oo :: C :: nil) = 2 
-> rk(A :: C :: nil) = 2 -> rk(B :: C :: nil) = 2 
-> rk(Oo :: A :: B :: C :: nil) = 2     (* line a*)
-> rk(Oo :: Ap :: nil) = 2  
-> rk(Oo :: A :: Ap :: nil) = 3         (* a != e*)
-> rk(Oo :: Bp :: nil) = 2 
-> rk(Ap :: Bp :: nil) = 2
-> rk(Oo :: Cp :: nil) = 2 
-> rk(Ap :: Cp :: nil) = 2 
-> rk(Bp :: Cp :: nil) = 2 ->
rk(Oo :: Ap :: Bp :: Cp :: nil) = 2     (* line e*)
-> rk(B :: Ap :: X :: nil) = 2 (* Pappus point X *)  
-> rk(A :: Bp :: X :: nil) = 2
-> rk(C :: Ap :: Y :: nil) = 2 (* Pappus point Y *) 
-> rk(A :: Cp :: Y :: nil) = 2
-> rk(C :: Bp :: Z :: nil) = 2 (* Pappus point Z *)
-> rk(B :: Cp :: Z :: nil) = 2
-> rk(X :: Y :: Z :: nil) = 2    (* Pappus prop. *)
-> rk(Ap :: M :: Sp :: nil) = 2 ->     (* line b *)
rk(Oo :: A :: B :: C :: Ap :: M :: Sp :: nil) = 4
-> rk(Bp :: N :: T :: nil) = 2 ->      (* line c *)
rk(Oo :: A :: B :: C :: Bp :: N :: T :: nil) = 4 
-> rk(C :: Sp :: T :: nil) = 2 ->      (* line d *)
rk(Oo :: C :: Ap :: Bp :: Cp :: Sp :: T :: nil) = 4
-> rk(Ap :: Bp :: M :: N :: Sp :: T :: nil) = 4
-> rk(A :: M :: U :: nil) = 2 ->       (* line f *)
rk(Oo :: A :: Ap :: Bp :: Cp :: M :: U :: nil) = 4
-> rk(A :: C :: M :: Sp :: T :: U :: nil) = 4
-> rk(B :: N :: V :: nil) = 2 ->       (* line g *)
rk(Oo :: B :: Ap :: Bp :: Cp :: N :: V :: nil) = 4 
-> rk(B :: C :: N :: Sp :: T :: V :: nil) = 4 
-> rk(Cp :: U :: V :: nil) = 2         (* line h *)
-> rk(Oo :: A :: B :: C :: Cp :: U :: V :: nil) = 4
-> rk(A :: B :: M :: N :: U :: V :: nil) = 4 
-> rk(Ap :: Cp :: M :: Sp :: U :: V :: nil) = 4
-> rk(Bp :: Cp :: N :: T :: U :: V :: nil) = 4 
-> rk(Y :: M :: R :: nil) = 2         (* point R *)
-> rk(Z :: N :: R :: nil) = 2 
->                                  (*coplanarity*)
rk(C :: Cp :: Sp :: T :: U :: V :: nil) = 3.
Proof.
  intros.
(*  pprove.*)
  Require Import pprove_Pappus2DG_347.
  solve_using LP4P7P13P14P15P16.
Qed.
Check Pappus2DG.


Lemma Pappus2DG_noXYZ : 
forall Oo A B C Ap Bp Cp M N Sp T U V, 
 rk(Oo :: A :: nil) = 2 -> rk(Oo :: B :: nil) = 2 
-> rk(A :: B :: nil) = 2 -> rk(Oo :: C :: nil) = 2 
-> rk(A :: C :: nil) = 2 -> rk(B :: C :: nil) = 2 
-> rk(Oo :: A :: B :: C :: nil) = 2     (* line a*)
-> rk(Oo :: Ap :: nil) = 2  
-> rk(Oo :: A :: Ap :: nil) = 3         (* a != e*)
-> rk(Oo :: Bp :: nil) = 2 
-> rk(Ap :: Bp :: nil) = 2
-> rk(Oo :: Cp :: nil) = 2 
-> rk(Ap :: Cp :: nil) = 2 
-> rk(Bp :: Cp :: nil) = 2 ->
rk(Oo :: Ap :: Bp :: Cp :: nil) = 2     (* line e*)
(*-> rk(B :: Ap :: X :: nil) = 2 (* Pappus point X *)  
-> rk(A :: Bp :: X :: nil) = 2
-> rk(C :: Ap :: Y :: nil) = 2 (* Pappus point Y *) 
-> rk(A :: Cp :: Y :: nil) = 2
-> rk(C :: Bp :: Z :: nil) = 2 (* Pappus point Z *)
-> rk(B :: Cp :: Z :: nil) = 2
-> rk(X :: Y :: Z :: nil) = 2    (* Pappus prop. *)*)
-> rk(Ap :: M :: Sp :: nil) = 2 ->     (* line b *)
rk(Oo :: A :: B :: C :: Ap :: M :: Sp :: nil) = 4
-> rk(Bp :: N :: T :: nil) = 2 ->      (* line c *)
rk(Oo :: A :: B :: C :: Bp :: N :: T :: nil) = 4 
-> rk(C :: Sp :: T :: nil) = 2 ->      (* line d *)
rk(Oo :: C :: Ap :: Bp :: Cp :: Sp :: T :: nil) = 4
-> rk(Ap :: Bp :: M :: N :: Sp :: T :: nil) = 4
-> rk(A :: M :: U :: nil) = 2 ->       (* line f *)
rk(Oo :: A :: Ap :: Bp :: Cp :: M :: U :: nil) = 4
-> rk(A :: C :: M :: Sp :: T :: U :: nil) = 4
-> rk(B :: N :: V :: nil) = 2 ->       (* line g *)
rk(Oo :: B :: Ap :: Bp :: Cp :: N :: V :: nil) = 4 
-> rk(B :: C :: N :: Sp :: T :: V :: nil) = 4 
-> rk(Cp :: U :: V :: nil) = 2         (* line h *)
-> rk(Oo :: A :: B :: C :: Cp :: U :: V :: nil) = 4
-> rk(A :: B :: M :: N :: U :: V :: nil) = 4 
-> rk(Ap :: Cp :: M :: Sp :: U :: V :: nil) = 4
-> rk(Bp :: Cp :: N :: T :: U :: V :: nil) = 4 
(*-> rk(Y :: M :: R :: nil) = 2         (* point R *)
-> rk(Z :: N :: R :: nil) = 2 *)
->                                  (*coplanarity*)
rk(C :: Cp :: Sp :: T :: U :: V :: nil) = 3.
Proof.
intros.
Check rk_pappus.
Check rk_inter.
assert (HX:rk (B :: Ap :: A :: Bp :: nil) <= 3).
assert (rk (B :: Ap :: A :: Bp :: nil) = 3).
Require Import pprove_Pappus2DG_noXYZ_576. 
solve_using LP2P3P5P6.
lia.
destruct (rk_inter B Ap A Bp HX) as [X [HX1 HX2]].

assert (HY:rk (C :: Ap :: A :: Cp :: nil) <= 3).
assert (rk (C :: Ap :: A :: Cp :: nil) = 3).
Require Import pprove_Pappus2DG_noXYZ_18969. 
 solve_using LP2P4P5P7.
lia.
destruct (rk_inter C Ap A Cp HY) as [Y [HY1 HY2]].

assert (HZ:rk (B :: Cp :: C :: Bp :: nil) <= 3).
assert (rk (B :: Cp :: C :: Bp :: nil) = 3).
Require Import pprove_Pappus2DG_noXYZ_39020. 
solve_using LP3P4P6P7.
lia.
destruct (rk_inter B Cp C Bp HZ) as [Z [HZ1 HZ2]].
assert (Hpappus : rk (X :: Y :: Z :: nil) = 2).


(*
rk_pappus
     : forall A B C D E F G H I : Point,
       rk (A :: B :: nil) = 2 ->
       rk (A :: C :: nil) = 2 ->
       rk (A :: D :: nil) = 2 ->
       rk (A :: E :: nil) = 2 ->
       rk (A :: F :: nil) = 2 ->
       rk (B :: C :: nil) = 2 ->
       rk (B :: D :: nil) = 2 ->
       rk (B :: E :: nil) = 2 ->
       rk (B :: F :: nil) = 2 ->
       rk (C :: D :: nil) = 2 ->
       rk (C :: E :: nil) = 2 ->
       rk (C :: F :: nil) = 2 ->
       rk (D :: E :: nil) = 2 ->
       rk (D :: F :: nil) = 2 ->
       rk (E :: F :: nil) = 2 ->
       rk (A :: B :: C :: nil) = 2 ->
       rk (D :: E :: F :: nil) = 2 ->
       rk (A :: E :: G :: nil) = 2 ->
       rk (B :: D :: G :: nil) = 2 ->
       rk (A :: F :: H :: nil) = 2 ->
       rk (C :: D :: H :: nil) = 2 ->
       rk (B :: F :: I :: nil) = 2 -> rk (C :: E :: I :: nil) = 2 -> rk (G :: H :: I :: nil) = 2
*)

eapply (rk_pappus) with (A:=A) (B:=B) (C:=C) (D:=Ap) (E:=Bp) (F:=Cp); try assumption. 
Require Import pprove_Pappus2DG_noXYZ_60841. 
solve_using LP2P5.
Require Import pprove_Pappus2DG_noXYZ_60842. 
solve_using LP2P6.
Require Import pprove_Pappus2DG_noXYZ_60843. 
 solve_using LP2P7. 
admit.
admit.
admit.
admit.
admit.
admit.
admit.
admit.

assert (HR:rk (Y :: M :: Z :: N :: nil) <= 3).
assert (rk (Y :: M :: Z :: N :: nil) = 3).
pprove.
Require Import pprove_Pappus2DG_noXYZ_129851. 
 solve_using LP1P5P8P9P11P15P16.
admit. (*
pprove.
Require Import pprove_Pappus2DG_noXYZ_39020. 
solve_using LP3P4P6P7.*)
lia.
destruct (rk_inter Y M Z N HR) as [R [HR1 HR2]].
apply Pappus2DG with (Oo:=Oo) (A:=A) (B:=B) (Ap:=Ap) (Bp:=Bp) (X:=X) (Y:=Y) (Z:=Z) (M:=M) (N:=N) (R:=R); assumption.
Qed.



Ltac revert_all_relevant_hyps P1 P2 :=

  repeat match goal with H:(rk (P1::_)= ?a) |- _ => revert H 
| H:(rk (_::P1::_)= ?a) |- _ => revert H 
| H:(rk (_::_::P1::_)= ?a) |- _ => revert H 
| H:(rk (_::_::_::P1::_)= ?a) |- _ => revert H 
| H:(rk (_::_::_::_::P1::_)= ?a) |- _ => revert H 
| H:(rk (_::_::_::_::_::P1::_)= ?a) |- _ => revert H 
| H:(rk (_::_::_::_::_::_::P1::_)= ?a) |- _ => revert H
| H:(rk (_::_::_::_::_::_::_::P1::_)= ?a) |- _ => revert H
| H:(rk (_::_::_::_::_::_::_::_::P1::_)= ?a) |- _ => revert H
         end;
            
  repeat match goal with H:(rk (P2::_)= ?a) |- _ => revert H 
| H:(rk (_::P2::_)= ?a) |- _ => revert H 
| H:(rk (_::_::P2::_)= ?a) |- _ => revert H 
| H:(rk (_::_::_::P2::_)= ?a) |- _ => revert H 
| H:(rk (_::_::_::_::P2::_)= ?a) |- _ => revert H 
| H:(rk (_::_::_::_::_::P2::_)= ?a) |- _ => revert H 
| H:(rk (_::_::_::_::_::_::P2::_)= ?a) |- _ => revert H
| H:(rk (_::_::_::_::_::_::_::P2::_)= ?a) |- _ => revert H
| H:(rk (_::_::_::_::_::_::_::_::P2::_)= ?a) |- _ => revert H
         end.

revert_all_relevant_hyps A Bp.
Ltac clear_rk_hyps := match goal with
                        H:rk(_)=_ |- _ => clear H
                      | H:rk(_)<=_ |- _ => clear H
                                                                        
                      end.
repeat clear_rk_hyps.
Ltac clear_useless_points := repeat match goal with X:Point |- _ => clear X end.
clear_useless_points.
clear Z.
pprove.




(*

Lemma dg : forall A A' B B' C C' R P Q 
                  N M L N' M' L' O : Point,
rk(B ::  C' ::  P ::  L :: nil) = 2 -> (* line a *)
rk(B' ::  C ::  P ::  L' :: nil) = 2 -> (* line a' *)
rk(A' ::  Q ::  C ::  M :: nil) = 2 -> (* line b *)
rk(A ::  Q ::  C' ::  M' :: nil) = 2 -> (* line b' *)
rk(R ::  A ::  B' ::  N :: nil) = 2 -> (* line c *)
rk(R ::  A' ::  B ::  N' :: nil) = 2 -> (* line c' *)
rk(A' ::  B ::  C ::  C' ::  P ::  Q :: nil) = 4 -> (* a & b *)
rk(A ::  B ::  B' ::  C' ::  P ::  R :: nil) = 4 -> (* a & c *)
rk(A ::  A' ::  B' ::  C  ::  Q ::  R :: nil) = 4 -> (* b & c *)
rk(A ::  B' ::  C ::  C' ::  P ::  Q :: nil) = 4 -> (* a' & b' *)
rk(A' ::  B ::  B' ::  C ::  P ::  R :: nil) = 4 -> (* a' & c' *)
rk(A ::  A' ::  B ::  C' ::  Q ::  R :: nil) = 4 -> (* b' & c' *)
rk(N ::  M ::  L ::  O :: nil) = 2 -> (* line e *)
rk(N' ::  M' ::  L' ::  O :: nil) = 2 -> (* line e' *)
rk(A ::  C' ::  P ::  Q ::  B ::  M' :: nil) = 3 -> (* plane [a & b'] & M' *)
rk(B ::  C' ::  P ::  N' ::  M' ::  L' :: nil) = 4 -> (* a & e' *)
rk(A' ::  C ::  Q ::  N' ::  M' ::  L' :: nil) = 4 -> (* b & e' *)
rk(A ::  B' ::  R ::  N' ::  M' ::  L' :: nil) = 4 -> (* c & e' *)
rk(B' ::  C ::  P ::  N ::  M ::  L :: nil) = 4 -> (* a' & e *)
rk(A ::  C' ::  Q ::  N ::  M ::  L :: nil) = 4 -> (* b' & e *)
rk(A' ::  B ::  R ::  N ::  M ::  L :: nil) = 4 -> (* c' & e *)
rk(A ::  C' ::  Q :: M' :: nil) = 2. (* M' belongs to b' *) *)

Require Import lemma00.

Require Import lemmaXX.
Require Import lemmaYY.

Require Import lemma1.
Require Import lemma2.
Require Import lemma3.
Require Import lemma4.
Require Import lemma5.
Require Import lemma6.
Require Import lemma7.
Require Import lemma8.
Require Import lemma9.
Require Import lemma10.
Require Import lemma11.
Require Import lemma12.
Require Import lemma13.
Require Import lemma14.
Require Import lemma15.
Require Import lemma16.
Require Import lemma17.
Require Import lemma18.
Require Import lemma19.

Lemma eq_le_ge : forall x y : nat, x<=y<=x -> x=y.
Proof.
  intros; omega.
Qed.

Check rk_pappus.
(* Lemma dg : forall A A' B B' C C' R P Q 
                  N M L N' M' L' O : Point,
rk(B, C', P, L) = 2 -> */ line a */
rk(B', C, P, L') = 2 -> */ line a' */
rk(A', Q, C, M) = 2 -> /* line b */
rk(A, Q, C', M') = 2 -> /* line b' */
rk(R, A, B', N) = 2 -> /* line c */
rk(R, A', B, N') = 2 -> /* line c' */
rk(A', B, C, C', P, Q) = 4 -> /* a & b */
rk(A, B, B', C', P, R) = 4 -> /* a & c */
rk(A, A', B', C , Q, R) = 4 -> /* b & c */
rk(A, B', C, C', P, Q) = 4 -> /* a' & b' */
rk(A', B, B', C, P, R) = 4 -> /* a' & c' */
rk(A, A', B, C', Q, R) = 4 -> /* b' & c' */
rk(N, M, L, O) = 2 -> /* line e */
rk(N', M', L', O) = 2 -> /* line e' */
rk(A, C', P, Q, B, M') = 3 -> /* plane [a & b'] & M' */
rk(B, C', P, N', M', L') = 4 -> /* a & e' */
rk(A', C, Q, N', M', L') = 4 -> /* b & e' */
rk(A, B', R, N', M', L') = 4 -> /* c & e' */
rk(B', C, P, N, M, L) = 4 -> /* a' & e */
rk(A, C', Q, N, M, L) = 4 -> /* b' & e */
rk(A', B, R, N, M, L) = 4 -> /* c' & e */
rk(A, C', Q, M') = 2. /* M' belongs to b' */ *)

Axiom rk_DG : forall A A' B B' C C'
                     D D' E E' F F'
                     T U V W,
                     
    (* 3 skew lines *)
    rk(A::A'::nil)=2 -> (* a *)
    rk(B::B'::nil)=2 -> (* b *)
    rk(C::C'::nil)=2 -> (* c *)
    rk(A::A'::B::B'::nil)=4 -> (* skew a b *)
    rk(A::A'::C::C'::nil)=4 -> (* skew a c *)
    rk(B::B'::C::C'::nil)=4 -> (* skew b c *)

    (* 3 other skew lines *)
    rk(D::D'::nil)=2 ->
    rk(E::E'::nil)=2 ->
    rk(F::F'::nil)=2 ->
    rk(D::D'::E::E'::nil)=4 -> 
    rk(D::D'::F::F'::nil)=4 ->
    rk(E::E'::F::F'::nil)=4 ->

    (* all 3 lines meet all 3 other lines *)
    rk(A::A'::D::D'::nil)=3 ->
    rk(A::A'::E::E'::nil)=3 ->
    rk(A::A'::F::F'::nil)=3 ->


    rk(B::B'::D::D'::nil)=3 ->
    rk(B::B'::E::E'::nil)=3 ->
    rk(B::B'::F::F'::nil)=3 ->

    rk(C::C'::D::D'::nil)=3 ->
    rk(C::C'::E::E'::nil)=3 ->
    rk(C::C'::F::F'::nil)=3 ->

    (* any traversal of the first set *)
    rk(T::U::nil)=2 ->
    rk(T::U::A::A'::nil)=3 ->
    rk(T::U::B::B'::nil)=3 ->
    rk(T::U::C::C'::nil)=3 ->
    
    (* any traversal of the second set *)
    rk(V::W::nil)=2 ->
    rk(V::W::D::D'::nil)=3 ->
    rk(V::W::E::E'::nil)=3 ->
    rk(V::W::F::F'::nil)=3 ->

    (* meets = are coplanar *)
    rk(V::W::T::U::nil)=3.

Lemma plane_of_2_lines : forall T U V X Y Z,
    rk(T::U::nil)=2 -> rk(T::V::nil)=2 -> rk(U::V::nil)=2 -> rk(T::U::V::nil)=2 ->
    rk(X::Y::nil)=2 -> rk(X::Z::nil)=2 -> rk(Y::Z::nil)=2 -> rk(X::Y::Z::nil)=2 ->
    rk(T::U::X::Y::nil)=3 ->
    exists R:Point, rk(T::U::V::R::nil)=2 /\ rk(X::Y::Z::R::nil)=2.
Proof.
  intros.
  assert (H1': rk (T :: U :: X :: Y :: nil) <=3) by omega.
  destruct (rk_inter _ _ _ _ H1') as [R [Hi1 Hi2]].
  exists R; split.
  apply (LP1P2P3P7 T U V X Y Z R); assumption.
  apply (LP1P2P3P7 X Y Z T U V R); try assumption.
  assert (Hrk:rk(X::Y::T::U::nil)=rk(T::U::X::Y::nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  assumption.
Qed.

(*Lemma LP8P9P10 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 ,
rk(P1 :: P2 ::  nil) = 2 -> rk(P1 :: P3 ::  nil) = 2 -> rk(P2 :: P3 ::  nil) = 2 ->
rk(P1 :: P4 ::  nil) = 2 -> rk(P2 :: P4 ::  nil) = 2 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P2 :: P3 :: P4 ::  nil) = 2 -> rk(P1 :: P5 ::  nil) = 2 -> rk(P1 :: P6 ::  nil) = 2 ->
rk(P5 :: P6 ::  nil) = 2 -> rk(P1 :: P7 ::  nil) = 2 -> rk(P5 :: P7 ::  nil) = 2 ->
rk(P6 :: P7 ::  nil) = 2 -> rk(P1 :: P5 :: P6 :: P7 ::  nil) = 2 -> rk(P2 :: P3 :: P4 :: P5 :: P6 :: P7 ::  nil) = 3 ->
rk(P3 :: P5 :: P8 ::  nil) = 2 -> rk(P2 :: P6 :: P8 ::  nil) = 2 -> rk(P4 :: P5 :: P9 ::  nil) = 2 ->
rk(P2 :: P7 :: P9 ::  nil) = 2 -> rk(P4 :: P6 :: P10 ::  nil) = 2 -> rk(P3 :: P7 :: P10 ::  nil) = 2 ->
rk(P1 :: P2 :: P5 :: P11 ::  nil) = 4 -> rk(P8 :: P12 ::  nil) = 2 -> rk(P11 :: P12 ::  nil) = 2 ->
rk(P8 :: P11 :: P12 ::  nil) = 2 -> rk(P5 :: P11 :: P13 ::  nil) = 2 -> rk(P6 :: P12 :: P14 ::  nil) = 2 ->
rk(P2 :: P11 :: P15 ::  nil) = 2 -> rk(P3 :: P12 :: P16 ::  nil) = 2 -> rk(P4 :: P13 :: P14 :: P17 ::  nil) = 2 ->
rk(P7 :: P15 :: P16 :: P17 ::  nil) = 2 -> rk(P8 :: P9 :: P10 ::  nil) = 2.
Proof.
Admitted.*)

Lemma rk_3_to_4 :  forall A B C:Point, rk(A::B::C::nil)=3 -> exists P:Point, rk(A::B::C::P::nil)=4.
Proof.
intros A B C HABC.
destruct (rk_lower_dim) as [P1 [P2 [P3 [P4 HP1P2P3P4]]]].
assert (HP1:rk(A::B::C::P1::nil)=3\/rk(A::B::C::P1::nil)=4).
assert (3<=rk(A::B::C::P1::nil)<=4).
split.
rewrite <- HABC.
apply matroid2; my_inO.
apply rk_upper_dim.
omega.
destruct HP1 as [HP13 | HP14].

assert (HP2:rk(A::B::C::P1::P2::nil)=3\/rk(A::B::C::P1::P2::nil)=4).
assert (3<=rk(A::B::C::P1::P2::nil)<=4).
split.
rewrite <- HP13.
apply matroid2; my_inO.
apply rk_upper_dim.
omega.
destruct HP2 as [HP23 | HP24].

assert (HP3:rk(A::B::C::P1::P2::P3::nil)=3\/rk(A::B::C::P1::P2::P3::nil)=4).
assert (3<=rk(A::B::C::P1::P2::P3::nil)<=4).
split.
rewrite <- HP23.
apply matroid2; my_inO.
apply rk_upper_dim.
omega.
destruct HP3 as [HP33 | HP34].

assert (HP4:rk(A::B::C::P1::P2::P3::P4::nil)=4).
assert (4<=rk(A::B::C::P1::P2::P3::P4::nil)<=4).
split.
rewrite <- HP1P2P3P4.
apply matroid2; my_inO.
apply rk_upper_dim.
omega.
(* case P4 *)
destruct (eq_dec P1 P4).
subst; replace (rk (A :: B :: C :: P4 :: P2::P3::P4 :: nil)) with (rk (A :: B :: C :: P4::P2 ::P3:: nil)) in * by (apply eq_le_ge; split; apply matroid2; my_inO);rewrite HP4 in HP33; omega.
destruct (eq_dec P2 P4).
subst; replace (rk (A :: B :: C :: P1 :: P4::P3::P4 :: nil)) with (rk (A :: B :: C :: P1::P4 ::P3:: nil)) in * by (apply eq_le_ge; split; apply matroid2; my_inO);rewrite HP4 in HP33; omega.
destruct (eq_dec P3 P4).
subst; replace (rk (A :: B :: C :: P1 :: P2::P4::P4 :: nil)) with (rk (A :: B :: C :: P1::P2 ::P4:: nil)) in * by (apply eq_le_ge; split; apply matroid2; my_inO);rewrite HP4 in HP33; omega.

exists P4.
assert (4<=rk(A::B::C::P4::nil)<=4).
split.
assert (Hm3:rk((A::B::C::P1::P2::P3::nil) ++ (A::B::C::P4::nil)) +
        rk(list_inter (A::B::C::P1::P2::P3::nil) (A::B::C::P4::nil)) <= rk (A::B::C::P1::P2::P3::nil) + rk  (A::B::C::P4::nil)).
apply matroid3.
replace (rk
          ((A :: B :: C :: P1 :: P2 :: P3::nil) ++
           A :: B :: C :: P4 :: nil)) with (rk (A::B::C::P1::P2::P3::P4::nil)) in Hm3 by (apply eq_le_ge; split; apply matroid2; my_inO).
replace (rk
          (list_inter
             (A :: B :: C :: P1 :: P2 ::P3:: nil)
             (A :: B :: C :: P4 :: nil))) with (rk (A::B::C::nil)) in Hm3 by (apply eq_le_ge; split;apply matroid2; my_inO).

omega.
apply rk_upper_dim.
omega.

(* case P3 *)
destruct (eq_dec P1 P3).
subst; replace (rk (A :: B :: C :: P3 :: P2::P3:: nil)) with (rk (A :: B :: C ::P3 ::P2:: nil)) in * by (apply eq_le_ge; split; apply matroid2; my_inO); rewrite HP23 in *; omega.
destruct (eq_dec P2 P3).
subst; replace (rk (A :: B :: C :: P1 :: P3::P3 :: nil)) with (rk (A :: B :: C ::P1 ::P3:: nil)) in * by (apply eq_le_ge; split; apply matroid2; my_inO); rewrite HP34 in *; omega.
exists P3.
assert (4<=rk(A::B::C::P3::nil)<=4).
split.
assert (Hm3:rk((A::B::C::P1::P2::nil) ++ (A::B::C::P3::nil)) +
        rk(list_inter (A::B::C::P1::P2::nil) (A::B::C::P3::nil)) <= rk (A::B::C::P1::P2::nil) + rk  (A::B::C::P3::nil)).
apply matroid3.
replace (rk
          ((A :: B :: C :: P1 :: P2 :: nil) ++
           A :: B :: C :: P3 :: nil)) with (rk (A::B::C::P1::P2::P3::nil)) in Hm3 by (apply eq_le_ge; split; apply matroid2; my_inO).
replace (rk
          (list_inter
             (A :: B :: C :: P1 :: P2 :: nil)
             (A :: B :: C :: P3 :: nil))) with (rk (A::B::C::nil)) in Hm3 by (apply eq_le_ge; split;apply matroid2; my_inO).
omega.
apply rk_upper_dim.
omega.

destruct (eq_dec P1 P2).
subst; replace (rk (A :: B :: C :: P2 :: P2 :: nil)) with (rk (A :: B :: C :: P2 :: nil)) in HP24 by (apply eq_le_ge; split; apply matroid2; my_inO);rewrite HP24 in HP13; omega.
exists P2.
assert (4<=rk(A::B::C::P2::nil)<=4).
split.
assert (Hm3:rk((A::B::C::P1::nil) ++ (A::B::C::P2::nil)) +
        rk(list_inter (A::B::C::P1::nil) (A::B::C::P2::nil)) <= rk (A::B::C::P1::nil) + rk  (A::B::C::P2::nil)).
apply matroid3.
replace (rk((A :: B :: C :: P1 :: nil) ++ A :: B :: C :: P2 :: nil)) with  (rk(A :: B :: C :: P1 :: P2 :: nil)) in Hm3 by (apply eq_le_ge; split; apply matroid2; my_inO).
replace  (rk (list_inter (A :: B :: C :: P1 :: nil) (A :: B :: C :: P2 :: nil))) with (rk (A::B::C::nil)) in Hm3 by (apply eq_le_ge; split;apply matroid2; my_inO).
omega.
apply rk_upper_dim.
omega.

exists P1; assumption.
Qed.

Lemma traversal : forall C B Q A P,
    rk(B::Q::nil)=2 -> rk(A::P::nil)=2 -> rk(B::Q::A::P::nil)=4 ->
    rk(C::A::P::nil)=3 -> rk(C::B::Q::nil)=3 -> 
    exists Idf, exists Idg,  rk(Idf::Idg::nil)=2/\
                             rk(C::Idf::nil)=2/\
                             rk(C::Idg::nil)=2/\
                             
                             rk(A::P::Idf::nil)=2 /\
                             rk(B::Q::Idg::nil)=2 /\ 
                             rk(C::Idf::Idg::nil)=2.
Admitted.                                    

Lemma traversal_specific : forall O A B C A' C' P Q,
    rk(O::A::A'::nil)=3 -> rk(O::A::A'::P::nil)=4 -> rk(O::A::A'::C'::nil)=3 ->
    rk(O::A::A'::Q::nil)=4 ->  rk(P::Q::nil)=2 -> 
    exists Idf, exists Idg, rk(A::P::Idf::nil)=2 /\
                            rk(B::Q::Idg::nil)=2 /\ 
                            rk(C::Idf::Idg::nil)=2.
Admitted.
    
Lemma DG_wo_extra_points : forall O A B C A2 B2 C2 X Y Z: Point,
  rk(A::B::nil)=2 ->
  rk(A::C::nil)=2 -> 
  rk(B::C::nil)=2 -> 
  
  rk(A2::B2::nil)=2 -> 
  rk(A2::C2::nil)=2 -> 
  rk(B2::C2::nil)=2 -> 

  rk(O::A::nil)=2 -> 
  rk(O::B::nil)=2 -> 
  rk(O::C::nil)=2 -> 
  rk(O::A2::nil)=2 -> 
  rk(O::B2::nil)=2 -> 
  rk(O::C2::nil)=2 -> 

  rk(A::B2::X::nil)=2 -> 
  rk(B::A2::X::nil)=2 -> 
  rk(A::C2::Y::nil)=2 -> 
  rk(C::A2::Y::nil)=2 -> 
  rk(B::C2::Z::nil)=2 -> 
  rk(C::B2::Z::nil)=2 -> 
  
  rk(O::A::B::C::nil)=2 ->  (* line a *)
  rk(O::A2::B2::C2::nil)=2 ->  (* line e *)

  rk(O::A::A2::nil)=3 -> (* plane (a,e) *)
  
(*  rk(A2::P::Ihb::nil)=2 ->  // line b
  rk(Q::B2::Ihc::nil)=2 ->  // line c
  rk(C2::Idg::Idf::R::nil)=2 ->  // line d *)

(*  rk(A::P::Idf::nil)=2 ->  // line f
  rk(B::Q::Idg::nil)=2 ->  // line g
  rk(C::Ihb::Ihc::R::nil)=2 ->  // line h *)

(*  rk(O::A::A2::P::nil) = 4 -> // P is outside plane (a,e) *)
(*
  rk(Q::X::P::nil)=2 -> 
  rk(Q::X::nil)=2 -> 
  rk(Q::P::nil)=2 ->
  *)
  rk(X::Y::Z::nil)=2.
Proof.
  intros.
  Check (LP1P2P5 O A B C A2 B2 C2).
  assert (H19':rk (O ::A :: A2 :: nil) = 3) by (eapply (LP1P2P5 O A B C A2 B2 C2); assumption).
  elim (rk_3_to_4 O A A2 H19'); intros P HP.
  elim (rk_three_points_on_lines X P).
  intros Q [HQ1 [HQ2 HQ3]].
  (* let d be the unique transversal from C′ to the skew lines f and g *)
  (* let h be the unique transversal from C to the skew lines b and c*)
  (*assert (HBQ:rk (B :: Q :: nil) = 2) by (apply (LP3P12 O A B C A2 B2 C2 X Y Z P Q); assumption).
  assert (HAP:rk(A :: P ::nil)=2) by (apply (LP2P11 O A B C A2 B2 C2 X Y Z P Q); assumption).
  assert (HBQAP:rk (B :: Q :: A :: P :: nil) = 4).
  
  assert (HBQAP':rk (A :: B :: P :: Q :: nil) = 4)
    by (apply (LP2P3P11P12 O A B C A2 B2 C2 X Y Z P Q); assumption).
  assert (Hrk : rk (B :: Q :: A :: P :: nil) = rk (A :: B :: P :: Q :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk; assumption.
  assert (HA2B2PQ:rk (C2 :: A :: P :: nil) = 3).
  assert (Hrk:rk (C2 :: A :: P :: nil) = rk (A::C2::P::nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  (*apply (LP2P7P11 O A B C A2 B2 C2 X Y Z P Q); admit.*)
  admit.
  assert (HC2BQ:rk(C2::B::Q::nil)=3) by admit.*)

  Check (traversal_specific O A B C A2 C2 P Q).
  assert (HOAA2 : rk (O :: A :: A2 :: nil) = 3).
  admit.
  assert (HOAA2Q : rk (O :: A :: A2 :: P :: nil) = 4).
  admit. 
  assert (HOAA2C2: rk (O :: A :: A2 :: C2 :: nil) = 3).
  admit.
  assert (HOAA2P:rk (O :: A :: A2 :: Q :: nil) = 4).
  admit.
  assert(HPQ: rk (P :: Q :: nil) = 2).
  admit.

  
  destruct (traversal_specific O A B C A2 C2 P Q HOAA2 HOAA2Q HOAA2C2 HOAA2P HPQ) as [Idf [Idg [Hd1 [Hd2 Hd3 ]]]].
(*
                               traversal_specific C2 B Q A P HBQ HAP HBQAP HA2B2PQ HC2BQ) as [Idf [Idg [Hd1 [Hd2 [Hd3 [Hd4 [Hd5 Hd6]]]]]]].
  assert (HA2P: rk (A2 :: P :: nil) = 2) by (apply (LP5P11 O A B C A2 B2 C2 X Y Z P Q); assumption).
  assert (HQB2: rk (B2 :: Q :: nil) = 2) by (apply (LP6P12 O A B C A2 B2 C2 X Y Z P Q); assumption).
  assert (HQB2A2P : rk (B2 :: Q :: A2 :: P :: nil) = 4).
  assert (HQB2A2P' : rk (A2 :: B2 :: P :: Q :: nil) = 4)
    by (apply (LP5P6P11P12 O A B C A2 B2 C2 X Y Z P Q); assumption).
  assert (Hrk: rk (B2 :: Q :: A2 :: P :: nil) = rk (A2 :: B2 :: P :: Q :: nil) )
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk; assumption.
  (*apply (LP2P7P11 O A B C A2 B2 C2 X Y Z P Q); try assumption.
  assert (Hrk2:rk (A2 :: B2 :: P :: Q :: nil) = rk (B2 :: Q :: A2 :: P :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk2; assumption.
  assert (Hrk:rk (C2 :: B :: Q :: nil) = rk (B :: C2 :: Q :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.*)
(*  apply (LP3P7P12 O A B C A2 B2 C2 X Y Z P Q);  assumption. *)
(*  assert (HQB2:rk(B2::Q::nil)=2) by admit.*)
(*  assert (HA2P:rk(A2::P::nil)=2) by admit.*)
(*  assert (HQB2A2P:rk(B2::Q::A2::P::nil)=4) by admit.*)
  assert (HCA2P: rk (C :: A2 :: P :: nil) = 3) by admit.
  assert (HCB2Q: rk (C :: B2 :: Q :: nil) = 3) by admit. *)
  Check (traversal_specific O A2 B2 C2 A C P Q ).
  assert (HOA2A : rk (O :: A2 :: A :: nil) = 3).
  admit.
  assert (HA2AQ : rk (O :: A2 :: A :: P :: nil) = 4).
  admit.
  assert (HOA2AC : rk (O :: A2 :: A :: C :: nil) = 3).
  admit.
  assert (HOA2AP : rk (O :: A2 :: A :: Q :: nil) = 4).
  admit.
  assert (HQP: rk (P::Q::nil)=2).
  admit.
  destruct (traversal_specific O A2 B2 C2 A C P Q HOA2A HA2AQ HOA2AC HOA2AP HQP) as [Ihb [Ihc [Hh1 [Hh2 Hh3]]]].
  assert (rk (C :: Ihb :: C2 :: Idg :: nil) = 3).
  Check (rk_DG A B A2 P B2 Q A2 B2 A P B Q C2 Idg C Ihb).
  (*
       rk (A :: B :: nil) = 2 ->
       rk (A2 :: P :: nil) = 2 ->
       rk (B2 :: Q :: nil) = 2 ->
       rk (A :: B :: A2 :: P :: nil) = 4 ->
       rk (A :: B :: B2 :: Q :: nil) = 4 ->
       rk (A2 :: P :: B2 :: Q :: nil) = 4 ->
       rk (A2 :: B2 :: nil) = 2 ->
       rk (A :: P :: nil) = 2 ->
       rk (B :: Q :: nil) = 2 ->
       rk (A2 :: B2 :: A :: P :: nil) = 4 ->
       rk (A2 :: B2 :: B :: Q :: nil) = 4 ->
       rk (A :: P :: B :: Q :: nil) = 4 ->
       rk (A :: B :: A2 :: B2 :: nil) = 3 ->
       rk (A :: B :: A :: P :: nil) = 3 ->
       rk (A :: B :: B :: Q :: nil) = 3 ->
       rk (A2 :: P :: A2 :: B2 :: nil) = 3 ->
       rk (A2 :: P :: A :: P :: nil) = 3 ->
       rk (A2 :: P :: B :: Q :: nil) = 3 ->
       rk (B2 :: Q :: A2 :: B2 :: nil) = 3 ->
       rk (B2 :: Q :: A :: P :: nil) = 3 ->
       rk (B2 :: Q :: B :: Q :: nil) = 3 ->
       rk (C2 :: Idg :: nil) = 2 ->
       rk (C2 :: Idg :: A :: B :: nil) = 3 ->
       rk (C2 :: Idg :: A2 :: P :: nil) = 3 ->
       rk (C2 :: Idg :: B2 :: Q :: nil) = 3 ->
       rk (C :: Ihb :: nil) = 2 ->
       rk (C :: Ihb :: A2 :: B2 :: nil) = 3 ->
       rk (C :: Ihb :: A :: P :: nil) = 3 ->
       rk (C :: Ihb :: B :: Q :: nil) = 3 ->
       rk (C :: Ihb :: C2 :: Idg :: nil) = 3
   *)
  apply (rk_DG A B A2 P B2 Q A2 B2 A P B Q C2 Idg C Ihb); try assumption.
  admit. (* trivial*)
  admit. (* trivial*)
  apply (LP2P3P5P11 O A B C A2 B2 C2 X Y Z P Q); assumption.
  apply (LP2P3P6P12 O A B C A2 B2 C2 X Y Z P Q); assumption.
  assert (Hrk:rk (A2 :: P :: B2 :: Q :: nil) = rk (A2 :: B2 :: P :: Q :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  apply (LP5P6P11P12 O A B C A2 B2 C2 X Y Z P Q); assumption.
  admit. (* trivial*)
  admit. (* trivial*)
  assert (Hrk:rk (A2 :: B2 :: A :: P :: nil) = rk (A :: A2 :: B2 :: P :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  apply (LP2P5P6P11 O A B C A2 B2 C2 X Y Z P Q); assumption.
  assert (Hrk:rk (A2 :: B2 :: B :: Q :: nil) = rk (B :: A2 :: B2 :: Q :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  apply (LP3P5P6P12 O A B C A2 B2 C2 X Y Z P Q); assumption.
  assert (Hrk:rk (A :: P :: B :: Q :: nil) = rk (A :: B :: P :: Q :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  apply (LP2P3P11P12 O A B C A2 B2 C2 X Y Z P Q); assumption.
  admit. (* trivial *)
  admit. (* trivial - to be checked *)
  admit. (* trivial - to be checked *)
  admit. (* trivial - to be checked *)
  admit. (* trivial - to be checked *)
  admit. (* trivial - to be checked *)
  admit.
  admit.
  admit.
admit. (* a verifier en premier : C2 Idg = 2 *)
admit. (*rk (C2 :: Idg :: A :: B :: nil) = 3*)
admit. (*rk (C2 :: Idg :: A2 :: P :: nil) = 3*)
admit. (* rk (C2 :: Idg :: B2 :: Q :: nil) = 3*)



  admit.
  admit.
  assert (Hrk:rk (A2 :: P :: B :: Q :: nil) = rk (B :: A2 :: P :: Q :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  apply (LP3P5P11P12 O A B C A2 B2 C2 X Y Z P Q); assumption.
  assert (Hrk:rk (B2 :: Q :: A2 :: B2 :: nil) = rk (A2 :: B2 :: Q :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  apply (LP5P6P12 O A B C A2 B2 C2 X Y Z P Q); assumption.
  assert (Hrk:rk (B2 :: Q :: A :: P :: nil) = rk (A :: B2 :: P :: Q :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  apply (LP2P6P11P12 O A B C A2 B2 C2 X Y Z P Q); assumption.
  assert (Hrk:rk (B2 :: Q :: B :: Q :: nil) = rk (B :: B2 :: Q :: nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk.
  apply (LP3P6P12 O A B C A2 B2 C2 X Y Z P Q); assumption.
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
(*  apply (LP7P16 O A B C A2 B2 C2 X Y Z P Q Ihb Ihc Idf Idg); assumption.
  admit. (* pb *)
  admit. (* ? *)
  admit. (* ? *)
  apply (LP4P13 O A B C A2 B2 C2 X Y Z P Q Ihb Ihc Idf Idg); assumption.
  admit. (* pb *)
  admit.
  admit.*)
  Check plane_of_2_lines.
  destruct (plane_of_2_lines C Ihb Ihc C2 Idg Idf) as [R [HR1 HR2]]; try assumption.
  assert (Hrk:rk (Idg :: Idf :: nil) = rk (Idf::Idg::nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk; assumption.
  assert (Hrk:rk (C2:: Idg :: Idf :: nil) = rk (C2::Idf::Idg::nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk; assumption.

  eapply LP8P9P10 with (P1:=O) (P2:=A) (P3:=B) (P4:=C) (P5:=A2) (P6:=B2) (P7:=C2)
  (* P8 P9 P10 are in the conclusion *)
  (P11:=P) (P12:=Q) (P13:=Ihb) (P14:=Ihc) (P15:=Idf) (P16:=Idg) (P17:=R); try assumption.

  assert (Hrk:rk (C2:: Idf :: Idg :: R :: nil) = rk (C2::Idg::Idf::R::nil))
    by (apply eq_le_ge; split; apply matroid2; my_inO).
  rewrite Hrk; assumption.
Qed.
