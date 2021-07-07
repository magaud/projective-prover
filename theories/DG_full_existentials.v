From Tuto0 Require Export Loader.
Require Import Ltac_utils.

(* Pappus -> DG - full *)

Lemma Pappus2DG_full : forall Oo A B C Ap Bp Cp X Y Z M N P Q Sp T U V R ,
rk(Oo :: A ::  nil) = 2 -> rk(Oo :: B ::  nil) = 2 -> rk(A :: B ::  nil) = 2 ->
rk(Oo :: C ::  nil) = 2 -> rk(A :: C ::  nil) = 2 -> rk(B :: C ::  nil) = 2 ->
rk(Oo :: A :: B :: C ::  nil) = 2 -> rk(Oo :: Ap ::  nil) = 2 -> rk(Oo :: A :: Ap ::  nil) = 3 ->
rk(Oo :: Bp ::  nil) = 2 -> rk(Ap :: Bp ::  nil) = 2 -> rk(Oo :: Cp ::  nil) = 2 ->
rk(Ap :: Cp ::  nil) = 2 -> rk(Bp :: Cp ::  nil) = 2 -> rk(Oo :: Ap :: Bp :: Cp ::  nil) = 2 ->
rk(B :: Ap :: X ::  nil) = 2 -> rk(A :: Bp :: X ::  nil) = 2 -> rk(C :: Ap :: Y ::  nil) = 2 ->
rk(A :: Cp :: Y ::  nil) = 2 -> rk(C :: Bp :: Z ::  nil) = 2 -> rk(B :: Cp :: Z ::  nil) = 2 ->
rk(X :: Y :: Z ::  nil) = 2 -> rk(Ap :: M :: Q :: Sp ::  nil) = 2 -> rk(Oo :: A :: B :: C :: Ap :: M :: Q :: Sp ::  nil) = 4 ->
rk(Bp :: N :: P :: T ::  nil) = 2 -> rk(Oo :: A :: B :: C :: Bp :: N :: P :: T ::  nil) = 4 -> rk(C :: Sp :: T ::  nil) = 2 ->
rk(Oo :: C :: Ap :: Bp :: Cp :: Sp :: T ::  nil) = 4 -> rk(Ap :: Bp :: M :: N :: P :: Q :: Sp :: T ::  nil) = 4 -> rk(A :: M :: P :: U ::  nil) = 2 ->
rk(Oo :: A :: Ap :: Bp :: Cp :: M :: P :: U ::  nil) = 4 -> rk(A :: C :: M :: P :: Sp :: T :: U ::  nil) = 4 -> rk(B :: N :: Q :: V ::  nil) = 2 ->
rk(Oo :: B :: Ap :: Bp :: Cp :: N :: Q :: V ::  nil) = 4 -> rk(B :: C :: N :: Q :: Sp :: T :: V ::  nil) = 4 -> rk(Cp :: U :: V ::  nil) = 2 ->
rk(Oo :: A :: B :: C :: Cp :: U :: V ::  nil) = 4 -> rk(A :: B :: M :: N :: P :: Q :: U :: V ::  nil) = 4 -> rk(Ap :: Cp :: M :: Q :: Sp :: U :: V ::  nil) = 4 ->
rk(Bp :: Cp :: N :: P :: T :: U :: V ::  nil) = 4 -> rk(Y :: M :: R ::  nil) = 2 -> rk(Z :: N :: R ::  nil) = 2 ->
rk(C :: Cp :: Sp :: T :: U :: V ::  nil) = 3.
Proof.
  intros.
  try pprove.
  Require Import pprove_Pappus2DG_full_373. 
 solve_using LCCpSpTUV.
Qed.


Lemma Pappus2DG_noXYZ :
  forall Oo A B C Ap Bp Cp M N P Q Sp T U V ,
rk(Oo :: A ::  nil) = 2 -> rk(Oo :: B ::  nil) = 2 -> rk(A :: B ::  nil) = 2 ->
rk(Oo :: C ::  nil) = 2 -> rk(A :: C ::  nil) = 2 -> rk(B :: C ::  nil) = 2 ->
rk(Oo :: A :: B :: C ::  nil) = 2 -> rk(Oo :: Ap ::  nil) = 2 -> rk(Oo :: A :: Ap ::  nil) = 3 ->
rk(Oo :: Bp ::  nil) = 2 -> rk(Ap :: Bp ::  nil) = 2 -> rk(Oo :: Cp ::  nil) = 2 ->
rk(Ap :: Cp ::  nil) = 2 -> rk(Bp :: Cp ::  nil) = 2 -> rk(Oo :: Ap :: Bp :: Cp ::  nil) = 2 ->
(*rk(B :: Ap :: X ::  nil) = 2 -> rk(A :: Bp :: X ::  nil) = 2 -> rk(C :: Ap :: Y ::  nil) = 2 ->
rk(A :: Cp :: Y ::  nil) = 2 -> rk(C :: Bp :: Z ::  nil) = 2 -> rk(B :: Cp :: Z ::  nil) = 2 ->
rk(X :: Y :: Z ::  nil) = 2 -> *)rk(Ap :: M :: Q :: Sp ::  nil) = 2 -> rk(Oo :: A :: B :: C :: Ap :: M :: Q :: Sp ::  nil) = 4 ->
rk(Bp :: N :: P :: T ::  nil) = 2 -> rk(Oo :: A :: B :: C :: Bp :: N :: P :: T ::  nil) = 4 -> rk(C :: Sp :: T ::  nil) = 2 ->
rk(Oo :: C :: Ap :: Bp :: Cp :: Sp :: T ::  nil) = 4 -> rk(Ap :: Bp :: M :: N :: P :: Q :: Sp :: T ::  nil) = 4 -> rk(A :: M :: P :: U ::  nil) = 2 ->
rk(Oo :: A :: Ap :: Bp :: Cp :: M :: P :: U ::  nil) = 4 -> rk(A :: C :: M :: P :: Sp :: T :: U ::  nil) = 4 -> rk(B :: N :: Q :: V ::  nil) = 2 ->
rk(Oo :: B :: Ap :: Bp :: Cp :: N :: Q :: V ::  nil) = 4 -> rk(B :: C :: N :: Q :: Sp :: T :: V ::  nil) = 4 -> rk(Cp :: U :: V ::  nil) = 2 ->
rk(Oo :: A :: B :: C :: Cp :: U :: V ::  nil) = 4 -> rk(A :: B :: M :: N :: P :: Q :: U :: V ::  nil) = 4 -> rk(Ap :: Cp :: M :: Q :: Sp :: U :: V ::  nil) = 4 ->
rk(Bp :: Cp :: N :: P :: T :: U :: V ::  nil) = 4 -> (*rk(Y :: M :: R ::  nil) = 2 -> rk(Z :: N :: R ::  nil) = 2 ->*)
rk(C :: Cp :: Sp :: T :: U :: V ::  nil) = 3.
Proof.
  intros.
assert (HX:rk (B :: Ap :: A :: Bp :: nil) <= 3).
assert (rk (B :: Ap :: A :: Bp :: nil) = 3).
try pprove.
Require Import pprove_Pappus2DG_noXYZ_634. 
Check rk_inter.

solve_using LP2P3P5P6. 
lia.
destruct (rk_inter B Ap A Bp HX) as [X [HX1 HX2]].

assert (HY:rk (C :: Ap :: A :: Cp :: nil) <= 3).
assert (rk (C :: Ap :: A :: Cp :: nil) = 3).
try pprove.
Require Import pprove_Pappus2DG_noXYZ_22319. 
solve_using LP2P4P5P7.
lia.
destruct (rk_inter C Ap A Cp HY) as [Y [HY1 HY2]].

assert (HZ:rk (B :: Cp :: C :: Bp :: nil) <= 3).
assert (rk (B :: Cp :: C :: Bp :: nil) = 3).
try pprove.
Require Import pprove_Pappus2DG_noXYZ_45808. 
solve_using LP3P4P6P7.
lia.
destruct (rk_inter B Cp C Bp HZ) as [Z [HZ1 HZ2]].
assert (Hpappus : rk (X :: Y :: Z :: nil) = 2).
clear H14 H15 H20 H21 H22 H23 H29 H30 M.
clear H16 H17 H24 H25 H26 H31 N.
clear H18 H19 T.
clear H27 H28 U.
clear V.
clear Sp P Q.

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
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71219. 
solve_using LP2P5.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71220. 
solve_using LP2P6.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71221. 
solve_using LP2P7.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71223. 
try pprove.
solve_using LP3P5.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71224. 
solve_using LP3P6.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71225. 
solve_using LP3P7.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71226. 
solve_using LP4P5.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71227. 
solve_using LP4P6.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71228. 
solve_using LP4P7.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71232. 
solve_using LP2P3P4.
try pprove.
Require Import pprove_Pappus2DG_noXYZ_71233. 
solve_using LP5P6P7.

assert (HR:rk (Y :: M :: Z :: N :: nil) <= 3).
assert (rk (Y :: M :: Z :: N :: nil) = 3).
try pprove.
Require Import pprove_Pappus2DG_noXYZ_144785. 
solve_using LP8P9P17P18.
lia.
destruct (rk_inter Y M Z N HR) as [R [HR1 HR2]].
apply Pappus2DG_full with (Oo:=Oo) (A:=A) (B:=B) (Ap:=Ap) (Bp:=Bp) (X:=X) (Y:=Y) (Z:=Z) (M:=M) (N:=N) (P:=P) (Q:=Q) (R:=R); assumption.
Qed.


(*
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

Ltac clear_rk_hyps := match goal with
                        H:rk(_)=_ |- _ => clear H
                      | H:rk(_)<=_ |- _ => clear H
                                                                        
                      end.

*)
