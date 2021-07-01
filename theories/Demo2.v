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
  pprove.
  Require Import pprove_Pappus2DG_347.
  solve_using LP4P7P13P14P15P16.
Qed.
Check Pappus2DG.

(* DG -> Pappus *)

Lemma DG2Pappus : forall Oo A B C Ap Bp Cp P X 
Y Z Q A1 B1 Ap1 Bp1 R ,
rk(A :: B :: nil) = 2 -> 
rk(A :: C :: nil) = 2 -> rk(B :: C :: nil) = 2 ->
rk(Oo :: A :: B :: C :: nil) = 2 -> 
rk(Oo :: A :: Ap :: nil) = 3 -> 
rk(Oo :: B :: Bp :: nil) = 3 ->
rk(Ap :: Bp :: nil) = 2 -> 
rk(Oo :: C :: Cp :: nil) = 3 -> 
rk(Ap :: Cp :: nil) = 2 ->
rk(Bp :: Cp :: nil) = 2 -> 
rk(Oo :: Ap :: Bp :: Cp :: nil) = 2 -> 
rk(Oo :: A :: B :: C :: 
   Ap :: Bp :: Cp :: P :: nil) = 4 ->
rk(B :: Ap :: X :: nil) = 2 -> 
rk(A :: Bp :: X :: nil) = 2 -> 
rk(C :: Ap :: Y :: nil) = 2 ->
rk(A :: Cp :: Y :: nil) = 2 -> 
rk(C :: Bp :: Z :: nil) = 2 -> 
rk(B :: Cp :: Z :: nil) = 2 ->
rk(P :: Q :: nil) = 2 -> 
rk(X :: Q :: nil) = 2 -> 
rk(P :: X :: Q :: nil) = 2 ->
rk(A :: P :: A1 :: nil) = 2 -> 
rk(A :: Cp :: P :: A1 :: nil) = 3 -> 
rk(B :: Q :: B1 :: nil) = 2 ->
rk(Cp :: A1 :: B1 :: nil) = 2 -> 
rk(Ap :: P :: Ap1 :: nil) = 2 -> 
rk(C :: Ap :: P :: Ap1 :: nil) = 3 ->
rk(Bp :: Q :: Bp1 :: nil) = 2 -> 
rk(C :: Ap1 :: Bp1 :: nil) = 2 -> 
rk(Cp :: A1 :: B1 :: R :: nil) = 2 ->
rk(C :: Ap1 :: Bp1 :: R :: nil) = 2 
-> 
rk(X :: Y :: Z :: nil) = 2.   (* Pappus col. *)
Proof.
  intros.
  pprove.
  Require Import pprove_DG2Pappus_535.
  solve_using LP9P10P11.
Qed.
Check DG2Pappus.

  

