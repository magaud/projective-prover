From Tuto0 Require Export Loader.
Require Import Ltac_utils.

(* DG -> Pappus *)

Lemma DG2Pappus : forall O A B C Ap Bp Cp P X Y Z Q A1 B1 Ap1 Bp1 R : Point,
    rk(O:: A :: B :: C :: nil) = 2 ->
    rk(O:: Ap :: Bp :: Cp :: nil) = 2 ->
    rk(O:: A :: Ap :: nil) = 3 ->
    rk(O:: B :: Bp :: nil) = 3 ->
    rk(O:: C :: Cp :: nil) = 3 ->
    rk(A:: B :: nil) = 2 ->
    rk(A:: C :: nil) = 2 ->
    rk(B:: C :: nil) = 2 ->
    rk(Ap:: Bp :: nil) = 2 ->
    rk(Ap:: Cp :: nil) = 2 ->
    rk(Bp:: Cp :: nil) = 2 ->
    rk(O:: A :: B :: C :: Ap :: Bp :: Cp :: P :: nil) = 4 ->
    rk(A:: Bp :: X :: nil) = 2 ->
    rk(Ap:: B :: X :: nil) = 2 ->
    rk(A:: Cp :: Y :: nil) = 2 ->
    rk(Ap:: C :: Y :: nil) = 2 ->
    rk(B:: Cp :: Z :: nil) = 2 ->
    rk(Bp:: C :: Z :: nil) = 2 ->
    rk(X:: P :: Q :: nil) = 2 ->
    rk(X:: Q :: nil) = 2 ->
    rk(P:: Q :: nil) = 2 ->
    rk(A:: P :: A1 :: nil) = 2 ->
    rk(A:: P :: A1 :: Cp :: nil) = 3 ->
    rk(B:: Q :: B1 :: nil) = 2 ->
    rk(Cp:: A1 :: B1 :: nil) = 2 ->
    rk(Ap:: P :: Ap1 :: nil) = 2 ->
    rk(Ap:: P :: Ap1 :: C :: nil) = 3 ->
    rk(Bp:: Q :: Bp1 :: nil) = 2 ->
    rk(C:: Ap1 ::Bp1 :: nil) = 2 ->
    rk(C:: Ap1 :: Bp1 :: R :: nil) = 2 ->
    rk(Cp:: A1:: B1:: R :: nil) = 2 ->
    rk(X::Y::Z::nil) = 2.
Proof.
  intros.
  pprove.
  Require Import pprove_DG2Pappus.
  solve_using LP9P10P11.
Qed.
  
