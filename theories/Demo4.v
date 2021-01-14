From Tuto0 Require Export Loader.
Require Import Ltac_utils.

Lemma plane_of_2_lines : forall T U V X Y Z,
    rk(T::U::nil)=2 -> rk(T::V::nil)=2 -> rk(U::V::nil)=2 -> rk(T::U::V::nil)=2 ->
    rk(X::Y::nil)=2 -> rk(X::Z::nil)=2 -> rk(Y::Z::nil)=2 -> rk(X::Y::Z::nil)=2 ->
    rk(T::U::X::Y::nil)=3 ->
    exists R:Point, rk(T::U::V::R::nil)=2 /\ rk(X::Y::Z::R::nil)=2.
Proof.
  intros.
  pprove.
  Require Import plane_of_2_lines.
  solve_using L.
Qed.
