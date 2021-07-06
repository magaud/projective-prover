From Tuto0 Require Export Loader.
Require Import Ltac_utils.

Lemma plane_of_2_lines : forall T U V X Y Z,
    rk(T::U::nil)=2 -> rk(T::V::nil)=2 -> rk(U::V::nil)=2 -> rk(T::U::V::nil)=2 ->
    rk(X::Y::nil)=2 -> rk(X::Z::nil)=2 -> rk(Y::Z::nil)=2 -> rk(X::Y::Z::nil)=2 ->
    rk(T::U::X::Y::nil)=3 ->
    exists R:Point, rk(T::U::V::R::nil)=2 /\ rk(X::Y::Z::R::nil)=2.
Proof.
    intros.
    assert (H1': rk (T :: U :: X :: Y :: nil) <=3) by lia.
    destruct (rk_inter _ _ _ _ H1') as [R [Hi1 Hi2]].
    exists R; split.
    pprove.
    Require Import pprove_plane_of_2_lines_197.
    solve_using LP1P2P3P7. 
    pprove.
    Require Import pprove_plane_of_2_lines_198. 
    solve_using LP4P5P6P7. 
 Qed.
