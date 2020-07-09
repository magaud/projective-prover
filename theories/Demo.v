From Tuto0 Require Export Loader.

(* a small example *)

Lemma ex1 : forall A B C D:Point,
    rk(A::B::C::nil) = 3 ->
    rk(A::C::D::nil) = 2 ->
    rk(A::C::nil) = 2 ->
    rk(C::D::nil) = 2 ->
    rk(A::B::C::nil) = 3.
Proof.
  (* call the prover *)
Admitted.
