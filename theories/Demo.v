From Tuto0 Require Export Loader.

Locate Point.

(* a small example *)

Lemma ex1 : forall A B C D:Point,
    rk(A::B::C::nil) = 3 ->
    rk(A::C::D::nil) = 2 ->
    rk(A::C::nil) = 2 ->
    rk(C::D::nil) = 2 ->
    rk(A::B::C::nil) = 3.
Proof.
  intros.
  (* call the prover *)
  pprove.
Admitted.

Lemma ex1_solved : forall A B C D:Point,
    rk(A::B::C::nil) = 3 ->
    rk(A::C::D::nil) = 2 ->
    rk(A::C::nil) = 2 ->
    rk(C::D::nil) = 2 ->
    rk(A::B::C::nil) = 3.
Proof.
intros P1 P2 P3 P4 
HP1P3eq HP1P2P3eq HP3P4eq HP1P3P4eq .

assert(HP1P2P3M : rk(P1 :: P2 :: P3 ::  nil) <= 3) by (solve_hyps_max HP1P2P3eq HP1P2P3M3).
assert(HP1P2P3m : rk(P1 :: P2 :: P3 ::  nil) >= 1) by (solve_hyps_min HP1P2P3eq HP1P2P3m1).
intuition.
Qed.

Check ex1_solved.
Print ex1_solved.