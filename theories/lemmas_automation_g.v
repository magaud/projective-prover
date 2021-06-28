Require Export basic_rank_space_list.
Require Import Lia.
(*
Lemma matroid1_b_useful : forall (l : list Point) (m : nat), length l <= m -> rk l <= m.
Proof.
intros.
assert(HH := matroid1_b l).
lia.
Qed.

Lemma matroid3_useful : forall e e' ei : list Point,
 incl ei (list_inter e e') ->
 rk(e ++ e') + rk(ei) <= rk(e) + rk(e').
Proof.
intros.
assert (rk (e ++ e') + rk (list_inter e e') <= rk e + rk e').
apply matroid3.
assert (rk (ei) <= rk (list_inter e e')).
apply matroid2;auto.
lia.
Qed.

Lemma le_S_sym : forall n m : nat,
n >= S m -> n >= m.
Proof.
intros.
intuition.
Qed.

Lemma eq_le_incl : forall n m, n = m -> n <= m.
Proof.
  intros; lia.
Qed.

Ltac solve_hyps_max H H0 :=
solve[apply matroid1_b_useful;simpl;repeat constructor
|apply rk_upper_dim
|apply eq_le_incl;apply H
|apply eq_le_incl;apply eq_sym;apply H
|apply H0
|apply le_S;apply H0
|apply le_S;apply le_S;apply H0
|apply le_S;apply le_S;apply le_S;apply H0
].

Ltac solve_hyps_min H H0:=
solve[apply matroid1_b_useful2;simpl;repeat constructor
|apply matroid1_a
|apply eq_le_incl;apply H
|apply eq_le_incl;apply eq_sym;apply H
|apply H0
|apply le_S_sym;apply H0
|apply le_S_sym;apply le_S_sym;apply H0
|apply le_S_sym;apply le_S_sym;apply le_S_sym;apply H0
].
*)

