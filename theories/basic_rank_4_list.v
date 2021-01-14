From Tuto0 Require Export basic_matroid_list.
Require Import Lia.

Parameter rk_singleton_ge : forall A, rk (A :: nil)  >= 1.
Parameter rk_couple_ge : forall A B, ~ A = B -> rk(A :: B :: nil) >= 2.
Parameter rk_three_points_on_lines : forall A B, exists C, rk (A :: B :: C :: nil) = 2 /\ rk (B :: C :: nil) = 2 /\ rk (A :: C :: nil) = 2.
Parameter rk_inter : forall A B C D, rk(A :: B :: C :: D :: nil) <= 3 -> exists J : Point, rk(A :: B :: J :: nil) = 2 /\ rk (C :: D :: J :: nil) = 2.
Parameter rk_lower_dim : exists A0 A1 A2 A3, rk( A0 :: A1 :: A2 :: A3 :: nil) = 4.
Parameter rk_upper_dim : forall e, rk(e) <= 5.

Lemma rk_singleton_1 : forall A, rk(A :: nil) <= 1.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma rk_singleton : forall A, rk(A :: nil) = 1.
Proof.
intros.
assert(H := rk_singleton_ge A).
assert(HH := rk_singleton_1 A).
lia.
Qed.

Lemma matroid1_b_useful2 : forall (l : list Point) (a : Point), length (a :: l) >= 1 -> rk (a :: l) >= 1.
Proof.
intros.
assert(HH := rk_singleton a).
assert(HH0 := matroid2 (a :: nil) (a :: l)).
assert(HH1 : incl (a :: nil) (a :: l));[my_inO|].
assert(HH2 := HH0 HH1).
lia.
Qed.

Lemma rule_1 : forall A B AiB, forall MA MB mAiB, 
rk(A) <= MA -> rk(B) <= MB -> rk(AiB) >= mAiB -> incl AiB (list_inter A B) ->
rk(A ++ B) <= MA + MB - mAiB.
Proof.
intros.
assert(HH := matroid3_useful A B AiB H2).
lia.
Qed.

Lemma rule_2 : forall A B AiB, forall mAuB mAiB MB, 
rk(A ++ B) >= mAuB -> rk(AiB) >= mAiB -> rk(B) <= MB -> incl AiB (list_inter A B) ->
rk(A) >= mAuB + mAiB - MB.
Proof.
intros.
assert(HH := matroid3_useful A B AiB H2).
lia.
Qed.

Lemma rule_3 : forall A B AiB, forall MA MB mAuB, 
rk(A) <= MA -> rk(B) <= MB -> rk(A ++ B) >= mAuB -> incl AiB (list_inter A B) ->
rk(AiB) <= MA + MB - mAuB.
Proof.
intros.
assert(HH := matroid3_useful A B AiB H2).
lia.
Qed.

Lemma rule_4 : forall A B AiB, forall mAuB mAiB MA, 
rk(A ++ B) >= mAuB -> rk(AiB) >= mAiB -> rk(A) <= MA -> incl AiB (list_inter A B) ->
rk(B) >= mAuB + mAiB - MA.
Proof.
intros.
assert(HH := matroid3_useful A B AiB H2).
lia.
Qed.

Lemma rule_5 : forall A B, forall mA mB, 
rk(A) >= mA -> mA >= mB -> incl A B ->
rk(B) >= mA.
Proof.
intros.
assert(HH := matroid2 A B H1).
lia.
Qed.

Lemma rule_6 : forall A B, forall MA MB, 
rk(B) <= MB -> MB <= MA -> incl A B ->
rk(A) <= MB.
Proof.
intros.
assert(HH := matroid2 A B H1).
lia.
Qed.

Lemma rule_7 : forall A B, forall mA mB, 
rk(B) >= mB -> mB >= mA -> incl B A ->
rk(A) >= mB.
Proof.
intros.
assert(HH := matroid2 B A H1).
lia.
Qed.

Lemma rule_8 : forall A B, forall MA MB, 
rk(A) <= MA -> MA <= MB -> incl B A ->
rk(B) <= MA.
Proof.
intros.
assert(HH := matroid2 B A H1).
lia.
Qed.

Parameter rk_pappus : forall A B C D E F G H I,
rk(A :: B :: nil) = 2 -> rk(A :: C :: nil) = 2 -> rk(A :: D :: nil) = 2 -> 
rk(A :: E :: nil) = 2 -> rk(A :: F :: nil) = 2 ->
rk(B :: C :: nil) = 2 -> rk(B :: D :: nil) = 2 -> rk(B :: E :: nil) = 2 ->
rk(B :: F :: nil) = 2 ->
rk(C :: D :: nil) = 2 -> rk(C :: E :: nil) = 2 -> rk(C :: F :: nil) = 2 ->
rk(D :: E :: nil) = 2 -> rk(D :: F :: nil) = 2 ->
rk(E :: F :: nil) = 2 ->
rk(A :: B :: C :: nil) = 2 -> rk(D :: E :: F :: nil) = 2 -> 
rk(A :: E :: G :: nil) = 2 -> rk(B :: D :: G :: nil) = 2 ->
rk(A :: F :: H :: nil) = 2 -> rk(C :: D :: H :: nil) = 2 ->
rk(B :: F :: I :: nil) = 2 -> rk(C :: E :: I :: nil) = 2 -> rk(G :: H :: I :: nil) = 2.


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


