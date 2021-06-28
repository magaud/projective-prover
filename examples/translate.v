(*Require Import ssreflect ssrfun ssrbool.*)
From Tuto0 Require Export Loader.
Require Import Ltac_utils.

(*Require Import Setoid.
Require Import List.
*)
Parameter Point : Type.
Parameter Line: Type.

Parameter rk2 : Point -> Point -> nat.
Parameter rk3 : Point -> Point -> Point -> nat.

Parameter eqP : Point -> Point -> bool.
Parameter eqL : Line -> Line -> bool.

Parameter incid_lp : Point -> Line -> Prop.

Lemma two_points_on_l : forall l:Line, {x:Point & {y:Point & rk2 x y  = 2}}.
Admitted.

Definition on_line := fun A B C l => incid_lp A l /\ incid_lp B l /\ incid_lp C l.
Definition collinear A B C :=  exists l, incid_lp A l /\ incid_lp B l /\ incid_lp C l.

Lemma collinear_spec : forall A B C, collinear A B C <-> rk3 A B C = 2.
Admitted.


Lemma non_collinear_spec : forall A B C, ~collinear A B C <-> rk3 A B C = 3.
Admitted.



Lemma eq_spec : forall A B, A = B <-> rk2 A B = 1.
Admitted.

Lemma diff_spec : forall A B:Point, A<> B <-> rk2 A B = 2.
Admitted.

Lemma incid_lp_spec : forall L_p1 L_p2 L X,
      L_p1 = (projT1 (two_points_on_l L)) ->
      L_p2 = projT1 (projT2 (two_points_on_l L)) ->
      incid_lp X L <-> rk3 X L_p1 L_p2 = 3.
Admitted.

Ltac revert_hyps :=
  match goal with L:Line |- _ => fail 0 | P:Point |- _ => fail 0 | H:_ |- _ => revert H end.

Ltac use L := let x1 := fresh L "_p1" in
              let x1' := fresh L "_p1'" in 
                  let x2 := fresh L "_p2" in
                  let H:= fresh "__" in
                  let Heq := fresh "___" in 
                  pose (x1:=(projT1 (two_points_on_l L)));
                (*  assert (x1':Point) by exact (projT1 (two_points_on_l L));
                  assert (Heq:x1=x1') by admit;
try rewrite -> Heq in *;*)
                   pose (x2:=(projT1 (projT2 (two_points_on_l L))));
                   repeat (rewrite (incid_lp_spec x1 x2 L) in *;[idtac | trivial | trivial]); generalize dependent x1; generalize dependent x2; clear L; intros.

Ltac add_to_distinct_list x xs := 
match xs with
 | nil     => constr:(x::xs)
 | x::_    => fail 1
 | ?y::?ys => let zs := add_to_distinct_list x ys in constr:(y::zs)
end.

Ltac collect_Lines_list xs :=
match goal with
 | [ N : Line |- _ ] => let ys := add_to_distinct_list N xs
                       in collect_Lines_list ys
 | _                => xs
end.

Ltac collect_Lines := collect_Lines_list (@nil Line).

Ltac on_all_lines l :=
  match l with
    nil => idtac "end"
  | ?x::?xs => use x; on_all_lines xs
  end.

Ltac translate :=
  intros;
  repeat rewrite non_collinear_spec in *;
  repeat rewrite collinear_spec in *;
  repeat rewrite diff_spec in *;
  repeat rewrite eq_spec in *;
  unfold on_line in *;
  on_all_lines (collect_Lines).

Lemma x : forall l:Line, True.
  intros.
use l.
Admitted.
       
Theorem Desargues : 
 forall O P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R',
((on_line P Q gamma lPQ) /\ (on_line P' Q' gamma lP'Q')) /\
((on_line P R beta lPR) /\ (on_line P' R' beta lP'R')) /\
((on_line Q R alpha lQR) /\ (on_line Q' R' alpha lQ'R')) /\
((on_line O P P' lP) /\ (on_line O Q Q' lQ) /\(on_line O R R' lR)) /\ 
~collinear O P Q /\  ~collinear O P R /\ ~collinear O Q R /\ 
~collinear P Q R /\ ~collinear P' Q' R' /\ ((~P=P')\/(~Q=Q')\/(~R=R')) ->
collinear alpha beta gamma.
Proof.
  translate.

  intuition.

  (* énoncé de Desargues avec des rangs *)

  (* TODO *)

Definition dist_4p  (A B C D:Point) : bool :=
  (negb (eqP A B)) && (negb (eqP A C)) && (negb (eqP A D))
                     && (negb (eqP B C)) && (negb (eqP B D)) && (negb (eqP C D)).

Definition dist_3p  (A B C :Point) : bool := (negb (eqP A B)) && (negb (eqP A C)) && (negb (eqP B C)).


Definition dist_3l (A B C :Line) : bool :=
  (negb (eqL A B)) && (negb (eqL A C)) && (negb (eqL B C)).

