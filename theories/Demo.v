From Tuto0 Require Export Loader.
Require Import Ltac_utils.

Locate Point.

(* a small example *)
Lemma ex : forall A B C D : Point, forall n m:nat,forall f:nat->nat,
      f(n)=m ->
      (exists p:nat, p=m) ->
    rk(A::B::C::D::nil) = 3 ->
    True ->
    rk(A::C::D::nil) = 2 ->
    rk(A::C::nil) = 2 ->
    rk(C::D::nil) = 2 ->
    (exists e:Point, rk(C::D::e::nil)=7) -> 
    rk(A::B::C::nil) = 3.
Proof.
  intros.
  pprove.
  Require Import pprove_ex.
  solve_using LP1P2P3.
Qed.

Lemma ex1 : forall A B C D:Point,
    rk(A::B::D::nil) = 3 ->
    rk(A::C::D::nil) = 2 ->
    rk(A::C::nil) = 2 ->
    rk(C::D::nil) = 2 ->
    rk(A::B::C::nil) = 3.
Proof.
  intros.
  (* call the prover *)
  pprove.
  Require Import pprove_ex1.
  solve_using LP1P2P3. 
Qed.
Check ex1.

Lemma ex2 : forall A B C D:Point,
    rk(A::D::B::nil) = 3 ->
    rk(A::C::D::nil) = 2 ->
    rk(C::A::nil) = 2 ->
    rk(C::D::nil) = 2 ->
    rk(A::C::B::nil) = 3.
Proof.
  intros.
  (* call the prover *)
  pprove.
  Require Import pprove_ex2.
  solve_using LP1P2P3. 
Qed.
Check ex2.

Lemma ex3 : forall A B C D ,
rk(A :: C ::  nil) = 2 -> rk(A :: B :: D ::  nil) = 2 -> rk(C :: D ::  nil) = 2 ->
rk(A :: C :: D ::  nil) = 2 -> rk(C :: A ::  nil) = 2.
Proof.
  intros.
  pprove.
  Require Import pprove_ex3.
  solve_using LP1P3. 
Qed.

Definition triple (X Y Z : Point) : (list Point) := (X :: Y :: Z :: nil).

Lemma desargues : forall a b c A B C alpha beta gamma O : Point,

forall raAO : rk(triple a A O)=2, 
forall rbBO : rk(triple b B O)=2, 
forall rcCO : rk(triple c C O)=2, 
forall rABC : rk(triple A B C)=3, 
forall rabc : rk(triple a b c)=3, 

forall rABCabc : rk(A::B::C::a::b::c::nil)=4, 

forall rABgamma : rk(triple A B gamma)=2,
forall rabgamma : rk(triple a b gamma)=2,

forall rACbeta : rk(triple A C beta)=2,
forall racbeta : rk(triple a c beta)=2,

forall rBCalpha : rk(triple B C alpha)=2,
forall rbcalpha : rk(triple b c alpha)=2,



forall raA : rk(a:: A :: nil)=2,
forall rcC : rk(c:: C :: nil)=2,
forall rbB : rk(b:: B:: nil)=2,
  
  rk(O::a::nil)=2->
  rk(O::b::nil)=2->
  rk(O::c::nil)=2->
  rk(O::A::nil)=2->
  rk(O::B::nil)=2->
  rk(O::C::nil)=2->
  
  rk ( alpha ::beta ::gamma::nil) = 2.
Proof.
  unfold triple.
  intros.
  pprove.
  Require Import pprove_desargues. 
  solve_using LP7P8P9.
Qed.
  
