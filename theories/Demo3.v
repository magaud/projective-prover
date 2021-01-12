From Tuto0 Require Export Loader.
Require Import Ltac_utils.

Lemma LP1P2P3 : forall P1 P2 P3 P4 P5 P6 P7 P8 ,
rk(P2 :: P3 ::  nil) = 2 -> rk(P2 :: P4 ::  nil) = 2 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P2 :: P3 :: P4 ::  nil) = 2 -> rk(P1 :: P2 :: P5 ::  nil) = 3 -> rk(P1 :: P3 :: P6 ::  nil) = 3 ->
rk(P5 :: P6 ::  nil) = 2 -> rk(P1 :: P4 :: P7 ::  nil) = 3 -> rk(P5 :: P7 ::  nil) = 2 ->
rk(P6 :: P7 ::  nil) = 2 -> rk(P1 :: P5 :: P6 :: P7 ::  nil) = 2 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 ::  nil) = 4 ->

rk(P1 :: P2 :: P3 ::  nil) = 2.
Proof.
  intros.
  pprove.
  Require Import pprove_LP1P2P3.  
  solve_using LP1P2P3.
Qed.


Lemma LP1P2P4 : forall P1 P2 P3 P4 P5 P6 P7 P8 ,
rk(P2 :: P3 ::  nil) = 2 -> rk(P2 :: P4 ::  nil) = 2 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P2 :: P3 :: P4 ::  nil) = 2 -> rk(P1 :: P2 :: P5 ::  nil) = 3 -> rk(P1 :: P3 :: P6 ::  nil) = 3 ->
rk(P5 :: P6 ::  nil) = 2 -> rk(P1 :: P4 :: P7 ::  nil) = 3 -> rk(P5 :: P7 ::  nil) = 2 ->
rk(P6 :: P7 ::  nil) = 2 -> rk(P1 :: P5 :: P6 :: P7 ::  nil) = 2 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 ::  nil) = 4 ->

rk(P1 :: P2 :: P4 ::  nil) = 2.
Proof.
  intros.
  pprove.
  Require Import pprove_LP1P2P4.  
  solve_using LP1P2P4.
Qed.

