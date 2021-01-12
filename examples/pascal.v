Require Import lemmas_automation_g.

Lemma LP1P2P3 : forall P1 P2 P3 P4 P5 P6 P7 P8 ,
rk(P2 :: P3 ::  nil) = 2 -> rk(P2 :: P4 ::  nil) = 2 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P2 :: P3 :: P4 ::  nil) = 2 -> rk(P1 :: P2 :: P5 ::  nil) = 3 -> rk(P1 :: P3 :: P6 ::  nil) = 3 ->
rk(P5 :: P6 ::  nil) = 2 -> rk(P1 :: P4 :: P7 ::  nil) = 3 -> rk(P5 :: P7 ::  nil) = 2 ->
rk(P6 :: P7 ::  nil) = 2 -> rk(P1 :: P5 :: P6 :: P7 ::  nil) = 2 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 :: P7 :: P8 ::  nil) = 4 ->

rk(P1 :: P2 :: P3 ::  nil) = 2.
Proof.

intros P1 P2 P3 P4 P5 P6 P7 P8 
HP2P3eq HP2P4eq HP3P4eq HP1P2P3P4eq HP1P2P5eq HP1P3P6eq HP5P6eq HP1P4P7eq HP5P7eq HP6P7eq
HP1P5P6P7eq HP1P2P3P4P5P6P7P8eq .

assert(HP1P2P3m2 : rk(P1 :: P2 :: P3 :: nil) >= 2).
{
	try assert(HP2P3eq : rk(P2 :: P3 :: nil) = 2) by (apply LP2P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP2P3mtmp : rk(P2 :: P3 :: nil) >= 2) by (solve_hyps_min HP2P3eq HP2P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P2 :: P3 :: nil) (P1 :: P2 :: P3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P2 :: P3 :: nil) (P1 :: P2 :: P3 :: nil) 2 2 HP2P3mtmp Hcomp Hincl);apply HT.
}
try clear HP2P3M1. try clear HP2P3M2. try clear HP2P3M3. try clear HP2P3m4. try clear HP2P3m3. try clear HP2P3m2. try clear HP2P3m1. 

assert(HP1P2P3M2 : rk(P1 :: P2 :: P3 :: nil) <= 2).
{
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 2) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) (P5 := P5) (P6 := P6) (P7 := P7) (P8 := P8) ;try assumption).
	assert(HP1P2P3P4Mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) <= 2) by (solve_hyps_max HP1P2P3P4eq HP1P2P3P4M2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_6 (P1 :: P2 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: nil) 2 2 HP1P2P3P4Mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P3P4M1. try clear HP1P2P3P4M2. try clear HP1P2P3P4M3. try clear HP1P2P3P4m4. try clear HP1P2P3P4m3. try clear HP1P2P3P4m2. try clear HP1P2P3P4m1. 

assert(HP1P2P3M : rk(P1 :: P2 :: P3 ::  nil) <= 3) by (solve_hyps_max HP1P2P3eq HP1P2P3M3).
assert(HP1P2P3m : rk(P1 :: P2 :: P3 ::  nil) >= 1) by (solve_hyps_min HP1P2P3eq HP1P2P3m1).
intuition.
Qed.

