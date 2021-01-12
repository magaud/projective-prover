Require Import lemmas_automation_g.


(* dans la couche 0 *)
Lemma LP2 : forall P1 P2 P3 P4 ,
rk(P1 :: P3 ::  nil) = 2 -> rk(P1 :: P2 :: P4 ::  nil) = 3 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P3 :: P4 ::  nil) = 2 -> rk(P2 ::  nil) = 1.
Proof.

intros P1 P2 P3 P4 
HP1P3eq HP1P2P4eq HP3P4eq HP1P3P4eq .

assert(HP2M : rk(P2 ::  nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
assert(HP2m : rk(P2 ::  nil) >= 1) by (solve_hyps_min HP2eq HP2m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LP1P3 : forall P1 P2 P3 P4 ,
rk(P1 :: P3 ::  nil) = 2 -> rk(P1 :: P2 :: P4 ::  nil) = 3 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P3 :: P4 ::  nil) = 2 -> rk(P1 :: P3 ::  nil) = 2.
Proof.

intros P1 P2 P3 P4 
HP1P3eq HP1P2P4eq HP3P4eq HP1P3P4eq .

assert(HP1P3M : rk(P1 :: P3 ::  nil) <= 2) by (solve_hyps_max HP1P3eq HP1P3M2).
assert(HP1P3m : rk(P1 :: P3 ::  nil) >= 1) by (solve_hyps_min HP1P3eq HP1P3m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LP1P2P4 : forall P1 P2 P3 P4 ,
rk(P1 :: P3 ::  nil) = 2 -> rk(P1 :: P2 :: P4 ::  nil) = 3 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P3 :: P4 ::  nil) = 2 -> rk(P1 :: P2 :: P4 ::  nil) = 3.
Proof.

intros P1 P2 P3 P4 
HP1P3eq HP1P2P4eq HP3P4eq HP1P3P4eq .

assert(HP1P2P4M : rk(P1 :: P2 :: P4 ::  nil) <= 3) by (solve_hyps_max HP1P2P4eq HP1P2P4M3).
assert(HP1P2P4m : rk(P1 :: P2 :: P4 ::  nil) >= 1) by (solve_hyps_min HP1P2P4eq HP1P2P4m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LP1P3P4 : forall P1 P2 P3 P4 ,
rk(P1 :: P3 ::  nil) = 2 -> rk(P1 :: P2 :: P4 ::  nil) = 3 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P3 :: P4 ::  nil) = 2 -> rk(P1 :: P3 :: P4 ::  nil) = 2.
Proof.

intros P1 P2 P3 P4 
HP1P3eq HP1P2P4eq HP3P4eq HP1P3P4eq .

assert(HP1P3P4M : rk(P1 :: P3 :: P4 ::  nil) <= 3) by (solve_hyps_max HP1P3P4eq HP1P3P4M3).
assert(HP1P3P4m : rk(P1 :: P3 :: P4 ::  nil) >= 1) by (solve_hyps_min HP1P3P4eq HP1P3P4m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LP1P2P3P4 : forall P1 P2 P3 P4 ,
rk(P1 :: P3 ::  nil) = 2 -> rk(P1 :: P2 :: P4 ::  nil) = 3 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P3 :: P4 ::  nil) = 2 -> rk(P1 :: P2 :: P3 :: P4 ::  nil) = 3.
Proof.

intros P1 P2 P3 P4 
HP1P3eq HP1P2P4eq HP3P4eq HP1P3P4eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour P1P2P3P4 requis par la preuve de (?)P1P2P3P4 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour P1P2P3P4 requis par la preuve de (?)P1P2P3P4 pour la règle 5  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 4 pour P1P2P3P4 requis par la preuve de (?)P1P2P3P4 pour la règle 1  *)
(* Application de la règle 1 code (5 dans la thèse) conclusion AUB *)
(* marque des antécédents A B AiB : 4 4 et 5*)
assert(HP1P2P3P4M3 : rk(P1 :: P2 :: P3 :: P4 :: nil) <= 3).
{
	try assert(HP2eq : rk(P2 :: nil) = 1) by (apply LP2 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) ;try assumption).
	assert(HP2Mtmp : rk(P2 :: nil) <= 1) by (solve_hyps_max HP2eq HP2M1).
	try assert(HP1P3P4eq : rk(P1 :: P3 :: P4 :: nil) = 2) by (apply LP1P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) ;try assumption).
	assert(HP1P3P4Mtmp : rk(P1 :: P3 :: P4 :: nil) <= 2) by (solve_hyps_max HP1P3P4eq HP1P3P4M2).
	assert(Hmtmp : rk(nil) >= 0) by (solve_hyps_min Hnuleq Hm).
	assert(Hincl : incl (nil) (list_inter (P2 :: nil) (P1 :: P3 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P2 :: P1 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P2 :: P1 :: P3 :: P4 :: nil) ((P2 :: nil) ++ (P1 :: P3 :: P4 :: nil))) by (clear_all_rk;my_inO).
	assert(HT := rule_1 (P2 :: nil) (P1 :: P3 :: P4 :: nil) (nil) 1 2 0 HP2Mtmp HP1P3P4Mtmp Hmtmp Hincl);
	rewrite <-HT2 in HT;try rewrite <-HT1 in HT;apply HT.
}
try clear HP2M1. try clear HP2M2. try clear HP2M3. try clear HP2m4. try clear HP2m3. try clear HP2m2. try clear HP2m1. 

(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HP1P2P3P4m2 : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 2).
{
	try assert(HP1P3eq : rk(P1 :: P3 :: nil) = 2) by (apply LP1P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) ;try assumption).
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P2 :: P3 :: P4 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HP1P2P3P4m3 : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 3).
{
	try assert(HP1P2P4eq : rk(P1 :: P2 :: P4 :: nil) = 3) by (apply LP1P2P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) ;try assumption).
	assert(HP1P2P4mtmp : rk(P1 :: P2 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P4eq HP1P2P4m3).
	assert(Hcomp : 3 <= 3) by (repeat constructor).
	assert(Hincl : incl (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P2 :: P4 :: nil) (P1 :: P2 :: P3 :: P4 :: nil) 3 3 HP1P2P4mtmp Hcomp Hincl);apply HT.
}
try clear HP1P2P4M1. try clear HP1P2P4M2. try clear HP1P2P4M3. try clear HP1P2P4m4. try clear HP1P2P4m3. try clear HP1P2P4m2. try clear HP1P2P4m1. 

assert(HP1P2P3P4M : rk(P1 :: P2 :: P3 :: P4 ::  nil) <= 4) by (apply rk_upper_dim).
assert(HP1P2P3P4m : rk(P1 :: P2 :: P3 :: P4 ::  nil) >= 1) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m1).
intuition.
Qed.

(* dans la couche 0 *)
Lemma LP1P2P3 : forall P1 P2 P3 P4 ,
rk(P1 :: P3 ::  nil) = 2 -> rk(P1 :: P2 :: P4 ::  nil) = 3 -> rk(P3 :: P4 ::  nil) = 2 ->
rk(P1 :: P3 :: P4 ::  nil) = 2 -> rk(P1 :: P2 :: P3 ::  nil) = 3.
Proof.

intros P1 P2 P3 P4 
HP1P3eq HP1P2P4eq HP3P4eq HP1P3P4eq .

(* dans constructProofaux(), preuve de 2 <= rg <= 3 pour P1P2P3 requis par la preuve de (?)P1P2P3 pour la règle 2  *)
(* dans constructProofaux(), preuve de 1 <= rg <= 3 pour P1P2P3 requis par la preuve de (?)P1P2P3 pour la règle 5  *)
(* Application de la règle 5 code (1 ou 2 dans la thèse) *)
(* marque de l'antécédent : 4 *)
assert(HP1P2P3m2 : rk(P1 :: P2 :: P3 :: nil) >= 2).
{
	try assert(HP1P3eq : rk(P1 :: P3 :: nil) = 2) by (apply LP1P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) ;try assumption).
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hcomp : 2 <= 2) by (repeat constructor).
	assert(Hincl : incl (P1 :: P3 :: nil) (P1 :: P2 :: P3 :: nil)) by (repeat clear_all_rk;my_inO).
	assert(HT := rule_5 (P1 :: P3 :: nil) (P1 :: P2 :: P3 :: nil) 2 2 HP1P3mtmp Hcomp Hincl);apply HT.
}


(* Application de la règle 2 code (7 ou 8 dans la thèse) conclusion A*)
(* marque des antécédents AUB AiB B: 4 4 et 4*)
assert(HP1P2P3m3 : rk(P1 :: P2 :: P3 :: nil) >= 3).
{
	try assert(HP1P3P4eq : rk(P1 :: P3 :: P4 :: nil) = 2) by (apply LP1P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) ;try assumption).
	assert(HP1P3P4Mtmp : rk(P1 :: P3 :: P4 :: nil) <= 2) by (solve_hyps_max HP1P3P4eq HP1P3P4M2).
	try assert(HP1P2P3P4eq : rk(P1 :: P2 :: P3 :: P4 :: nil) = 3) by (apply LP1P2P3P4 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) ;try assumption).
	assert(HP1P2P3P4mtmp : rk(P1 :: P2 :: P3 :: P4 :: nil) >= 3) by (solve_hyps_min HP1P2P3P4eq HP1P2P3P4m3).
	try assert(HP1P3eq : rk(P1 :: P3 :: nil) = 2) by (apply LP1P3 with (P1 := P1) (P2 := P2) (P3 := P3) (P4 := P4) ;try assumption).
	assert(HP1P3mtmp : rk(P1 :: P3 :: nil) >= 2) by (solve_hyps_min HP1P3eq HP1P3m2).
	assert(Hincl : incl (P1 :: P3 :: nil) (list_inter (P1 :: P2 :: P3 :: nil) (P1 :: P3 :: P4 :: nil))) by (repeat clear_all_rk;my_inO).
	assert(HT1 : equivlist (P1 :: P2 :: P3 :: P4 :: nil) (P1 :: P2 :: P3 :: P1 :: P3 :: P4 :: nil)) by (clear_all_rk;my_inO).
	assert(HT2 : equivlist (P1 :: P2 :: P3 :: P1 :: P3 :: P4 :: nil) ((P1 :: P2 :: P3 :: nil) ++ (P1 :: P3 :: P4 :: nil))) by (clear_all_rk;my_inO).
	try rewrite HT1 in HP1P2P3P4mtmp;try rewrite HT2 in HP1P2P3P4mtmp.
	assert(HT := rule_2 (P1 :: P2 :: P3 :: nil) (P1 :: P3 :: P4 :: nil) (P1 :: P3 :: nil) 3 2 2 HP1P2P3P4mtmp HP1P3mtmp HP1P3P4Mtmp Hincl);apply HT.
}


assert(HP1P2P3M : rk(P1 :: P2 :: P3 ::  nil) <= 3) by (solve_hyps_max HP1P2P3eq HP1P2P3M3).
assert(HP1P2P3m : rk(P1 :: P2 :: P3 ::  nil) >= 1) by (solve_hyps_min HP1P2P3eq HP1P2P3m1).
intuition.
Qed.

