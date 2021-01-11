Require Export List.
Require Export Morphisms.

Parameter Point:Set.
Parameter eq_Point_dec : forall x y:Point, {x=y}+{x<>y}.

Parameter rk : list Point -> nat.

Definition equivlist (l l':list Point) := forall x, List.In x l <-> List.In x l'.

Parameter rk_compat : forall x x', equivlist x x' -> rk x = rk x'.

Global Instance rk_morph : Proper (equivlist ==> (@Logic.eq nat)) rk.
Proof.
intros;repeat red.
apply rk_compat.
Qed.

Definition triple (X Y Z : Point) : (list Point) := (X :: Y :: Z :: nil).

Lemma LP7P8P9 : forall P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 ,
rk(P1 :: P2 :: P3 ::  nil) = 3 -> rk(P1 :: P4 ::  nil) = 2 -> rk(P2 :: P5 ::  nil) = 2 ->
rk(P3 :: P6 ::  nil) = 2 -> rk(P4 :: P5 :: P6 ::  nil) = 3 -> rk(P1 :: P2 :: P3 :: P4 :: P5 :: P6 ::  nil) = 4 ->
rk(P2 :: P3 :: P7 ::  nil) = 2 -> rk(P5 :: P6 :: P7 ::  nil) = 2 -> rk(P1 :: P3 :: P8 ::  nil) = 2 ->
rk(P4 :: P6 :: P8 ::  nil) = 2 -> rk(P1 :: P2 :: P9 ::  nil) = 2 -> rk(P4 :: P5 :: P9 ::  nil) = 2 ->
rk(P1 :: P10 ::  nil) = 2 -> rk(P2 :: P10 ::  nil) = 2 -> rk(P3 :: P10 ::  nil) = 2 ->
rk(P4 :: P10 ::  nil) = 2 -> rk(P1 :: P4 :: P10 ::  nil) = 2 -> rk(P5 :: P10 ::  nil) = 2 ->
rk(P2 :: P5 :: P10 ::  nil) = 2 -> rk(P6 :: P10 ::  nil) = 2 -> rk(P3 :: P6 :: P10 ::  nil) = 2 ->
rk(P7 :: P8 :: P9 ::  nil) = 2.
Proof.
Admitted.

(* Ltac tools *)
(* super utile : http://adam.chlipala.net/cpdt/html/Match.html *)

Ltac add_to_distinct_list x xs := 
match xs with
 | nil     => constr:(x::xs)
 | x::_    => fail 1
 | ?y::?ys => let zs := add_to_distinct_list x ys in constr:(y::zs)
end.

Ltac collect_points_list xs :=
match goal with
 | [ N : Point |- _ ] => let ys := add_to_distinct_list N xs
                       in collect_points_list ys
 | _                => xs
end.

Ltac lrev T l m :=
  match l with
    nil => m
   | ?x::?xs => lrev T xs (x::m)
  end.

Ltac collect_points :=
  let c := collect_points_list (@nil Point) in
  lrev Point c (@nil Point).

Ltac belongs x l :=
   match l with
    nil => constr:(@nil Point)
  | x::_ => constr:(x::nil)
  | _::?ys => belongs x ys
(*  | _ => idtac "erreur"*)
  end.
  
Ltac reorder T l lref :=
  match lref with
    nil => constr:(@nil T)
  | ?x::?xs => let be := (belongs x l) in
               match be with
                 nil =>  let res := reorder T l xs in res
               | _::_ => let res := reorder T l xs in let res2 := constr:(x::res) in res2
               end
  end.
                   
Ltac solve_equivlist :=
unfold equivlist; split; intros;
                     repeat match goal with
                     | H:In ?x (_::_) |- _ =>
             destruct (in_inv H); subst; clear H;
             try solve [repeat (try apply in_eq; apply in_cons)]
       | H:In ?x nil |- _ => inversion H
       end.

Ltac adapt_hyp lref :=
  match goal with f:(rk(?e) = ?v) |- _ =>
                  let H':= fresh f in
                  let eqH := fresh f in 
                  let e' := reorder Point e lref in
                  (*idtac e;idtac e';*)
                  (assert (eqH:equivlist e' e) by solve_equivlist;
                   try rewrite <- (rk_compat _ _ eqH) in f); clear eqH; revert f
  end.

Ltac expr_to_apply A t l :=
    match l with
      nil => t
    | ?x::?xs => expr_to_apply A constr:(t x) xs
                   end.

Ltac solve_using t :=
 intros; repeat adapt_hyp collect_points; let v := expr_to_apply Point t collect_points in intros; eapply v; eassumption.

  
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
 (* rk(a::b::c::nil)=3 ->
  rk(A::B::C::nil)=3 ->*)
  
  rk(O::a::nil)=2->
  rk(O::b::nil)=2->
  rk(O::c::nil)=2->
  rk(O::A::nil)=2->
  rk(O::B::nil)=2->
  rk(O::C::nil)=2->
  
  rk ( alpha ::beta ::gamma::nil) = 2.
Proof.
  unfold triple in *.
  solve_using LP7P8P9.
Qed.

(* manual proof *)
eapply (LP7P8P9 a b c A B C alpha beta gamma O); try eassumption.
  intros; eapply LP7P8P9.
  eassumption.
eapply rABC. 
rewrite r2.
apply raA.
rewrite r2.
apply rbB.
rewrite r2.
apply rcC.
eapply rabc.
eapply rABCabc.
eapply  rBCalpha.
eapply rbcalpha.
eapply  rACbeta.
eapply racbeta.
eapply  rABgamma.
eapply  rabgamma.
rewrite r2.
apply H2.
rewrite r2.
apply H3.
rewrite r2.
apply H4.
rewrite r2.
apply H.
rewrite r3.
apply raAO.
rewrite r2.
apply H0.
rewrite r3.
apply rbBO.
rewrite r2.
apply H1.
rewrite r3.
apply rcCO.
Qed.
