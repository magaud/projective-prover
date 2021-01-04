Parameter Point:Set.
Parameter rk : list Point -> nat.

Definition triple (X Y Z : Point) : (list Point) := (X :: Y :: Z :: nil).

Lemma r2 : forall x y, rk (x :: y :: nil) = rk (y :: x ::nil).
Admitted.

Lemma r3 : forall x y t, rk (x :: y :: t :: nil) = rk (y :: x :: t :: nil).
Admitted.

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
intros; eapply LP7P8P9.
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
