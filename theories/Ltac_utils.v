(* Ltac tools *)
(* useful link for writing Ltac tactics: http://adam.chlipala.net/cpdt/html/Match.html *)

Require Import lemmas_automation_g.

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

Ltac adapt_goal lref :=
  match goal with |- rk(?e)=?v =>
                  let eqH := fresh in 
                  let e' := reorder Point e lref in
                  (assert (eqH:equivlist e' e) by solve_equivlist; try rewrite <- (rk_compat _ _ eqH))
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
 intros; adapt_goal collect_points; repeat adapt_hyp collect_points; let v := expr_to_apply Point t collect_points in intros; eapply v; eassumption.
