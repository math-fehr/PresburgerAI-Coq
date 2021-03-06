From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import eqtype seq ssrnat.

Require Import Lia.
Require Import Omega.

Ltac rewrite_is_true :=
  repeat match goal with
         | [ H: is_true ?e |- context[?e] ] => rewrite H
         | [ H: is_true (negb ?e) |- context[?e] ] => move: (H) => /negb_true_iff ->
         | _ => rewrite /=
         end.

Ltac simpleq :=
  repeat match goal with
         | [ H: is_true (?x != ?y) |- context[?y == ?x] ] => rewrite eq_sym in H; rewrite_is_true; rewrite eq_sym in H
         | [ H: is_true (?x == ?y) |- context[?y == ?x] ] => rewrite eq_sym in H; rewrite_is_true; rewrite eq_sym in H
         | [ |- context[?x == ?x] ] => rewrite eq_refl
         | _ => rewrite /=
         end.

Ltac reflect_ne_in tac :=
  repeat match goal with
         | [ H: ?x <> ?y |- _ ] => move => /eqP in H
         | _ => tac
         end.

Ltac reflect_ne :=
  repeat match goal with
         | [ H: ?x <> ?y |- _ ] => move => /eqP in H
         | _ => idtac
         end.

Ltac simpl_seq :=
  repeat match goal with
         | [ H: is_true (?x == ?y) |- context[?x \in (?y :: ?l)] ] => rewrite in_cons
         | [ H: is_true (?y == ?x) |- context[?x \in (?y :: ?l)] ] => rewrite in_cons
         | [ H: is_true (?x != ?y) |- context[?x \in (?y :: ?l)] ] => rewrite in_cons
         | [ H: is_true (?y != ?x) |- context[?x \in (?y :: ?l)] ] => rewrite in_cons
         | [ H: is_true (?x \in ?l) |- context[?x \in (?y :: ?l)] ] => rewrite in_cons
         | [ H: is_true (?x \notin ?l) |- context[?x \in (?y :: ?l)] ] => rewrite in_cons
         | [ |- context[?x \in (?x :: ?l)] ] => rewrite in_cons; rewrite eq_refl
         | [ H: is_true (?x \notin ?y :: ?z) |- _ ] =>
           let Hne := fresh "H" in
           rewrite in_cons in H; move: H; move => /norP [Hne H]
         | [ H: is_true (?x \notin ?y ++ ?z) |- _ ] =>
           let Hne := fresh "H" in
           rewrite mem_cat in H; move: H; move => /norP [Hne H]
         | [ H: is_true (?x \in iota 0 ?n) |- _ ] =>
           let H' := fresh "H" in rewrite mem_iota add0n in H; move => /andP in H; destruct H as [_ H']
         | [ |- is_true (?x \in iota 0 ?n) ] => rewrite mem_iota add0n; apply /andP; split; [ apply leq0n | auto ]
         | _ => idtac
         end.

Ltac simpl_bool :=
  repeat match goal with
         | [ |- context[_ && true] ] => rewrite Bool.andb_true_r
         | [ |- context[_ && false] ] => rewrite Bool.andb_false_r
         | [ |- context[_ || true] ] => rewrite Bool.orb_true_r
         | [ |- context[_ || false] ] => rewrite Bool.orb_false_r
         | _ => rewrite /=
         end.

Ltac divide_hypotheses :=
  repeat match goal with
         | [ H: is_true (?H1 && ?H2) |- _ ] =>
           let H1 := fresh "H" in let H2 := fresh "H" in move: H => /andP [H1 H2]
         | [ H: is_true (~~ (?H1 || ?H2)) |- _] =>
           let H1 := fresh "H" in let H2 := fresh "H" in move: H => /norP [H1 H2]
         | _ => idtac
         end.

Ltac bigsubst :=
  subst ; match goal with
          | [ H1: ?a = Some ?s1, H2: ?a = Some ?s2 |- _ ] => move: (H1); rewrite H2 => [[Heq]]; bigsubst
          | [ H: Some ?a = Some ?b |- _ ] => case: H => H; bigsubst
          | _ => idtac
          end.

Ltac ssrsubst :=
  repeat match goal with
         | [ H: is_true (?x == ?y) |- _ ] => move => /eqP in H
         | _ => bigsubst
         end.

Ltac solve_contra :=
  match goal with
  | [ H1: is_true ?b, H2: is_true (~~ ?b) |- _ ] => by rewrite H1 in H2
  end.

Ltac remove_SS :=
  repeat match goal with
         | [ H: context[?x.+1 == ?y.+1] |- _ ] => rewrite eqSS in H
         | [ |- context[?x.+1 == ?y.+1] ] => rewrite eqSS
         end.

Ltac to_coq_nat :=
  repeat match goal with
         | [ H: is_true (?x < ?y) |- _ ] => move => /ltP in H
         | [ H: is_true (?x <= ?y) |- _ ] => move => /leP in H
         | [ |- is_true (?x != ?y) ] => apply /eqP
         | [ |- is_true (?x == ?y) ] => apply /eqP
         | [ H: is_true (~~ (?x < ?y)) |- _ ] => rewrite -leqNgt in H; move => /leP in H
         end.

Ltac intro_ne :=
  match goal with
  | [ |- _ <> _ ] => intro
  | _ => idtac
  end.

Ltac case_if :=
  match goal with
  | [ |- context[ if ?c then _ else _ ] ] => let H := fresh "H" in destruct c eqn:H
  end.

Ltac case_match :=
  match goal with
  | [ |- context[ match ?x with _ => _ end] ] => let H := fresh "H" in destruct x eqn:H
  end.

Ltac simplssr_ := rewrite_is_true; simpl_seq; simpl_bool; simpleq.
Ltac simplssr := repeat (reflect_ne_in simplssr_).
Ltac autossr :=
  first [ solve [ try (solve_contra) ; simplssr ; intros ; reflect_ne ; ssrsubst ; simplssr ; first [ by auto | divide_hypotheses ; ssrsubst ; simplssr ; (try solve_contra); by auto ] ] | idtac ].

Ltac liassr := remove_SS ; to_coq_nat ; intros ; intro_ne ; subst ; first [lia | omega ].
