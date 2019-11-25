From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype seq.

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
         | [ |- context[_ \in (_ :: _)] ] => rewrite in_cons
         | [ H: ?x::?y \notin ?z |- _ ] =>
           let Hne := fresh "H" in
           rewrite in_cons in H; move: H; move => /norP [Hne H]
         | _ => idtac
         end.

Ltac simpl_bool :=
  repeat match goal with
         | [ |- context[_ && true] ] => rewrite Bool.andb_true_r
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

Ltac ssrsubst :=
  repeat match goal with
         | [ H: is_true (?x == ?y) |- _ ] => move => /eqP in H
         | _ => subst
         end.

Ltac simplssr_ := rewrite_is_true; simpl_seq; simpl_bool; simpleq.
Ltac simplssr := repeat (reflect_ne_in simplssr_).
Ltac autossr :=
  first [ solve [ simplssr ; intros ; reflect_ne ; ssrsubst ; simplssr ; first [ by auto | divide_hypotheses ; ssrsubst ; simplssr ; by auto ] ] | idtac ].
