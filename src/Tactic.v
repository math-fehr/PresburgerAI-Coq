From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype.

Ltac rewrite_is_true :=
  repeat match goal with
         | [ H: is_true ?e |- context[?e] ] => rewrite H
         | [ H: is_true (negb ?e) |- context[?e] ] => move => /negb_true_iff in H; rewrite H; move => /negb_true_iff in H
         | _ => rewrite /=
         end.

Ltac simpleq :=
  repeat match goal with
         | [ H: is_true (?x != ?y) |- context[?y == ?x] ] => rewrite eq_sym in H; rewrite_is_true; rewrite eq_sym in H
         | [ H: is_true (?x == ?y) |- context[?y == ?x] ] => rewrite eq_sym in H; rewrite_is_true; rewrite eq_sym in H
         | [ |- context[?x == ?x] ] => rewrite (eq_refl _ ?x)
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

Ltac simplssr := rewrite_is_true; simpleq.
