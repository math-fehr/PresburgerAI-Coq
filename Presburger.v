From Coq Require Import ssreflect ssrfun ssrbool.

Require Import String.
Open Scope string_scope.

Class PresburgerSet (s: Type) :=
  {
    eval_point : s -> (string -> nat) -> bool;

    union_set : s -> s -> s;
    union_set_spec : forall p1 p2 x,
        eval_point (union_set p1 p2) x = eval_point p1 x || eval_point p2 x;

    intersect_set : s -> s -> s;
    intersect_set_spec : forall p1 p2 x,
        eval_point (intersect_set p1 p2) x = eval_point p1 x && eval_point p2 x;
  }.
