From Coq Require Import ssreflect ssrfun ssrbool.
Require Export Coq.Sets.Ensembles.

Require Import String.
Open Scope string_scope.

Class PresburgerSet (s: Type) :=
  {
    eval_point : s -> (string -> nat) -> bool;

    empty_set : s;
    empty_set_spec : forall x, eval_point empty_set x = false;

    universe_set : s;
    universe_set_spec : forall x, eval_point universe_set x = true;

    union_set : s -> s -> s;
    union_set_spec : forall p1 p2 x,
        eval_point (union_set p1 p2) x = eval_point p1 x || eval_point p2 x;

    intersect_set : s -> s -> s;
    intersect_set_spec : forall p1 p2 x,
        eval_point (intersect_set p1 p2) x = eval_point p1 x && eval_point p2 x;

    is_subset : s -> s -> bool;
    is_subset_spec : forall p1 p2, is_subset p1 p2 = true <-> forall x, eval_point p1 x = true -> eval_point p2 x = true;
  }.


Theorem is_subset_refl {s: Type} {P : PresburgerSet s} :
  forall p, is_subset p p = true.
Proof.
  move => p.
  apply is_subset_spec => //.
Qed.

Theorem is_subset_trans {s: Type} {P : PresburgerSet s} :
  forall p1 p2 p3, is_subset p1 p2 = true ->
              is_subset p2 p3 = true ->
              is_subset p1 p3 = true.
Proof.
  move => p1 p2 p3 /is_subset_spec H12 /is_subset_spec H23.
  apply is_subset_spec.
  by auto.
Qed.

Theorem is_subset_union_l {s: Type} {P: PresburgerSet s} :
  forall p1 p2, is_subset p1 (union_set p1 p2).
Proof.
  move => p1 p2.
  apply is_subset_spec => x Hp1.
  rewrite union_set_spec Hp1.
  reflexivity.
Qed.

Theorem is_subset_union_r {s: Type} {P: PresburgerSet s} :
  forall p1 p2, is_subset p2 (union_set p1 p2).
Proof.
  move => p1 p2.
  apply is_subset_spec => x Hp2.
  rewrite union_set_spec Hp2.
  by apply orbT.
Qed.


