From Coq Require Import ssreflect ssrfun ssrbool.
Require Export PolyAI.TotalMap.
Require Export Coq.Sets.Ensembles.
Require Export Coq.ZArith.BinInt.

Require Import String.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Inductive PwAff :=
| AConst (c: Z)
| AVar (v: string)
| APlus (a1 a2: PwAff)
| AMinus (a1 a2: PwAff)
| AMul (c: Z) (a: PwAff)
| AEq (a1 a2: PwAff)
| ANeq (a1 a2: PwAff)
| ALe (a1 a2: PwAff)
| ALt (a1 a2: PwAff)
| AGe (a1 a2: PwAff)
| AGt (a1 a2: PwAff).

Definition indicator (b: bool) :=
  match b with
  | true => 1
  | false => 0
  end.

Fixpoint eval_aff (a: PwAff) (m: total_map Z) :=
  match a with
  | AConst c => c
  | AVar v => m v
  | APlus a1 a2 => (eval_aff a1 m) + (eval_aff a2 m)
  | AMinus a1 a2 => (eval_aff a1 m) - (eval_aff a2 m)
  | AMul c a => c * (eval_aff a m)
  | AEq a1 a2 => indicator ((eval_aff a1 m) =? (eval_aff a2 m))
  | ANeq a1 a2 => indicator (negb ((eval_aff a1 m) =? (eval_aff a2 m)))
  | ALe a1 a2 => indicator ((eval_aff a1 m) <=? (eval_aff a2 m))
  | ALt a1 a2 => indicator ((eval_aff a1 m) <? (eval_aff a2 m))
  | AGe a1 a2 => indicator ((eval_aff a1 m) >=? (eval_aff a2 m))
  | AGt a1 a2 => indicator ((eval_aff a1 m) >? (eval_aff a2 m))
  end.

Inductive Constraint :=
| CEq (a1 a2: PwAff)
| CNeq (a1 a2: PwAff)
| CLe (a1 a2: PwAff)
| CLt (a1 a2: PwAff)
| CGe (a1 a2: PwAff)
| CGt (a1 a2: PwAff).

Definition eval_constraint (c: Constraint) (m: total_map Z) :=
  match c with
  | CEq a1 a2 => (eval_aff a1 m) =? (eval_aff a2 m)
  | CNeq a1 a2 => negb ((eval_aff a1 m) =? (eval_aff a2 m))
  | CLe a1 a2 => (eval_aff a1 m) <=? (eval_aff a2 m)
  | CLt a1 a2 => (eval_aff a1 m) <? (eval_aff a2 m)
  | CGe a1 a2 => (eval_aff a1 m) >=? (eval_aff a2 m)
  | CGt a1 a2 => (eval_aff a1 m) >? (eval_aff a2 m)
  end.

Class PresburgerSet (s: Type) :=
  {
    eval_set : s -> total_map Z -> bool;

    empty_set : s;
    empty_set_spec : forall x, eval_set empty_set x = false;

    universe_set : s;
    universe_set_spec : forall x, eval_set universe_set x = true;

    union_set : s -> s -> s;
    union_set_spec : forall p1 p2 x,
        eval_set (union_set p1 p2) x = eval_set p1 x || eval_set p2 x;

    intersect_set : s -> s -> s;
    intersect_set_spec : forall p1 p2 x,
        eval_set (intersect_set p1 p2) x = eval_set p1 x && eval_set p2 x;

    is_subset : s -> s -> bool;
    is_subset_spec : forall p1 p2, is_subset p1 p2 = true <->
                              forall x, eval_set p1 x = true -> eval_set p2 x = true;

    set_from_constraint : Constraint -> s;
    set_from_constraint_spec : forall c x, eval_set (set_from_constraint c) x = eval_constraint c x;

    set_project_out : s -> string -> s;
    set_project_out_spec : forall p d x, eval_set (set_project_out p d) x = true <->
                                    exists v, eval_set p (d !-> v; x) = true;
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

Theorem constraint_one_variable_correct {s: Type} {P: PresburgerSet s} :
  forall m p x, eval_set p m = eval_set (intersect_set (set_from_constraint (CEq (AVar x) (AConst (m x)))) p) m.
Proof.
  move => m p x.
  rewrite intersect_set_spec set_from_constraint_spec.
    by rewrite /= Z.eqb_refl //.
Qed.

