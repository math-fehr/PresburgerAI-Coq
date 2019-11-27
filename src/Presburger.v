From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export TotalMap ssrZ ssrstring Tactic.
Require Export Coq.Sets.Ensembles.
Require Export Coq.ZArith.BinInt.

Require Import String.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* An affine function *)

Inductive Aff :=
| AConst (c: Z)
| AVar (v: string)
| APlus (a1 a2: Aff)
| AMinus (a1 a2: Aff)
| AMul (c: Z) (a: Aff).

(* Check if a variable is used in an affine function *)

Fixpoint used_in_aff (a: Aff) (v: string) :=
  match a with
  | AConst _ => true
  | AVar v' => (v == v')
  | APlus a1 a2 => used_in_aff a1 v || used_in_aff a2 v
  | AMinus a1 a2 => used_in_aff a1 v || used_in_aff a2 v
  | AMul c a' => used_in_aff a' v
  end.

(* Evaluate an affine function given values for each variable *)

Fixpoint eval_aff (a: Aff) (m: string -> Z) :=
  match a with
  | AConst c => c
  | AVar v => m v
  | APlus a1 a2 => (eval_aff a1 m) + (eval_aff a2 m)
  | AMinus a1 a2 => (eval_aff a1 m) - (eval_aff a2 m)
  | AMul c a => c * (eval_aff a m)
  end.

(* Implementation of a Presburger set / pw_aff library *)

Class PresburgerImpl (PMap PSet PwAff: Type) :=
  {
    eval_pset : PSet -> (string -> Z) -> bool;
    eval_pset_same : forall m1 m2,
        (forall x, m1 x = m2 x) -> forall s, eval_pset s m1 = eval_pset s m2;

    empty_set : PSet;
    empty_set_spec : forall x, ~~(eval_pset empty_set x);

    universe_set : PSet;
    universe_set_spec : forall x, eval_pset universe_set x;

    union_set : PSet -> PSet -> PSet;
    union_set_spec : forall p1 p2 x,
        eval_pset (union_set p1 p2) x = eval_pset p1 x || eval_pset p2 x;

    intersect_set : PSet -> PSet -> PSet;
    intersect_set_spec : forall p1 p2 x,
        eval_pset (intersect_set p1 p2) x = eval_pset p1 x && eval_pset p2 x;

    is_subset : PSet -> PSet -> bool;
    is_subset_spec : forall p1 p2, is_subset p1 p2 <->
                              forall x, eval_pset p1 x -> eval_pset p2 x;

    set_project_out : PSet -> string -> PSet;
    set_project_out_spec : forall p d (m: total_map), eval_pset (set_project_out p d) m <->
                                    exists v, eval_pset p (d !-> v; m);

    eval_pmap : PMap -> (string -> string -> Z) -> bool;
    eval_pmap_same : forall m1 m2,
        (forall x y, m1 x y = m2 x y) -> forall s, eval_pmap s m1 = eval_pmap s m2;

    empty_map : PMap;
    empty_map_spec : forall x, ~~(eval_pmap empty_map x);

    universe_map : PMap;
    universe_map_spec : forall x, eval_pmap universe_map x;

    union_map : PMap -> PMap -> PMap;
    union_map_spec : forall p1 p2 x,
        eval_pmap (union_map p1 p2) x = eval_pmap p1 x || eval_pmap p2 x;

    intersect_map : PMap -> PMap -> PMap;
    intersect_map_spec : forall p1 p2 x,
        eval_pmap (intersect_map p1 p2) x = eval_pmap p1 x && eval_pmap p2 x;

    is_subset_map : PMap -> PMap -> bool;
    is_subset_map_spec : forall p1 p2, is_subset_map p1 p2 <->
                                  forall x, eval_pmap p1 x -> eval_pmap p2 x;

    map_project_out : PMap -> string -> PMap;
    map_project_out_spec : forall p d (m: total_map), eval_pmap (map_project_out p d) m <->
                                                 exists v, eval_pmap p (d !-> v; m);

    eval_pw_aff : PwAff -> (string -> Z) -> option Z;

    pw_aff_from_aff : Aff -> PwAff;
    pw_aff_from_aff_spec : forall a x, eval_pw_aff (pw_aff_from_aff a) x = Some (eval_aff a x);

    intersect_domain : PwAff -> PSet -> PwAff;
    intersect_domain_spec : forall p s x, eval_pw_aff (intersect_domain p s) x =
                                     if eval_pset s x then
                                       eval_pw_aff p x
                                     else
                                       None;

    union_pw_aff : PwAff -> PwAff -> PwAff;
    union_pw_aff_spec : forall p1 p2 x, eval_pw_aff (union_pw_aff p1 p2) x =
                                   match eval_pw_aff p1 x with
                                   | None => eval_pw_aff p2 x
                                   | r => r
                                   end;

    eq_set : PwAff -> PwAff -> PSet;
    eq_set_spec : forall p1 p2 x, eval_pset (eq_set p1 p2) x =
                             match (eval_pw_aff p1 x, eval_pw_aff p2 x) with
                             | (Some v1, Some v2) => v1 == v2
                             | _ => false
                             end;

    ne_set : PwAff -> PwAff -> PSet;
    ne_set_spec : forall p1 p2 x, eval_pset (ne_set p1 p2) x =
                             match (eval_pw_aff p1 x, eval_pw_aff p2 x) with
                             | (Some v1, Some v2) => (v1 != v2)
                             | _ => false
                             end;

    le_set : PwAff -> PwAff -> PSet;
    le_set_spec : forall p1 p2 x, eval_pset (le_set p1 p2) x =
                             match (eval_pw_aff p1 x, eval_pw_aff p2 x) with
                             | (Some v1, Some v2) => v1 <=? v2
                             | _ => false
                             end;

    indicator_function : PSet -> PwAff;
    indicator_function_spec : forall s x, eval_pw_aff (indicator_function s) x =
                                     if eval_pset s x then
                                       Some 1
                                     else
                                       Some 0;
  }.

Generalizable All Variables.

Theorem empty_set_spec_rw `{PI: PresburgerImpl PMap PSet PwAff}:
  forall x, eval_pset empty_set x = false.
Proof.
  move => x.
  by rewrite (negbTE (empty_set_spec _)).
Qed.

Theorem empty_map_spec_rw `{PI: PresburgerImpl PMap PSet PwAff}:
  forall x, eval_pmap empty_map x = false.
Proof.
  move => x.
  by rewrite (negbTE (empty_map_spec _)).
Qed.

Theorem is_subset_refl `{PI: PresburgerImpl PMap PSet PwAff}:
  forall p, is_subset p p.
Proof.
  move => p.
    by apply is_subset_spec.
Qed.

Theorem is_subset_trans `{PI: PresburgerImpl PMap PSet PwAff}:
  forall p1 p2 p3, is_subset p1 p2 ->
              is_subset p2 p3 ->
              is_subset p1 p3.
Proof.
  move => p1 p2 p3.
  rewrite !is_subset_spec.
    by auto.
Qed.

Theorem is_subset_union_l `{PI: PresburgerImpl PMap PSet PwAff} :
  forall p1 p2, is_subset p1 (union_set p1 p2).
Proof.
  move => p1 p2.
  rewrite is_subset_spec => x Hp1.
    by rewrite union_set_spec Hp1.
Qed.

Theorem is_subset_union_r `{PI: PresburgerImpl PMap PSet PwAff} :
  forall p1 p2, is_subset p2 (union_set p1 p2).
Proof.
  move => p1 p2.
  rewrite is_subset_spec => x Hp2.
    by rewrite union_set_spec Hp2 orbT.
Qed.

Hint Rewrite @eval_pset_same @empty_set_spec_rw @universe_set_spec @union_set_spec @intersect_set_spec
     @eval_pmap_same @empty_map_spec_rw @universe_map_spec @union_map_spec @intersect_map_spec
     @pw_aff_from_aff_spec @intersect_domain_spec @union_pw_aff_spec @eq_set_spec @ne_set_spec @le_set_spec @indicator_function_spec : prw.

Hint Resolve @is_subset_spec @set_project_out_spec @is_subset_map_spec @map_project_out_spec.

Ltac simpl_presburger_ := repeat (autorewrite with prw; simplssr).
Ltac simpl_presburger := reflect_ne_in simpl_map_.

Ltac auto_presburger := intros ; simpl_map; autossr.

