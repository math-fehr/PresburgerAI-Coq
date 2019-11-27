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

Class PresburgerImpl (PMap PSet PwAff: eqType) :=
  {
    eval_pset : PSet -> @total_map string_eqType Z -> bool;

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

    eval_pmap : PMap -> @total_map string_eqType Z -> @total_map string_eqType Z -> bool;

    empty_map : PMap;
    empty_map_spec : forall x y, ~~(eval_pmap empty_map x y);

    universe_map : PMap;
    universe_map_spec : forall x y, eval_pmap universe_map x y;

    id_map : PMap;
    id_map_spec : forall x y, eval_pmap id_map x y = (x == y);

    union_map : PMap -> PMap -> PMap;
    union_map_spec : forall p1 p2 x y,
        eval_pmap (union_map p1 p2) x y = eval_pmap p1 x y || eval_pmap p2 x y;

    intersect_map : PMap -> PMap -> PMap;
    intersect_map_spec : forall p1 p2 x y,
        eval_pmap (intersect_map p1 p2) x y = eval_pmap p1 x y && eval_pmap p2 x y;

    is_subset_map : PMap -> PMap -> bool;
    is_subset_map_spec : forall p1 p2, is_subset_map p1 p2 <->
                                  forall x y, eval_pmap p1 x y -> eval_pmap p2 x y;

    map_project_out_in : PMap -> string -> PMap;
    map_project_out_in_spec : forall p d (m_in: total_map) m_out, eval_pmap (map_project_out_in p d) m_in m_out <->
                                                             exists v, eval_pmap p (d !-> v; m_in) m_out;

    map_project_out_out : PMap -> string -> PMap;
    map_project_out_out_spec : forall p d m_in (m_out: total_map), eval_pmap (map_project_out_out p d) m_in m_out <->
                                                              exists v, eval_pmap p m_in (d !-> v; m_out);

    map_apply_range : PMap -> PMap -> PMap;
    map_apply_range_spec : forall a1 a2 m_in m_out, eval_pmap (map_apply_range a1 a2) m_in m_out <-> exists m_mid, eval_pmap a1 m_in m_mid /\ eval_pmap a2 m_mid m_out;

    map_apply_range_bot : forall a, map_apply_range a empty_map = empty_map;

    transitive_closure_map : PMap -> PMap;
    transitive_closure_map_ge_step : forall a, is_subset_map a (transitive_closure_map a);
    transitive_closure_map_ge_id : forall a, is_subset_map id_map (transitive_closure_map a);
    transitive_closure_map_eq_compose : forall a, is_subset_map (map_apply_range (transitive_closure_map a) a) (transitive_closure_map a);

    eval_pw_aff : PwAff -> @total_map string_eqType Z -> option Z;

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

Section PresburgerTheorems.

  Context {PMap PSet PwAff: eqType}
          {PI: PresburgerImpl PMap PSet PwAff}.

  Theorem empty_set_spec_rw :
    forall x, eval_pset empty_set x = false.
  Proof.
    move => x.
      by rewrite (negbTE (empty_set_spec _)).
  Qed.

  Theorem empty_map_spec_rw :
    forall x y, eval_pmap empty_map x y = false.
  Proof.
    move => x y.
      by rewrite (negbTE (empty_map_spec _ _)).
  Qed.

  Theorem is_subset_refl :
    forall p, is_subset p p.
  Proof.
    move => p.
      by apply is_subset_spec.
  Qed.

  Theorem is_subset_map_refl :
    forall p, is_subset_map p p.
  Proof.
    move => p.
      by apply is_subset_map_spec.
  Qed.

  Theorem is_subset_trans :
    forall p1 p2 p3, is_subset p1 p2 ->
                is_subset p2 p3 ->
                is_subset p1 p3.
  Proof.
    move => p1 p2 p3.
    rewrite !is_subset_spec.
      by auto.
  Qed.

  Theorem is_subset_map_trans :
    forall p1 p2 p3, is_subset_map p1 p2 ->
                is_subset_map p2 p3 ->
                is_subset_map p1 p3.
  Proof.
    move => p1 p2 p3.
    rewrite !is_subset_map_spec.
    by auto.
  Qed.

  Theorem is_subset_union_l :
    forall p1 p2, is_subset p1 (union_set p1 p2).
  Proof.
    move => p1 p2.
    rewrite is_subset_spec => x Hp1.
      by rewrite union_set_spec Hp1.
  Qed.

  Theorem is_subset_union_r :
    forall p1 p2, is_subset p2 (union_set p1 p2).
  Proof.
    move => p1 p2.
    rewrite is_subset_spec => x Hp2.
      by rewrite union_set_spec Hp2 orbT.
  Qed.

End PresburgerTheorems.

Hint Rewrite @empty_set_spec_rw @universe_set_spec @union_set_spec @intersect_set_spec
     @empty_map_spec_rw @universe_map_spec @id_map_spec @union_map_spec @intersect_map_spec
     @pw_aff_from_aff_spec @intersect_domain_spec @union_pw_aff_spec @eq_set_spec @ne_set_spec @le_set_spec @indicator_function_spec
  using by first [liassr | autossr ] : prw.

Hint Resolve @is_subset_spec @is_subset_map_spec @set_project_out_spec @is_subset_map_spec @map_project_out_in_spec @map_project_out_out_spec.

Ltac simpl_presburger_ := repeat (autorewrite with prw; simplssr).
Ltac simpl_presburger := reflect_ne_in simpl_presburger_.

Ltac auto_presburger := intros ; simpl_presburger; autossr.
