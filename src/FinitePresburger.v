From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export TotalMap ssrZ ssrstring Tactic.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat eqtype.

Local Open Scope Z_scope.

(* An affine function that has an input of finite dimension *)

Inductive FiniteAff (dim: nat) :=
| FAConst (c: Z)
| FAVar (n: nat)
| FAPlus (a1 a2: FiniteAff dim)
| AMul (c: Z) (a: FiniteAff dim).

(* Evaluate an affine function *)

Fixpoint eval_finite_aff {dim: nat} (a: FiniteAff dim) (x: seq Z) :=
  match a with
  | FAConst c => c
  | FAVar n => nth 0 x n
  | FAPlus a1 a2 => (eval_finite_aff a1 x) + (eval_finite_aff a2 x)
  | AMul c a => c * (eval_finite_aff a x)
  end.

(* Equality between two points. Points are here represented by a list of
   values, where only the first n values matters. If the list size is
   smaller than n, it is filled with 0 *)

Definition point_equality (n: nat) : rel (seq Z) :=
  fun x1 x2 => all (fun i => nth 0 x1 i == nth 0 x2 i) (iota 0 n).

Theorem point_equality_sym (n: nat) :
  symmetric (point_equality n).
Proof.
  move => x1 x2. rewrite /point_equality. erewrite eq_in_all; eauto.
    by move => i Hi.
Qed.

Theorem point_equality_refl (n: nat) :
  reflexive (point_equality n).
Proof.
  move => x. rewrite /point_equality.
  rewrite ->eq_in_all with (a2 := xpredT). by apply /allP.
  move => i Hi. by rewrite eq_refl.
Qed.

(* Specification of a Presburger library with finite dimensions *)

Module Type FPresburgerImpl.
  Parameter PSet: nat -> Type.
  Parameter eqPSet : forall n, PSet n -> PSet n -> bool.
  Axiom eqPSetP : forall n, Equality.axiom (eqPSet n).
  Canonical PSet_eqMixin (n: nat) := EqMixin (eqPSetP n).
  Canonical PSet_eqType (n: nat) := Eval hnf in EqType (PSet n) (PSet_eqMixin n).

  Parameter PMap: nat -> nat -> Type.
  Parameter eqPMap : forall n m, PMap n m -> PMap n m -> bool.
  Axiom eqPMapP : forall n m, Equality.axiom (eqPMap n m).
  Canonical PMap_eqMixin (n m: nat) := EqMixin (eqPMapP n m).
  Canonical PMap_eqType (n m: nat) := Eval hnf in EqType (PMap n m) (PMap_eqMixin n m).

  Parameter PwAff: nat -> Type.
  Parameter eqPwAff : forall n, PwAff n -> PwAff n -> bool.
  Axiom eqPwAffP : forall n, Equality.axiom (eqPwAff n).
  Canonical PwAff_eqMixin (n: nat) := EqMixin (eqPwAffP n).
  Canonical PwAff_eqType (n: nat) := Eval hnf in EqType (PwAff n) (PwAff_eqMixin n).

  (* Check if a point is in a polyhedra *)
  Parameter f_eval_pset : forall n, PSet n -> seq Z -> bool.
  Arguments f_eval_pset {n}.

  Definition pset_eqclass (n: nat) := PSet n.
  Identity Coercion pset_of_eqclass : pset_eqclass >-> PSet.
  Coercion pred_of_pset (n: nat) (p : pset_eqclass n) : {pred (seq Z)} := f_eval_pset p.
  Canonical pset_predType (n: nat) := PredType (pred_of_pset n : PSet n -> pred (seq Z)).

  Axiom f_eval_pset_same : forall n (p: PSet n) x1 x2,
      point_equality n x1 x2 ->
      (x1 \in p) = (x2 \in p).

  Parameter f_empty_set: forall n, PSet n.
  Axiom f_empty_setP: forall n x, x \notin (f_empty_set n).

  Parameter f_universe_set: forall n, PSet n.
  Axiom f_universe_setP: forall n x, x \in (f_universe_set n).

  Parameter f_union_set: forall n, PSet n -> PSet n -> PSet n.
  Arguments f_union_set {n}.
  Axiom f_union_setP: forall n (p1 p2: PSet n) x,
      x \in (f_union_set p1 p2) = (x \in p1) || (x \in p2).

  Parameter f_intersect_set: forall n, PSet n -> PSet n -> PSet n.
  Arguments f_intersect_set {n}.
  Axiom f_intersect_setP: forall n (p1 p2: PSet n) x,
      x \in (f_intersect_set p1 p2) = (x \in p1) && (x \in p2).

  Parameter f_subtract_set: forall n, PSet n -> PSet n -> PSet n.
  Arguments f_subtract_set {n}.
  Axiom f_subtract_setP: forall n (p1 p2: PSet n) x,
      x \in (f_subtract_set p1 p2) = (x \in p1) && (x \notin p2).

  Definition f_complement_set {n: nat} :=
    f_subtract_set (f_universe_set n).

  Theorem f_complement_setP :
    forall n p x, (x \in (@f_complement_set n p)) = (x \notin p).
  Proof.
    move => n p x. by rewrite /f_complement_set f_subtract_setP f_universe_setP.
  Qed.

  Parameter f_is_subset_set: forall n, PSet n -> PSet n -> bool.
  Arguments f_is_subset_set {n}.
  Axiom f_is_subset_setP: forall n (p1 p2: PSet n),
      f_is_subset_set p1 p2 <->
      forall x, x \in p1 -> x \in p2.

  Parameter f_project_out_set: forall n, PSet n -> nat -> PSet n.
  Arguments f_project_out_set {n}.
  Axiom f_project_out_setP : forall n (p: PSet n) d x,
        x \in (f_project_out_set p d) <->
        exists v, (set_nth 0 x d v) \in p.

  Parameter f_involves_dim_set : forall n, PSet n -> nat -> bool.
  Arguments f_involves_dim_set {n}.
  Axiom f_involves_dim_setP :
    forall n (p: PSet n) d,
      ~~ (f_involves_dim_set p d) <->
      forall x v, (x \in p) = ((set_nth 0 x d v) \in p).

  Axiom f_eval_pset_same_involves :
    forall n (p: PSet n) x1 x2,
      (forall d, (d < n)%N -> f_involves_dim_set p d -> nth 0 x1 d = nth 0 x2 d) ->
      (x1 \in p) = (x2 \in p).

  Parameter f_eval_pmap : forall n m, PMap n m -> (seq Z * seq Z) -> bool.
  Arguments f_eval_pmap {n m}.

  Definition pmap_eqclass (n m: nat) := PMap n m.
  Identity Coercion pmap_of_eqclass : pmap_eqclass >-> PMap.
  Coercion pred_of_pmap (n m: nat) (p : pmap_eqclass n m) : {pred (seq Z * seq Z)} := f_eval_pmap p.
  Canonical pmap_predType (n m: nat) := PredType (pred_of_pmap n m : PMap n m -> pred (seq Z * seq Z)).

  Axiom f_eval_pmap_same_in : forall n m (pm: PMap n m) x_in1 x_in2 x_out,
      point_equality n x_in1 x_in2 ->
      ((x_in1, x_out) \in pm) = ((x_in2, x_out) \in pm).
  Axiom f_eval_pmap_same_out : forall n m (pm: PMap n m) x_in x_out1 x_out2,
      point_equality m x_out1 x_out2 ->
      ((x_in, x_out1) \in pm) = ((x_in, x_out2) \in pm).

  Parameter f_empty_map: forall n m, PMap n m.
  Axiom f_empty_mapP: forall n m x y, (x,y) \notin (f_empty_map n m).

  Parameter f_universe_map: forall n m, PMap n m.
  Axiom f_universe_mapP: forall n m x y, (x, y) \in (f_universe_map n m).

  Parameter f_get_domain_map: forall n m, PMap n m -> PSet n.
  Arguments f_get_domain_map {n} {m}.
  Axiom f_get_domain_mapP: forall n m (map: PMap n m) x_in,
      x_in \in (f_get_domain_map map) <-> exists x_out, (x_in, x_out) \in map.

  Parameter f_id_map: forall n, PMap n n.
  Axiom f_id_mapP: forall n x1 x2,
      (x1, x2) \in (f_id_map n) = point_equality n x1 x2.

  Parameter f_union_map: forall n m, PMap n m -> PMap n m -> PMap n m.
  Arguments f_union_map {n m}.
  Axiom f_union_mapP: forall n m (p1 p2: PMap n m) x y,
      (x, y) \in (f_union_map p1 p2) = ((x, y) \in p1) || ((x, y) \in p2).

  Parameter f_intersect_map: forall n m, PMap n m -> PMap n m -> PMap n m.
  Arguments f_intersect_map {n m}.
  Axiom f_intersect_mapP: forall n m (p1 p2: PMap n m) x y,
      (x, y) \in (f_intersect_map p1 p2) = ((x, y) \in p1) && ((x, y) \in p2).

  Parameter f_subtract_map: forall n m, PMap n m -> PMap n m -> PMap n m.
  Arguments f_subtract_map {n m}.
  Axiom f_subtract_mapP: forall n m (p1 p2: PMap n m) x,
      x \in (f_subtract_map p1 p2) = (x \in p1) && (x \notin p2).

  Parameter f_intersect_domain_map: forall n m, PMap n m -> PSet n -> PMap n m.
  Arguments f_intersect_domain_map {n} {m}.
  Axiom f_intersect_domain_mapP: forall n m (map: PMap n m) pset x_in x_out,
      (x_in, x_out) \in (f_intersect_domain_map map pset) =
      ((x_in, x_out) \in map) && (x_in \in pset).

  Parameter f_intersect_range_map: forall n m, PMap n m -> PSet m -> PMap n m.
  Arguments f_intersect_range_map {n} {m}.
  Axiom f_intersect_range_mapP: forall n m (map: PMap n m) pset x_in x_out,
      (x_in, x_out) \in (f_intersect_range_map map pset) =
      ((x_in, x_out) \in map) && (x_out \in pset).

  Parameter f_is_subset_map: forall n m, PMap n m -> PMap n m -> bool.
  Arguments f_is_subset_map {n m}.
  Axiom f_is_subset_mapP: forall n m (p1 p2: PMap n m),
      f_is_subset_map p1 p2 <->
      forall x y, (x, y) \in p1 -> (x, y) \in p2.

  Parameter f_project_out_map_in: forall n m, PMap n m -> nat -> PMap n m.
  Arguments f_project_out_map_in {n m}.
  Axiom f_project_out_mapp_inP: forall n m (p: PMap n m) d x y,
      (x, y) \in (f_project_out_map_in p d) <->
      exists v, (set_nth 0 x d v, y) \in p.

  Parameter f_project_out_map_out: forall n m, PMap n m -> nat -> PMap n m.
  Arguments f_project_out_map_out {n m}.
  Axiom f_project_out_mapp_outP: forall n m (p: PMap n m) d x y,
      (x, y) \in (f_project_out_map_out p d) <->
      exists v, (x, set_nth 0 y d v) \in p.

  Parameter f_apply_range_map : forall n m p, PMap n m -> PMap m p -> PMap n p.
  Arguments f_apply_range_map {n m p}.
  Axiom f_apply_range_mapP : forall n1 n2 n3 (m1: PMap n1 n2) (m2: PMap n2 n3) x1 x3,
      (x1, x3) \in (f_apply_range_map m1 m2) <->
      exists x2, ((x1, x2) \in m1) && ((x2, x3) \in m2).

  Parameter f_transitive_closure_map : forall n, PMap n n -> PMap n n.
  Arguments f_transitive_closure_map {n}.
  Axiom f_transitive_closure_map_ge_step : forall n (m: PMap n n), f_is_subset_map m (f_transitive_closure_map m).
  Axiom f_transitive_closure_map_ge_id : forall n (m: PMap n n),
      f_is_subset_map (f_id_map n) (f_transitive_closure_map m).
  Axiom f_transitive_closure_map_ge_compose : forall n (m: PMap n n),
      f_is_subset_map (f_apply_range_map (f_transitive_closure_map m) m)
                      (f_transitive_closure_map m).

  Parameter f_is_single_valued_map : forall n m, PMap n m -> bool.
  Arguments f_is_single_valued_map {n} {m}.
  Axiom f_is_single_valued_mapP :
    forall n m (pm: PMap n m),
      f_is_single_valued_map pm <->
      (forall x v1 v2, (x, v1) \in pm -> (x, v2) \in pm -> point_equality m v1 v2).

  Parameter f_eval_pw_aff : forall n, PwAff n -> seq Z -> option Z.
  Arguments f_eval_pw_aff {n}.

  Axiom f_eval_pw_aff_same : forall n (p: PwAff n) x1 x2,
      point_equality n x1 x2 ->
      f_eval_pw_aff p x1 = f_eval_pw_aff p x2.

  Parameter f_pw_aff_from_aff : forall n, FiniteAff n -> PwAff n.
  Arguments f_pw_aff_from_aff {n}.
  Axiom f_pw_aff_from_affP : forall n (a: FiniteAff n) x,
      f_eval_pw_aff (f_pw_aff_from_aff a) x = Some (eval_finite_aff a x).

  Parameter f_empty_pw_aff : forall n, PwAff n.
  Axiom f_empty_pw_affP :
    forall n x, f_eval_pw_aff (f_empty_pw_aff n) x = None.

  Parameter f_get_domain_pw_aff : forall n, PwAff n -> PSet n.
  Arguments f_get_domain_pw_aff {n}.
  Axiom f_get_domain_pw_affP : forall n (p: PwAff n) x,
      x \in (f_get_domain_pw_aff p) = match f_eval_pw_aff p x with
                                       | Some v => true
                                       | None => false
                                       end.

  Parameter f_intersect_domain : forall n, PwAff n -> PSet n -> PwAff n.
  Arguments f_intersect_domain {n}.
  Axiom f_intersect_domainP : forall n (p: PwAff n) (s: PSet n) x,
      f_eval_pw_aff (f_intersect_domain p s) x =
      if x \in s then
        f_eval_pw_aff p x
      else
        None.

  Parameter f_union_pw_aff : forall n, PwAff n -> PwAff n -> PwAff n.
  Arguments f_union_pw_aff {n}.
  Axiom f_union_pw_affP : forall n (p1 p2: PwAff n) x,
      f_eval_pw_aff (f_union_pw_aff p1 p2) x =
      if f_eval_pw_aff p1 x is Some r then
        Some r
      else
        f_eval_pw_aff p2 x.

  Parameter f_add_pw_aff : forall n, PwAff n -> PwAff n -> PwAff n.
  Arguments f_add_pw_aff {n}.
  Axiom f_add_pw_affP :
    forall n (p1 p2: PwAff n) x,
      f_eval_pw_aff (f_add_pw_aff p1 p2) x =
      match (f_eval_pw_aff p1 x, f_eval_pw_aff p2 x) with
      | (Some v1, Some v2) => Some (v1 + v2)
      | _ => None
      end.

  Parameter f_eq_set : forall n, PwAff n -> PwAff n -> PSet n.
  Arguments f_eq_set {n}.
  Axiom f_eq_setP :
    forall n (p1 p2: PwAff n) x,
      x \in (f_eq_set p1 p2) =
      match (f_eval_pw_aff p1 x, f_eval_pw_aff p2 x) with
      | (Some v1, Some v2) => v1 == v2
      | _ => false
      end.

  Parameter f_ne_set : forall n, PwAff n -> PwAff n -> PSet n.
  Arguments f_ne_set {n}.
  Axiom f_ne_setP :
    forall n (p1 p2: PwAff n) x,
      x \in (f_ne_set p1 p2) =
      match (f_eval_pw_aff p1 x, f_eval_pw_aff p2 x) with
      | (Some v1, Some v2) => v1 != v2
      | _ => false
      end.

  Parameter f_le_set : forall n, PwAff n -> PwAff n -> PSet n.
  Arguments f_le_set {n}.
  Axiom f_le_setP :
    forall n (p1 p2: PwAff n) x,
      x \in (f_le_set p1 p2) =
      match (f_eval_pw_aff p1 x, f_eval_pw_aff p2 x) with
      | (Some v1, Some v2) => v1 <=? v2
      | _ => false
      end.

  Parameter f_indicator_function : forall n, PSet n -> PwAff n.
  Arguments f_indicator_function {n}.
  Axiom f_indicator_functionP :
    forall n (p: PSet n) x,
      f_eval_pw_aff (f_indicator_function p) x =
      if x \in p then
        Some 1
      else
        Some 0.

  Parameter f_involves_dim_pw_aff : forall n, PwAff n -> nat -> bool.
  Arguments f_involves_dim_pw_aff {n}.
  Axiom f_involves_dim_pw_affP :
    forall n (p: PwAff n) d,
      ~~(f_involves_dim_pw_aff p d) <->
      forall x v, f_eval_pw_aff p x = f_eval_pw_aff p (set_nth 0 x d v).

  Axiom f_eval_pw_aff_same_involves :
    forall n (p: PwAff n) x1 x2,
      (forall d, (d < n)%N -> f_involves_dim_pw_aff p d -> nth 0 x1 d = nth 0 x2 d) ->
      (f_eval_pw_aff p x1) = (f_eval_pw_aff p x2).

  Parameter f_get_involved_dim : forall n, PwAff n -> seq nat.
  Arguments f_get_involved_dim {n}.
  Axiom f_get_involved_dimP :
    forall n (p: PwAff n) d, d \in (f_get_involved_dim p) = f_involves_dim_pw_aff p d.

  Parameter f_map_from_pw_aff : forall n, PwAff n -> PMap n 1.
  Arguments f_map_from_pw_aff {n}.
  Axiom f_map_from_pw_affP :
    forall n (p: PwAff n) x_in x_out,
      ((x_in, x_out) \in (f_map_from_pw_aff p)) =
      (f_eval_pw_aff p x_in == Some (nth 0 x_out 0)).

  Parameter f_map_lexmin : forall n, PMap n 1 -> PwAff n.
  Arguments f_map_lexmin {n}.
  Axiom f_map_lexminP :
    forall n m x_in x_out,
      @f_eval_pw_aff n (f_map_lexmin m) x_in = Some x_out <->
      (forall x_out', ((x_in, [::x_out']) \in m) -> x_out' >= x_out).

  Parameter f_apply_map_to_pw_aff : forall n m (map: PMap n m), f_is_single_valued_map map -> PwAff m -> PwAff n.
  Arguments f_apply_map_to_pw_aff {n m}.
  Axiom f_apply_map_to_pw_affP :
    forall n m map pw_aff H x_in v,
      f_eval_pw_aff (@f_apply_map_to_pw_aff n m map H pw_aff) x_in = v
      <-> (v = None /\ forall x_out, (x_in, x_out) \notin map) \/
        (exists x_mid, (x_in, x_mid) \in map /\ f_eval_pw_aff pw_aff x_mid = v).

  Parameter f_concat_map : forall n (s: seq (PMap n 1)), PMap n (size s).
  Arguments f_concat_map {n}.
  Axiom f_concat_mapP :
    forall n (s: seq (PMap n 1)) x_in x_out,
      (x_in, x_out) \in f_concat_map s
      <-> (forall i, (i < n)%N -> (x_in, [::(nth 0 x_out i)]) \in nth (f_empty_map n 1) s i).

  Parameter f_pw_aff_from_map : forall n m (pm: PMap n m), f_is_single_valued_map pm -> seq (PwAff n).
  Arguments f_pw_aff_from_map {n} {m}.
  Axiom f_pw_aff_from_map_size :
    forall n m (pm: PMap n m) H,
      size (f_pw_aff_from_map pm H) = m.
  Axiom f_pw_aff_from_mapP :
    forall n m (pm: PMap n m) H,
    forall x_in val,
    forall i, (i < m)%nat ->
    (exists x_out, nth 0%Z x_out i = val /\ (x_in, x_out) \in pm) <->
    (let pw_aff_i := nth (f_empty_pw_aff n) (f_pw_aff_from_map pm H) i in
     f_eval_pw_aff pw_aff_i x_in = Some val).

  Ltac rewrite_point_aux x1 x2 n H :=
    rewrite
      ?(f_eval_pset_same _ _ x1 x2 H)
      ?(f_eval_pw_aff_same _ _ x1 x2 H)
      ?(f_eval_pmap_same_in _ _ _ x1 x2 _ H)
      ?(f_eval_pmap_same_out _ _ _ _ x1 x2 H);
    repeat (match goal with
            | [ H1: is_true (?i \in iota 0%N n) |- context[nth 0%Z x1 ?i] ] =>
              move: (H) => /allP /(_ i H1) /eqP ->
            | [ H1: is_true (?i < _) |- context[nth 0%Z x1 ?i]] =>
              (have: (i \in iota 0%N n) by simplssr); let Hiota := fresh "Hiota" in intro Hiota
            end).

  Ltac intro_point_equality x_out1 x_out2 :=
    match goal with
    | [ H1: is_true ((?x_in, x_out1) \in ?map),
        H2: is_true ((?x_in, x_out2) \in ?map),
        H: is_true (f_is_single_valued_map ?map) |- _ ] =>
      move: (H);
      move => /f_is_single_valued_mapP /(_ x_in x_out1 x_out2 H1 H2)
    end.

  Ltac rewrite_point_tac x1 x2 tac :=
    match goal with
    | [ H: is_true (point_equality ?n x1 x2) |- _ ] => tac x1 x2 n H
    | _ => intro_point_equality x1 x2; let H := fresh "H" in intro H; rewrite_point_tac x1 x2 tac
    end.

  Ltac rewrite_point x1 x2 := rewrite_point_tac x1 x2 rewrite_point_aux.

  Ltac rewrite_point_H_tac H tac :=
    match type of H with
    | is_true (point_equality ?n ?x1 ?x2) => tac x1 x2 n H
    end.

  Ltac rewrite_point_H H := rewrite_point_H_tac H rewrite_point_aux.

  Ltac rewrite_point_in Hyp x1 x2 := move: Hyp; rewrite_point x1 x2 => Hyp.

  Theorem f_apply_range_preserves_single_valued :
    forall n m p (pm1: PMap n m) (H1: f_is_single_valued_map pm1) (pm2: PMap m p) (H2: f_is_single_valued_map pm2),
      f_is_single_valued_map (f_apply_range_map pm1 pm2).
  Proof.
    intros. rewrite f_is_single_valued_mapP => x x_out1 x_out2.
    rewrite !f_apply_range_mapP => [[x_mid1 /andP[H11 H21]]] [x_mid2 /andP[H12 H22]].
    rewrite_point_in H21 x_mid1 x_mid2.
    by intro_point_equality x_out1 x_out2.
  Qed.

  Theorem f_pw_aff_from_map_noneP :
    forall n m (pm: PMap n m) (H: f_is_single_valued_map pm),
    forall x_in i, (i < m)%N ->
    let pw_aff_i := nth (f_empty_pw_aff n) (f_pw_aff_from_map pm H) i in
    f_eval_pw_aff pw_aff_i x_in = None <->
    (~ exists x_out, (x_in, x_out) \in pm).
  Proof.
    move => n m pm Hsingle x_in i Hi.
    split.
    - move => HNone [x_out Hin].
      move: (f_pw_aff_from_mapP n m pm Hsingle x_in (nth 0 x_out i) i Hi) => [H _].
      have Hx_out: (exists x_out0, nth 0 x_out0 i = nth 0 x_out i /\ (x_in, x_out0) \in pm). by exists x_out.
      apply H in Hx_out. rewrite HNone in Hx_out. by [].
    - move => Hnotin.
      case Heval: (f_eval_pw_aff _ _) => [val| //]. exfalso.
      move: (f_pw_aff_from_mapP n m pm Hsingle x_in val i Hi) => [_ H].
      apply H in Heval. case: Heval => x_out [_ Hin]. apply Hnotin.
        by eauto.
  Qed.

  Theorem f_map_from_pw_aff_single_valued :
    forall n (map: PwAff n), f_is_single_valued_map (f_map_from_pw_aff map).
  Proof.
    move => n map.
    rewrite f_is_single_valued_mapP => x_in x_out1 x_out2 Hin1 Hin2.
    rewrite f_map_from_pw_affP in Hin1. move => /eqP in Hin1.
    rewrite f_map_from_pw_affP in Hin2. move => /eqP in Hin2.
    rewrite /point_equality. simplssr.
    rewrite Hin1 in Hin2. by case: Hin2 => ->.
  Qed.

  Theorem f_empty_set_rw :
    forall n x, x \in (f_empty_set n) = false.
  Proof.
    move => n x.
      by rewrite (negbTE (f_empty_setP _ _)).
  Qed.

  Theorem f_is_subset_set_refl :
    forall n (s: PSet n), f_is_subset_set s s.
  Proof.
    move => n s.
      by rewrite f_is_subset_setP.
  Qed.

  Theorem f_is_subset_set_trans :
    forall n (s1 s2 s3: PSet n),
      f_is_subset_set s1 s2 ->
      f_is_subset_set s2 s3 ->
      f_is_subset_set s1 s3.
  Proof.
    move => n s1 s2 s3 /f_is_subset_setP H12 /f_is_subset_setP H23.
    apply f_is_subset_setP => x.
    move => /(_ x) in H12. move => /(_ x) in H23.
      by auto.
  Qed.

  Theorem f_is_subset_intersect_right :
    forall n (s1 s2: PSet n), f_is_subset_set (f_intersect_set s1 s2) s1.
  Proof.
    move => n s1 s2. rewrite f_is_subset_setP => x.
    rewrite f_intersect_setP.
      by autossr.
  Qed.

  Theorem f_is_subset_intersect_left :
    forall n (s1 s2: PSet n), f_is_subset_set (f_intersect_set s1 s2) s2.
  Proof.
    move => n s1 s2. rewrite f_is_subset_setP => x.
    rewrite f_intersect_setP.
      by autossr.
  Qed.

  Definition f_cast_map {n1 n2 m1 m2: nat} (Hn: n1 = n2) (Hm: m1 = m2) (p: PMap n1 m1) : PMap n2 m2.
      by rewrite -Hn -Hm.
  Defined.

  Theorem f_cast_mapP :
    forall n1 n2 m1 m2 Hn Hm p x,
      (x \in (@f_cast_map n1 n2 m1 m2 Hn Hm p)) = (x \in p).
  Proof.
    move => n1 n2 m1 m2 Hn Hm p x.
    rewrite /f_cast_map /eq_rect_r /eq_rect.
    case Hn. case Hm.
      by [].
  Qed.

  Global Opaque f_cast_map.

  Hint Rewrite @f_empty_set_rw @f_is_subset_set_refl @f_universe_setP @f_union_setP @f_intersect_setP
       @f_map_from_pw_affP @f_intersect_domain_mapP
       @f_intersect_range_mapP @f_get_domain_mapP @f_get_domain_pw_affP
       @f_subtract_setP @f_complement_setP @f_apply_range_mapP
       @f_universe_mapP @f_id_mapP @f_union_mapP @f_intersect_mapP
       @f_pw_aff_from_affP @f_intersect_domainP @f_union_pw_affP @f_eq_setP @f_ne_setP @f_le_setP @f_indicator_functionP
       @f_add_pw_affP @f_empty_pw_affP @f_cast_mapP
       using by first [liassr | autossr ] : prw.

  Hint Resolve @f_is_subset_setP @f_is_subset_mapP @f_project_out_setP @f_is_subset_mapP
    @f_is_subset_intersect_right @f_is_subset_intersect_left: core.

  Ltac simpl_finite_presburger_ := repeat (autorewrite with prw; simpl_map).
  Ltac simpl_finite_presburger := reflect_ne_in simpl_finite_presburger_.

  Ltac auto_finite_presburger := intros ; simpl_finite_presburger; autossr.

End FPresburgerImpl.
