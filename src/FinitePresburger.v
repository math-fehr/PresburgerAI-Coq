From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export TotalMap ssrZ ssrstring Tactic.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat.

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

Definition point_equality (n: nat) (x1 x2: seq Z) :=
  forall m, (m < n)%nat -> nth 0 x1 m = nth 0 x2 m.

(* Specification of a Presburger library with finite dimensions *)

Module Type FPresburgerImpl.
  Parameter PSet: nat -> eqType.
  Parameter PMap: nat -> nat -> eqType.
  Parameter PwAff: nat -> eqType.

  (* Check if a point is in a polyhedra *)
  Parameter f_eval_pset : forall n, PSet n -> seq Z -> bool.
  Arguments f_eval_pset {n}.
  Notation "P \ins S" := (f_eval_pset S P) (at level 70, no associativity).

  Parameter f_empty_set: forall n, PSet n.
  Axiom f_empty_setP: forall n x, ~~(x \ins (f_empty_set n)).

  Parameter f_universe_set: forall n, PSet n.
  Axiom f_universe_setP: forall n x, x \ins (f_universe_set n).

  Parameter f_union_set: forall n, PSet n -> PSet n -> PSet n.
  Arguments f_union_set {n}.
  Axiom f_union_setP: forall n (p1 p2: PSet n) x,
      x \ins (f_union_set p1 p2) = (x \ins p1) || (x \ins p2).

  Parameter f_intersect_set: forall n, PSet n -> PSet n -> PSet n.
  Arguments f_intersect_set {n}.
  Axiom f_intersect_setP: forall n (p1 p2: PSet n) x,
      x \ins (f_intersect_set p1 p2) = (x \ins p1) && (x \ins p2).

  Parameter f_subtract_set: forall n, PSet n -> PSet n -> PSet n.
  Arguments f_subtract_set {n}.
  Axiom f_subtract_setP: forall n (p1 p2: PSet n) x,
      x \ins (f_subtract_set p1 p2) = (x \ins p1) && ~~ (x \ins p2).

  Parameter f_is_subset_set: forall n, PSet n -> PSet n -> bool.
  Arguments f_is_subset_set {n}.
  Axiom f_is_subset_setP: forall n (p1 p2: PSet n),
      f_is_subset_set p1 p2 <->
      forall x, x \ins p1 -> x \ins p2.

  Parameter f_project_out_set: forall n, PSet n -> nat -> PSet n.
  Arguments f_project_out_set {n}.
  Axiom f_project_out_setP : forall n (p: PSet n) d x,
        x \ins (f_project_out_set p d) <->
        exists v, (set_nth 0 x d v) \ins p.

  Parameter f_eval_pmap : forall n m, PMap n m -> seq Z -> seq Z -> bool.
  Arguments f_eval_pmap {n m}.
  Notation "P \inm S" := (f_eval_pmap S P.1 P.2) (at level 70, no associativity).

  Parameter f_empty_map: forall n m, PMap n m.
  Axiom f_empty_mapP: forall n m x y, ~~((x,y) \inm (f_empty_map n m)).

  Parameter f_universe_map: forall n m, PMap n m.
  Axiom f_universe_mapP: forall n m x y, (x, y) \inm (f_empty_map n m).

  Parameter f_id_map: forall n, PMap n n.
  Axiom f_id_mapP: forall n x1 x2,
      (x1, x2) \inm (f_id_map n) <-> point_equality n x1 x2.

  Parameter f_union_map: forall n m, PMap n m -> PMap n m -> PMap n m.
  Arguments f_union_map {n m}.
  Axiom f_union_mapP: forall n m (p1 p2: PMap n m) x y,
      (x, y) \inm (f_union_map p1 p2) = ((x, y) \inm p1) || ((x, y) \inm p2).

  Parameter f_intersect_map: forall n m, PMap n m -> PMap n m -> PMap n m.
  Arguments f_intersect_map {n m}.
  Axiom f_intersect_mapP: forall n m (p1 p2: PMap n m) x y,
      (x, y) \inm (f_intersect_map p1 p2) = ((x, y) \inm p1) && ((x, y) \inm p2).

  Parameter f_is_subset_map: forall n m, PMap n m -> PMap n m -> bool.
  Arguments f_is_subset_map {n m}.
  Axiom f_is_subset_mapP: forall n m (p1 p2: PMap n m),
      f_is_subset_map p1 p2 <->
      forall x y, (x, y) \inm p1 -> (x, y) \inm p2.

  Parameter f_project_out_map_in: forall n m, PMap n m -> nat -> PMap n m.
  Arguments f_project_out_map_in {n m}.
  Axiom f_project_out_mapp_inP: forall n m (p: PMap n m) d x y,
      (x, y) \inm (f_project_out_map_in p d) <->
      exists v, (set_nth 0 x d v, y) \inm p.

  Parameter f_project_out_map_out: forall n m, PMap n m -> nat -> PMap n m.
  Arguments f_project_out_map_out {n m}.
  Axiom f_project_out_mapp_outP: forall n m (p: PMap n m) d x y,
      (x, y) \inm (f_project_out_map_out p d) <->
      exists v, (x, set_nth 0 y d v) \inm p.

  Parameter f_apply_range_map : forall n m p, PMap n m -> PMap m p -> PMap n p.
  Arguments f_apply_range_map {n m p}.
  Axiom f_apply_range_mapP : forall n1 n2 n3 (m1: PMap n1 n2) (m2: PMap n2 n3) x1 x3,
      (x1, x3) \inm (f_apply_range_map m1 m2) <->
      exists x2, ((x1, x2) \inm m1) && ((x1, x3) \inm m2).

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
      (forall x v1 v2, (x, v1) \inm pm -> (x, v2) \inm pm -> point_equality m v1 v2).

  Parameter f_eval_pw_aff : forall n, PwAff n -> seq Z -> option Z.
  Arguments f_eval_pw_aff {n}.

  Parameter f_pw_aff_from_aff : forall n, FiniteAff n -> PwAff n.
  Arguments f_pw_aff_from_aff {n}.
  Axiom f_pw_aff_from_affP : forall n (a: FiniteAff n) x,
      f_eval_pw_aff (f_pw_aff_from_aff a) x = Some (eval_finite_aff a x).

  Parameter f_empty_pw_aff : forall n, PwAff n.
  Axiom f_empty_pw_affP :
    forall n x, f_eval_pw_aff (f_empty_pw_aff n) x = None.

  Parameter f_intersect_domain : forall n, PwAff n -> PSet n -> PwAff n.
  Arguments f_intersect_domain {n}.
  Axiom f_intersect_domainP : forall n (p: PwAff n) (s: PSet n) x,
      f_eval_pw_aff (f_intersect_domain p s) x =
      if f_eval_pset s x then
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
      f_eval_pset (f_eq_set p1 p2) x =
      match (f_eval_pw_aff p1 x, f_eval_pw_aff p2 x) with
      | (Some v1, Some v2) => v1 == v2
      | _ => false
      end.

  Parameter f_ne_set : forall n, PwAff n -> PwAff n -> PSet n.
  Arguments f_ne_set {n}.
  Axiom f_ne_setP :
    forall n (p1 p2: PwAff n) x,
      f_eval_pset (f_ne_set p1 p2) x =
      match (f_eval_pw_aff p1 x, f_eval_pw_aff p2 x) with
      | (Some v1, Some v2) => v1 != v2
      | _ => false
      end.

  Parameter f_le_set : forall n, PwAff n -> PwAff n -> PSet n.
  Arguments f_le_set {n}.
  Axiom f_le_setP :
    forall n (p1 p2: PwAff n) x,
      f_eval_pset (f_le_set p1 p2) x =
      match (f_eval_pw_aff p1 x, f_eval_pw_aff p2 x) with
      | (Some v1, Some v2) => v1 <=? v2
      | _ => false
      end.

  Parameter f_indicator_function : forall n, PSet n -> PwAff n.
  Arguments f_indicator_function {n}.
  Axiom f_indicator_functionP :
    forall n (p: PSet n) x,
      f_eval_pw_aff (f_indicator_function p) x =
      if f_eval_pset p x then
        Some 1
      else
        Some 0.

  Parameter f_involves_dim_pw_aff : forall n, PwAff n -> nat -> bool.
  Arguments f_involves_dim_pw_aff {n}.
  Axiom f_involves_dim_pw_affP :
    forall n (p: PwAff n) d,
      f_involves_dim_pw_aff p d <->
      forall x v, f_eval_pw_aff p x != f_eval_pw_aff p (set_nth 0 x d v).

  Parameter f_get_involved_dim : forall n, PwAff n -> seq nat.
  Arguments f_get_involved_dim {n}.
  Axiom f_get_involved_dimP :
    forall n (p: PwAff n) d, d \in (f_get_involved_dim p) = f_involves_dim_pw_aff p d.

  Parameter f_map_from_pw_aff : forall n, PwAff n -> PMap n 1.
  Arguments f_map_from_pw_aff {n}.
  Axiom f_map_from_pw_affP :
    forall n (p: PwAff n) x,
      let pmap := f_map_from_pw_aff p in
      match f_eval_pw_aff p x with
      | Some v => (x, [::v]) \inm pmap /\ forall v', (x, v') \inm pmap -> v = nth 0%Z v' 0
      | None => ~ exists v, (x, [::v]) \inm pmap
      end.

  Parameter f_concat_map : forall n (s: seq (PMap n 1)), PMap n (size s).
  Arguments f_concat_map {n}.
  Axiom f_concat_mapP :
    forall n (s: seq (PMap n 1)) x_in x_out,
      (x_in, x_out) \inm f_concat_map s
      <-> (forall i, (i < n)%N -> (x_in, [::(nth 0 x_out i)]) \inm nth (f_empty_map n 1) s i).

  Parameter f_pw_aff_from_map : forall n m (pm: PMap n m), f_is_single_valued_map pm -> seq (PwAff n).
  Arguments f_pw_aff_from_map {n} {m}.
  Axiom f_pw_aff_from_map_size :
    forall n m (pm: PMap n m) H,
      size (f_pw_aff_from_map pm H) = m.
  Axiom f_pw_aff_from_mapP :
    forall n m (pm: PMap n m) H,
    forall x_in val,
    forall i, (i < m)%nat ->
    (exists x_out, nth 0%Z x_out i = val /\ (x_in, x_out) \inm pm) <->
    (let pw_aff_i := nth (f_empty_pw_aff n) (f_pw_aff_from_map pm H) i in
     f_eval_pw_aff pw_aff_i x_in = Some val).

  Theorem f_pw_aff_from_map_noneP :
    forall n m (pm: PMap n m) (H: f_is_single_valued_map pm),
    forall x_in i, (i < m)%N ->
    let pw_aff_i := nth (f_empty_pw_aff n) (f_pw_aff_from_map pm H) i in
    f_eval_pw_aff pw_aff_i x_in = None <->
    (~ exists x_out, (x_in, x_out) \inm pm).
  Proof.
    move => n m pm Hsingle x_in i Hi.
    split.
    - move => HNone [x_out Hin].
      move: (f_pw_aff_from_mapP n m pm Hsingle x_in (nth 0 x_out i) i Hi) => [H _].
      have Hx_out: (exists x_out0, nth 0 x_out0 i = nth 0 x_out i /\ (x_in, x_out0) \inm pm). by exists x_out.
      apply H in Hx_out. rewrite HNone in Hx_out. by [].
    - move => Hnotin.
      case Heval: (f_eval_pw_aff _ _) => [val| //]. exfalso.
      move: (f_pw_aff_from_mapP n m pm Hsingle x_in val i Hi) => [_ H].
      apply H in Heval. case: Heval => x_out [_ Hin]. apply Hnotin.
        by eauto.
  Qed.

  Theorem f_empty_set_rw :
    forall n x, x \ins (f_empty_set n) = false.
  Proof.
    move => n x.
      by rewrite (negbTE (f_empty_setP _ _)).
  Qed.

  Hint Rewrite @f_empty_set_rw @f_universe_setP @f_union_setP @f_intersect_setP
       @f_subtract_setP @f_apply_range_mapP
       @f_universe_mapP @f_id_mapP @f_union_mapP @f_intersect_mapP
       @f_pw_aff_from_affP @f_intersect_domainP @f_union_pw_affP @f_eq_setP @f_ne_setP @f_le_setP @f_indicator_functionP
       @f_add_pw_affP
       @f_empty_pw_affP
       using by first [liassr | autossr ] : prw.

  Hint Resolve @f_is_subset_setP @f_is_subset_mapP @f_project_out_setP @f_is_subset_mapP : core.

  Ltac simpl_finite_presburger_ := repeat (autorewrite with prw; simpl_map).
  Ltac simpl_finite_presburger := reflect_ne_in simpl_finite_presburger_.

  Ltac auto_finite_presburger := intros ; simpl_finite_presburger; autossr.

End FPresburgerImpl.