From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export Presburger AbstractDomain RelationalAbstractDomain LSSA.

Section PMapAbstractDomain.

  Context {PMap PSet PwAff: eqType}
          {PI: PresburgerImpl PMap PSet PwAff}.

  Definition concrete_state := prod_eqType RegisterMap RegisterMap.

  Definition gamma_pmap (m: PMap) : Ensemble concrete_state:=
    fun R => eval_pmap m R.1 R.2.

  Theorem gamma_pmap_monotone :
    forall a1 a2, is_subset_map a1 a2 <-> Included concrete_state (gamma_pmap a1) (gamma_pmap a2).
  Proof.
    move => a1 a2.
    rewrite is_subset_map_spec /Included.
    split.
    - move => Hle [x1 x2] HIn.
      by apply (Hle x1 x2).
    - move => Hle x1 x2 Heval.
      set x := (x1, x2).
      have -> : x1 = x.1 by [].
      have -> : x2 = x.2 by [].
      by apply Hle.
  Qed.

  Theorem gamma_pmap_top :
    forall x, In concrete_state (gamma_pmap universe_map) x.
  Proof.
    move => x.
    rewrite /gamma_pmap /In.
      by auto_presburger.
  Qed.

  Theorem gamma_pmap_bot :
    forall x, ~ In concrete_state (gamma_pmap empty_map) x.
  Proof.
    move => x.
    rewrite /gamma_pmap /In.
      by auto_presburger.
  Qed.

  Theorem join_pmap_sound_l :
    forall a1 a2, is_subset_map a1 (union_map a1 a2).
  Proof.
    move => a1 a2.
    apply is_subset_map_spec => x1 x2.
      by simpl_presburger => ->.
  Qed.

  Theorem join_pmap_sound_r :
    forall a1 a2, is_subset_map a2 (union_map a1 a2).
  Proof.
    move => a1 a2.
    apply is_subset_map_spec => x1 x2.
    simpl_presburger => ->.
    by autossr.
  Qed.

  Instance adom_pmap : adom concrete_state PMap :=
    {
      le := is_subset_map;
      bot := empty_map;
      top := universe_map;
      join := union_map;

      gamma := gamma_pmap;

      le_refl := is_subset_map_refl;
      le_trans := is_subset_map_trans;
      gamma_monotone := gamma_pmap_monotone;
      gamma_top := gamma_pmap_top;
      gamma_bot := gamma_pmap_bot;
      join_sound_l := join_pmap_sound_l;
      join_sound_r := join_pmap_sound_r;
    }.

  Theorem pmap_id_relation_spec :
    forall x0 x1, In _ (gamma id_map) (x0, x1) <-> x0 = x1.
  Proof.
    move => x0 x1.
    rewrite /In /gamma /= /gamma_pmap /= id_map_spec.
      by split; autossr.
  Qed.

  Theorem pmap_compose_relation_spec :
    forall a1 a2 x0 x2, In _ (gamma (map_apply_range a1 a2)) (x0, x2) <->
                   exists x1, In _ (gamma a1) (x0, x1) /\ In _ (gamma a2) (x1, x2).
  Proof.
    move => a1 a2 x0 x2.
    rewrite /In /gamma /= /gamma_pmap /=.
      by apply map_apply_range_spec.
  Qed.

  Instance adom_relational_pmap : adom_relational adom_pmap :=
    {
      id_relation := id_map;
      id_relation_spec := pmap_id_relation_spec;

      compose_relation := map_apply_range;
      compose_relation_spec := pmap_compose_relation_spec;

      compose_bot := map_apply_range_bot;

      transitive_closure := transitive_closure_map;
      transitive_closure_ge_id := transitive_closure_map_ge_id;
      transitive_closure_ge_step := transitive_closure_map_ge_step;
      transitive_closure_eq_compose := transitive_closure_map_eq_compose;
    }.

End PMapAbstractDomain.
