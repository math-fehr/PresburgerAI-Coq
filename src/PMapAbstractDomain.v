From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export Presburger AbstractDomain LSSA.

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

End PMapAbstractDomain.
