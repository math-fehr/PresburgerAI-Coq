From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ssrbool Ensembles.
From PolyAI Require Export PFunc LSSA AbstractDomain.

Local Open Scope string_scope.

Section PFuncAbstractDomain.

  Context {PMap PSet PwAff: eqType}
          {PI: PresburgerImpl PMap PSet PwAff}.

  Definition concrete_state := prod_eqType RegisterMap RegisterMap.

  Definition PFuncMap := @total_map_eqType string_eqType (@PFunc_eqType PSet PwAff).

  Definition bot_PFuncMap : PFuncMap :=
    (_ !-> constant_pfunc VBot).

  Definition top_PFuncMap : PFuncMap :=
    (_ !-> constant_pfunc VTop).

  Definition join_PFuncMap (p1 p2: PFuncMap) :=
    t_pointwise_bin_op p1 p2 (fun x1 x2 => join_pfunc x1 x2).

  Definition gamma_PFuncMap (p: PFuncMap) :=
    fun (x: concrete_state) => forall i, in_V (x.2 i) (eval_pfunc (p i) x.1).

  Theorem gamma_top_PFuncMap :
    forall x, Ensembles.In _ (gamma_PFuncMap top_PFuncMap) x.
  Proof.
    move => x. rewrite /In /gamma_PFuncMap /top_PFuncMap.
    by auto_pfunc.
  Qed.

  Theorem gamma_bot_PFuncMap :
    forall x, ~ Ensembles.In _ (gamma_PFuncMap bot_PFuncMap) x.
  Proof.
    rewrite /In /gamma_PFuncMap /bot_PFuncMap => x /(_ "").
    by simpl_pfunc.
  Qed.

  Theorem join_sound_l_PFuncMap :
    forall a1 a2, Included _ (gamma_PFuncMap a1) (gamma_PFuncMap (join_PFuncMap a1 a2)).
  Proof.
    rewrite /Included /In /gamma_PFuncMap /join_PFuncMap => a1 a2 x Hle s.
    move => /(_ s) in Hle. move: Hle. simpl_pfunc.
    apply le_V_spec.
      by auto_pfunc.
  Qed.

  Theorem join_sound_r_PFuncMap :
    forall a1 a2, Included _ (gamma_PFuncMap a2) (gamma_PFuncMap (join_PFuncMap a1 a2)).
  Proof.
    rewrite /Included /In /gamma_PFuncMap /join_PFuncMap => a1 a2 x Hle s.
    move => /(_ s) in Hle. move: Hle. simpl_pfunc.
    apply le_V_spec.
    by auto_pfunc.
  Qed.

  Instance adom_pmap : adom concrete_state PFuncMap :=
    {
      bot := bot_PFuncMap;
      top := top_PFuncMap;
      join := join_PFuncMap;

      gamma := gamma_PFuncMap;

      gamma_top := gamma_top_PFuncMap;
      gamma_bot := gamma_bot_PFuncMap;
      join_sound_l := join_sound_l_PFuncMap;
      join_sound_r := join_sound_r_PFuncMap;
    }.


End PFuncAbstractDomain.
