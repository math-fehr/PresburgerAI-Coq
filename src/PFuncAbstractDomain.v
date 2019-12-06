From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ssrbool Ensembles.
From PolyAI Require Export PFunc LSSA AbstractDomain.

Local Open Scope string_scope.

Section PFuncAbstractDomain.

  Context {PFunc: eqType}
          {PFI: PFuncImpl PFunc}.

  Definition concrete_state := prod_eqType RegisterMap RegisterMap.

  Definition PFuncAD := @total_map_eqType string_eqType PFunc.

  Definition bot_PFunc : PFuncAD :=
    (_ !-> constant_pfunc VBot).

  Definition top_PFunc : PFuncAD :=
    (_ !-> constant_pfunc VTop).

  Definition join_PFunc (p1 p2: PFuncAD) :=
    t_pointwise_bin_op p1 p2 (fun x1 x2 => join_pfunc x1 x2).

  Definition gamma_PFunc (p: PFuncAD) :=
    fun (x: concrete_state) => forall i, in_V (x.2 i) (eval_pfunc (p i) (t_pointwise_un_op x.1 VVal)).

  Theorem gamma_top_PFunc :
    forall x, Ensembles.In _ (gamma_PFunc top_PFunc) x.
  Proof.
    move => x. rewrite /In /gamma_PFunc /top_PFunc => i /=.
    by auto_pfunc.
  Qed.

  Theorem gamma_bot_PFunc :
    forall x, ~ Ensembles.In _ (gamma_PFunc bot_PFunc) x.
  Proof.
    rewrite /In /gamma_PFunc /bot_PFunc => x /(_ "").
    by simpl_pfunc.
  Qed.

  Theorem join_sound_l_PFunc :
    forall a1 a2, Included _ (gamma_PFunc a1) (gamma_PFunc (join_PFunc a1 a2)).
  Proof.
    rewrite /Included /In /gamma_PFunc /join_PFunc => a1 a2 x Hle s.
    move => /(_ s) in Hle. move: Hle.
    simpl_pfunc.
    apply le_V_spec.
    pose proof join_pfunc_spec_l.
      by setoid_rewrite le_pfunc_spec in H.
  Qed.

  Theorem join_sound_r_PFunc :
    forall a1 a2, Included _ (gamma_PFunc a2) (gamma_PFunc (join_PFunc a1 a2)).
  Proof.
    rewrite /Included /In /gamma_PFunc /join_PFunc => a1 a2 x Hle s.
    move => /(_ s) in Hle. move: Hle.
    simpl_pfunc.
    apply le_V_spec.
    pose proof join_pfunc_spec_r.
      by setoid_rewrite le_pfunc_spec in H.
  Qed.

  Instance adom_pmap : adom concrete_state PFuncAD :=
    {
      bot := bot_PFunc;
      top := top_PFunc;
      join := join_PFunc;

      gamma := gamma_PFunc;

      gamma_top := gamma_top_PFunc;
      gamma_bot := gamma_bot_PFunc;
      join_sound_l := join_sound_l_PFunc;
      join_sound_r := join_sound_r_PFunc;
    }.

End PFuncAbstractDomain.
