From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ssrbool Ensembles.
From PolyAI Require Export PFunc LSSA AbstractDomain RelationalAbstractDomain.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat eqtype.

Local Open Scope string_scope.

Module PFuncMap (FPI: FPresburgerImpl).
  Import FPI.
  Module PFI := PFuncImpl FPI.
  Import PFI.

  Definition concrete_state := prod_eqType RegisterMap RegisterMap.

  Definition to_var_values_seq (p: Program) (R: RegisterMap) :=
    [ seq R v | v <- vars_in_program p ].

  Definition PFuncMap (p: Program) :=
    let n := size (vars_in_program p) in
    { x: seq (PFunc_eqType n) | size x == n}.

  Program Definition bot_PFuncMap (p: Program) : PFuncMap p :=
    let n := size (vars_in_program p) in
    (nseq n (constant_pfunc n VBot)).
  Next Obligation.
      by rewrite size_nseq.
  Qed.

  Program Definition top_PFuncMap (p: Program) : PFuncMap p :=
    let n := size (vars_in_program p) in
    nseq n (constant_pfunc n VTop).
  Next Obligation.
      by rewrite size_nseq.
  Qed.

  Program Definition join_PFuncMap {p: Program} (p1 p2: PFuncMap p) : PFuncMap p :=
    [ seq join_pfunc x.1 x.2 | x <- zip p1 p2].
  Next Obligation.
    rewrite size_map size_zip.
    case: p1. case: p2.
    move => x /eqP -> x0 /eqP ->.
      by rewrite ssrnat.minnn.
  Qed.

  Definition gamma_seq_PFuncMap {p: Program} (pf: PFuncMap p) (x: seq Z * seq Z) :=
    let n := size (vars_in_program p) in
    forall i, i < n -> nth 0%Z x.2 i \inV (eval_pfunc (nth (constant_pfunc _ VTop) (sval pf) i) x.1).

  Definition gamma_PFuncMap {p: Program} (pf: PFuncMap p) (x: concrete_state) :=
    gamma_seq_PFuncMap pf (to_var_values_seq p x.1, to_var_values_seq p x.2).

  Theorem gamma_top_PFuncMap :
    forall p x, Ensembles.In _ (gamma_PFuncMap (top_PFuncMap p)) x.
  Proof.
    move => p x n i Hibounds. rewrite nth_nseq. rewrite Hibounds.
    by auto_pfunc.
  Qed.

  Theorem gamma_bot_PFuncMap :
    forall p x, ~ Ensembles.In _ (gamma_PFuncMap (bot_PFuncMap p)) x.
  Proof.
    rewrite /In /gamma_PFuncMap /bot_PFuncMap => p x /(_ 0).
    rewrite size_vars_in_program => /(_ is_true_true).
    rewrite nth_nseq.
    case_if. by simpl_pfunc.
      by rewrite size_vars_in_program in H.
  Qed.

    Theorem join_sound_l_PFuncMap :
      forall p a1 a2, Included _ (@gamma_PFuncMap p a1) (gamma_PFuncMap (join_PFuncMap a1 a2)).
    Proof.
      rewrite /Included /In /gamma_PFuncMap /join_PFuncMap => p [a1 size_a1] [a2 size_a2].
      move: (size_a1) (size_a2).
      move => /eqP in size_a1. move => /eqP in size_a2.
      move => size_a1' size_a2' x Hle n i.
      move => /(_ i) in Hle. move: Hle. simpl_pfunc.
      move => Htemp Hibounds. move: (Htemp Hibounds).
      apply le_V_spec.
      case Hs : (i < size a1).
      - erewrite nth_map; last first. by rewrite size_zip size_a1 size_a2 minnn -size_a1.
        erewrite nth_zip; last first. by rewrite size_a1 size_a2.
        rewrite /= join_pfuncP.
          by apply join_V_leftP.
      - rewrite !nth_default.
        + by apply le_V_refl.
        + rewrite size_map size_zip size_a1 size_a2 minnn -size_a1.
            by rewrite leqNgt Hs.
        + by rewrite leqNgt Hs.
    Unshelve.
      eapply constant_pfunc.
      by apply VTop.
    Qed.

    Theorem join_sound_r_PFuncMap :
      forall p a1 a2, Included _ (@gamma_PFuncMap p a2) (gamma_PFuncMap (join_PFuncMap a1 a2)).
    Proof.
      rewrite /Included /In /gamma_PFuncMap /join_PFuncMap => p [a1 size_a1] [a2 size_a2].
      move: (size_a1) (size_a2).
      move => /eqP in size_a1. move => /eqP in size_a2.
      move => size_a1' size_a2' x Hle n i.
      move => /(_ i) in Hle. move: Hle. simpl_pfunc.
      move => Htemp Hibounds. move: (Htemp Hibounds).
      apply le_V_spec.
      case Hs : (i < size a2).
      - erewrite nth_map; last first. by rewrite size_zip size_a1 size_a2 minnn -size_a2.
        erewrite nth_zip; last first. by rewrite size_a1 size_a2.
        rewrite /= join_pfuncP.
          by apply join_V_rightP.
      - rewrite !nth_default.
        + by apply le_V_refl.
        + rewrite size_map size_zip size_a1 size_a2 minnn -size_a2.
            by rewrite leqNgt Hs.
        + by rewrite leqNgt Hs.
          Unshelve.
          eapply constant_pfunc.
            by apply VTop.
    Qed.

    Definition PFuncMap_eqMixin (p: Program) :=
      let n := size (vars_in_program p) in
      @sig_eqMixin (seq_eqType (PFunc_eqType n)) (fun x => size x == n).
    Canonical PFuncMap_eqType (p: Program) := Eval hnf in EqType (PFuncMap p) (PFuncMap_eqMixin p).

  Instance adom_pmap (p: Program) : adom concrete_state (PFuncMap_eqType p) p :=
    {
      bot := bot_PFuncMap p;
      top := top_PFuncMap p;
      join := join_PFuncMap;

      gamma := gamma_PFuncMap;

      gamma_top := gamma_top_PFuncMap p;
      gamma_bot := gamma_bot_PFuncMap p;
      join_sound_l := join_sound_l_PFuncMap p;
      join_sound_r := join_sound_r_PFuncMap p;
    }.

  Program Definition id_relation_PFuncMap (p: Program) : PFuncMap p :=
    let n := size (vars_in_program p) in
    mkseq (fun var => constant_var_pfunc n var) n.
  Next Obligation.
      by rewrite size_mkseq.
  Qed.

  Theorem id_relation_PFuncMapP (p: Program) :
    forall x, In _ (gamma_PFuncMap (id_relation_PFuncMap p)) (x, x).
  Proof.
    move => x.
    rewrite /gamma_PFuncMap /In /= => i n Hibound.
    rewrite nth_mkseq => [ | //].
    auto_pfunc.
  Qed.

  Definition get_intersected_assumed_set_aux {n: nat} (pf: seq (PFunc n)) (base: PSet n) : PSet n :=
    foldl (fun acc val => f_intersect_set acc (Assumed val)) base pf.

  Definition get_intersected_assumed_set {n: nat} (pf: seq (PFunc n)) : PSet n :=
    get_intersected_assumed_set_aux pf (f_universe_set n).

  Theorem get_intersected_assumed_set_base :
    forall n (pf: seq (PFunc n)) base,
      f_is_subset_set (get_intersected_assumed_set_aux pf base) base.
  Proof.
    move => n. elim. by auto_finite_presburger.
    move => p pf Hind base /=.
    eapply f_is_subset_set_trans. by apply Hind.
      by autossr.
  Qed.

  Theorem get_intersected_assumed_setP :
    forall n (pf: seq (PFunc n)),
      forall i, i < size pf ->
           forall default base, let pf_i := nth default pf i in
                f_is_subset_set (get_intersected_assumed_set_aux pf base) (Assumed pf_i).
  Proof.
    move => n. elim => [ // | ].
    move => p pf Hind [|i] Hi default base /=.
    - rewrite /get_intersected_assumed_set_aux /=.
      eapply f_is_subset_set_trans. by apply get_intersected_assumed_set_base.
        by auto_finite_presburger.
    - apply Hind.
      by rewrite /= -[in x in _ < x]addn1 -[i.+1]addn1 ltn_add2r in Hi.
  Qed.

  Program Definition pfuncmap_to_map {p: Program} (pf: PFuncMap p) :
    PMap (size (vars_in_program p)) (size (vars_in_program p)) :=
    let map := f_concat_map [seq f_map_from_pw_aff (Val x) | x <- sval pf] in
    f_cast_map (Logic.eq_refl _) _ map.
  Next Obligation.
    case: pf => x /eqP H /=.
      by rewrite size_map H.
  Defined.

  Theorem pfuncmap_to_mapP :
    forall p, let n := size (vars_in_program p) in
      forall (pf: PFuncMap p) x_in x_out,
        gamma_seq_PFuncMap pf (x_in, x_out) ->
        ~~ (x_in \ins get_intersected_assumed_set (sval pf)) ||
        ((x_in, x_out) \inm (pfuncmap_to_map pf)).
  Proof.
    move => p n [pf Hpf_eq]. move: (Hpf_eq). move => /eqP in Hpf_eq. move => Hpf x_in x_out Hgamma.
    set top_pfunc := (constant_pfunc n VTop).
    case Hintersected: (x_in \ins _); last first. by autossr.
    rewrite /= in Hintersected.
    rewrite /pfuncmap_to_map f_cast_mapP f_concat_mapP => i Hi.
    rewrite (nth_map top_pfunc); last first. by rewrite Hpf_eq.
    rewrite f_map_from_pw_affP /=.
    rewrite /gamma_seq_PFuncMap /= in Hgamma. move => /(_ i Hi) in Hgamma. rewrite /eval_pfunc in Hgamma.
    move: (get_intersected_assumed_setP n pf i).
    rewrite Hpf_eq => /(_ Hi top_pfunc (f_universe_set n)) /= => Hle.
    move => /f_is_subset_setP /(_ x_in Hintersected) in Hle.
    rewrite Hle in Hgamma. move: Hgamma.
    case_match => [ v | //].
      by rewrite /= => /eqP ->.
  Qed.

  Theorem is_single_valued_pfunc_map_to_map :
    forall p pf, f_is_single_valued_map (@pfuncmap_to_map p pf).
  Proof.
    move => p [pf Hpf_eq]. move: (Hpf_eq). move => /eqP in Hpf_eq. move => Hpf.
    rewrite f_is_single_valued_mapP => x_in x_out1 x_out2.
    rewrite /pfuncmap_to_map !f_cast_mapP.
    rewrite !f_concat_mapP => Hin1 Hin2.
    rewrite /point_equality => i Hi.
    move => /(_ i Hi) in Hin1. move => /(_ i Hi) in Hin2.
    erewrite nth_map in Hin1; last first. by rewrite Hpf_eq.
    erewrite nth_map in Hin2; last first. by rewrite Hpf_eq.
    move => /f_map_from_pw_affP in Hin2.
    move => /f_map_from_pw_affP in Hin1.
    rewrite Hin2 in Hin1.
      by case: Hin1 => ->.
    Unshelve.
      by apply (constant_pfunc (size (vars_in_program p)) VTop).
      by apply (constant_pfunc (size (vars_in_program p)) VTop).
  Qed.

  Program Definition compose_relation_PFuncMap {p: Program} (pf1 pf2: PFuncMap p) : PFuncMap p :=
    let map1 := pfuncmap_to_map pf1 in
    let new_val := fun pf => f_apply_map_to_pw_aff map1 (is_single_valued_pfunc_map_to_map p pf1) (Val pf) in
    let new_assumed_pf1 := get_intersected_assumed_set (sval pf1) in
    let new_assumed_pf2 := fun pf => f_get_domain_map (f_intersect_range_map map1 (Assumed pf)) in
    let new_assumed := fun pf => f_intersect_set new_assumed_pf1 (new_assumed_pf2 pf) in
    [ seq (mkPFunc (new_val pf) (new_assumed pf)) | pf <- sval pf2 ].
  Next Obligation.
    rewrite size_map. by case pf2 => //.
  Defined.

  Theorem compose_relation_PFuncMapP :
    forall p x1 x0 x2 (pf1 pf2: PFuncMap p),
      In _ (gamma_PFuncMap pf1) (x0, x1) ->
      In _ (gamma_PFuncMap pf2) (x1, x2) ->
      In _ (gamma (compose_relation_PFuncMap pf1 pf2)) (x0, x2).
  Proof.
    move => p x1 x0 x2 pf1 pf2.
    move => /= Hgamma01 Hgamma12. move: (Hgamma01) (Hgamma12).
    case Hpf1: pf1 => [x_pf1 H_pf1].
    case Hpf2: pf2 => [x_pf2 H_pf2].
    rewrite /In /= /gamma_PFuncMap.
    rewrite /In /gamma_PFuncMap /= in Hgamma01 Hgamma12.
    set x0' := (to_var_values_seq p x0).
    set x1' := (to_var_values_seq p x1).
    set x2' := (to_var_values_seq p x2).
    rewrite /gamma_seq_PFuncMap /=.
    set top_pfunc := {| Val := _; Assumed := _ |}.
    move => H01 H12 i Hi.
    move => /(_ i Hi) in H01. move => /(_ i Hi) in H12.
    erewrite nth_map; last first. by move: (H_pf2) => /eqP ->.
    rewrite /eval_pfunc /= in H01 H12 *. simpl_pfunc.
    move: H01. case H0Assumed: (x0' \ins _); last first.
    - have /negb_true_iff -> : (~~ (x0' \ins get_intersected_assumed_set x_pf1)) => [ | //].
      apply /negP => Hin.
      move: (get_intersected_assumed_setP (size (vars_in_program p)) x_pf1 i).
      move: (H_pf1) => /eqP ->. move => /(_ Hi top_pfunc (f_universe_set (size (vars_in_program p)))) /=.
      rewrite f_is_subset_setP => /(_ x0' Hin).
        by rewrite H0Assumed.
    - case H0: (f_eval_pw_aff _ _) => [ v0 | ] => [ Hv0 | //].
      case Hx0'assumed: (x0' \ins get_intersected_assumed_set x_pf1) => [ /= | //].
      case_if => [ | // ].
      apply f_get_domain_mapP in H.
      case: H => x1'same. simpl_pfunc => /andP[Hevalx0_same Hout_in_assumed].
      move: (pfuncmap_to_mapP p pf1 x0' x1').
      move => /(_ Hgamma01).
      erewrite f_apply_map_to_pw_affP; last by apply Hevalx0_same.
      rewrite [in sval _]Hpf1 /= Hx0'assumed /= => Hevalx0.
      rewrite -Hpf1 in Hevalx0_same.
      move: (is_single_valued_pfunc_map_to_map p pf1) => /f_is_single_valued_mapP.
      move => /(_ x0' x1'same x1' Hevalx0_same Hevalx0) Heqx1'.
      erewrite f_eval_pset_same in Hout_in_assumed; eauto.
      rewrite Hout_in_assumed in H12.
        by erewrite f_eval_pw_aff_same; eauto.
  Qed.


  Fail Instance adom_relational_pmap (p: Program) : adom_relational (adom_pmap p) :=
    {
      id_relation := id_relation_PFuncMap p;
      id_relation_spec := id_relation_PFuncMapP p;

      compose_relation := compose_relation_PFuncMap;
      compose_relation_spec := compose_relation_PFuncMapP p;
    }.

End PFuncMap.
