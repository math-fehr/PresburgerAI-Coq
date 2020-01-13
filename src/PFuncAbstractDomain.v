From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ssrbool Ensembles.
Local Set Warnings "-notation-overridden".
From PolyAI Require Export PFunc LSSA AbstractDomain RelationalAbstractDomain ssrseq.
From mathcomp Require Import ssrnat eqtype.

Local Open Scope string_scope.

Module PFuncMap (FPI: FPresburgerImpl).
  Import FPI.
  Module PFI := PFuncImpl FPI.
  Import PFI.

  Definition concrete_state := prod_eqType RegisterMap RegisterMap.

  Definition to_var_values_seq (p: Program) (R: RegisterMap) :=
    [ seq R v | v <- vars_in_program p ].

  Fixpoint to_var_values_map_ (p: Program) (pairs: seq (string_eqType * Z)) :=
    match pairs with
    | [::] => TDefault 0%Z
    | (k,v)::pairs' => (k !-> v; to_var_values_map_ p pairs')
    end.

  Theorem to_var_values_map_inbounds :
    forall p pairs i,
      uniq (unzip1 pairs) ->
      i < size pairs ->
      (to_var_values_map_ p pairs) (nth "" (unzip1 pairs) i) = nth 0%Z (unzip2 pairs) i.
  Proof.
    move => p. elim => [ // | ].
    move => [k v] pairs Hind [|i] /= /andP[Hknotin Huniq] Hi; first by simpl_map.
    rewrite t_update_neq. auto.
    apply /eqP => Hk.
    move => /negP in Hknotin. apply Hknotin.
    rewrite Hk. apply mem_nth.
    rewrite ltnS in Hi. by rewrite size_map.
  Qed.

  Theorem to_var_values_map_outbounds :
    forall p keys values i,
      i >= size values ->
      i < size keys ->
      uniq keys ->
      (to_var_values_map_ p (zip keys values)) (nth "" keys i) = 0%Z.
  Proof.
    move => p. elim => [ [|k v] // | k keys Hind values i Hikeys Hivalues Huniq].
    case: values Hikeys => [// | v values Hikeys].
    case: i Hikeys Hivalues => [ // | i /= Hikeys Hivalues]. rewrite !ltnS in Hikeys Hivalues.
    move: Huniq => /= /andP[Hkey Huniq].
    rewrite /= t_update_neq; auto.
    apply /eqP => Hknth. move => /negP in Hkey. apply Hkey.
    eapply (mem_nth "") in Hivalues. by rewrite -Hknth in Hivalues.
  Qed.

  Definition to_var_values_map (p: Program) (s: seq Z) :=
    let vars := vars_in_program p in
    to_var_values_map_ p (zip vars s).


  Theorem to_var_values_mapP :
    forall p s i, i < size (vars_in_program p) ->
             (to_var_values_map p s) (nth "" (vars_in_program p) i) =
             nth 0%Z s i.
  Proof.
    move => p s i Hi.
    move: (uniq_vars_in_program p) => Huniq.
    move: (zip_uniq _ _ "" 0%Z (vars_in_program p) s Huniq) => Huniq_zip.
    case Hsize: (i < size s).
    - move: (to_var_values_map_inbounds p (zip (vars_in_program p) s) i).
      rewrite /unzip1. have Huniq_map: (uniq [seq i.1 | i <- zip (vars_in_program p) s]).
      + move Hsez: (unzip1 (zip (vars_in_program p) s)) => sez.
        rewrite map_inj_in_uniq => [// | [x1 x2] [y1 y2] Hx Hy].
        move: (index_uniq_zip _ _ _ _ _ _ Huniq Hx) => Hxindex.
        move: (index_uniq_zip _ _ _ _ _ _ Huniq Hy) => Hyindex.
        move => /= Heq. subst. rewrite -Hxindex in Hyindex.
        rewrite -(nth_index ("",0%Z) Hx).
        rewrite -(nth_index ("",0%Z) Hy).
        by rewrite Hyindex.
      + move => /(_ Huniq_map).
        have: (i < size (zip (vars_in_program p) s)). rewrite size_zip leq_min. by autossr.
        move => Hi' /(_ Hi'). rewrite /to_var_values_map.
        rewrite (nth_map ("", 0%Z)) => //. rewrite nth_zip_cond Hi' /= => ->.
        rewrite (nth_map ("", 0%Z)) => //. by rewrite nth_zip_cond Hi' /=.
    - rewrite [in X in _ = X]nth_default; last first. rewrite leqNgt. by rewrite Hsize.
      rewrite /to_var_values_map.
      rewrite to_var_values_map_outbounds => //.
      rewrite leqNgt. by rewrite Hsize.
  Qed.

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
    all (fun i => nth 0%Z x.2 i \inV (eval_pfunc (nth (constant_pfunc _ VTop) (sval pf) i) x.1)) (iota 0 n).

  Definition gamma_PFuncMap {p: Program} (pf: PFuncMap p) (x: concrete_state) :=
    gamma_seq_PFuncMap pf (to_var_values_seq p x.1, to_var_values_seq p x.2).

  Theorem gamma_top_PFuncMap :
    forall p x, Ensembles.In _ (gamma_PFuncMap (top_PFuncMap p)) x.
  Proof.
    move => p x. rewrite /In /gamma_PFuncMap /gamma_seq_PFuncMap /=.
    apply /allP => i Hi. rewrite nth_nseq. rewrite mem_iota in Hi. move: Hi. move => /andP[_ Hi].
    rewrite add0n in Hi. rewrite Hi /eval_pfunc.
      by auto_pfunc.
  Qed.

  Theorem gamma_bot_PFuncMap :
    forall p x, ~ Ensembles.In _ (gamma_PFuncMap (bot_PFuncMap p)) x.
  Proof.
    rewrite /In /gamma_PFuncMap /gamma_seq_PFuncMap /bot_PFuncMap => p x /allP /(_ 0).
    have Hiniota: (0 \in iota 0 (size (vars_in_program p))). rewrite mem_iota. apply /andP. split; auto. rewrite add0n. apply size_vars_in_program.
    move => /(_ Hiniota). rewrite nth_nseq. rewrite size_vars_in_program.
    by simpl_pfunc.
  Qed.

  Theorem join_sound_l_PFuncMap :
    forall p a1 a2, Included _ (@gamma_PFuncMap p a1) (gamma_PFuncMap (join_PFuncMap a1 a2)).
  Proof.
    rewrite /Included /In /gamma_PFuncMap /gamma_seq_PFuncMap /join_PFuncMap /= => p [a1 size_a1] [a2 size_a2] x.
    apply sub_all_in => i /=. case Hin: (i \in iota _ _) => //. rewrite !implyTb.
    erewrite nth_map. erewrite nth_zip. rewrite /= join_pfuncP. apply le_V_spec. apply join_V_leftP.
    by move: size_a1 size_a2 => /eqP -> /eqP ->.
    rewrite size_zip. move: size_a1 size_a2 => /eqP -> /eqP ->. rewrite minnn.
    move: Hin. rewrite mem_iota => /andP[_]. by rewrite add0n.
    Unshelve. eapply constant_pfunc. apply VTop.
  Qed.

  Theorem join_sound_r_PFuncMap :
    forall p a1 a2, Included _ (@gamma_PFuncMap p a2) (gamma_PFuncMap (join_PFuncMap a1 a2)).
  Proof.
    rewrite /Included /In /gamma_PFuncMap /gamma_seq_PFuncMap /join_PFuncMap /= => p [a1 size_a1] [a2 size_a2] x.
    apply sub_all_in => i /=. case Hin: (i \in iota _ _) => //. rewrite !implyTb.
    erewrite nth_map. erewrite nth_zip. rewrite /= join_pfuncP. apply le_V_spec. apply join_V_rightP.
    by move: size_a1 size_a2 => /eqP -> /eqP ->.
    rewrite size_zip. move: size_a1 size_a2 => /eqP -> /eqP ->. rewrite minnn.
    move: Hin. rewrite mem_iota => /andP[_]. by rewrite add0n.
    Unshelve. eapply constant_pfunc. apply VTop.
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
    rewrite /gamma_PFuncMap /In /gamma_seq_PFuncMap /=.
    apply /allP => i. rewrite mem_iota add0n => /andP[_ Hi]. rewrite nth_mkseq => [ | //].
    auto_pfunc.
  Qed.

  Definition get_intersected_assumed_set {n: nat} (pf: seq (PFunc n)) : PSet n :=
    foldl (fun acc val => f_intersect_set acc val) (f_universe_set _) [seq Assumed val | val <- pf].

  Theorem get_intersected_assumed_setP :
    forall n pf x, x \ins (@get_intersected_assumed_set n pf) = all (fun pfunc => x \ins (Assumed pfunc)) pf.
  Proof.
    move => n pf x. rewrite /get_intersected_assumed_set.
    pose A := fun (s: PSet n) => (x \ins s).
    have HA : forall s, A s = (x \ins s). by rewrite /A.
    rewrite -HA fold_intersection.
    - rewrite /A. simpl_pfunc. by rewrite all_map /=.
    - move => acc a. rewrite /A. by simpl_pfunc.
  Qed.

  Definition get_unioned_bot_set {n: nat} (pf: seq (PFunc n)) :=
    foldl (fun acc val => f_union_set acc val) (f_empty_set _) [seq pfunc_get_bot_set val | val <- pf ].

  Theorem get_unioned_bot_setP :
    forall n pf x, x \ins (@get_unioned_bot_set n pf) = has (fun pfunc => x \ins (pfunc_get_bot_set pfunc)) pf.
  Proof.
    move => n pf x.
    pose A := fun (s: PSet n) => (x \ins s).
    have HA : forall s, A s = (x \ins s). by rewrite /A.
    rewrite -HA fold_union /=.
    - rewrite /A. simpl_pfunc. by rewrite has_map.
    - move => acc a. rewrite /A. by simpl_pfunc.
  Qed.

  Theorem get_unioned_bot_set_pfuncmapP :
    forall p pf x_in, (to_var_values_seq p x_in) \ins (get_unioned_bot_set (sval pf)) <-> forall x_out, ~ (In _ (@gamma_PFuncMap p pf) (x_in, x_out)).
  Proof.
    move => p [x_pf H_pf] x_in /=. rewrite /In /gamma_PFuncMap /gamma_seq_PFuncMap /=. move => /eqP in H_pf.
    set top_pfunc := {| Val := _ |}.
    split => [ HIn x_out /= | HIn ].
    - apply /negP /allPn.
      move: HIn. rewrite get_unioned_bot_setP => /hasP [pfunc /nthP Hpfunc_in x_in_in].
      move => /(_ top_pfunc) in Hpfunc_in. move: Hpfunc_in => [i [Hi Hnth]].
      exists i. rewrite mem_iota. apply /andP. split; auto. by rewrite add0n -H_pf.
      rewrite Hnth.
      rewrite pfunc_get_bot_setP in x_in_in. move => /eqP in x_in_in. by rewrite x_in_in.
    - rewrite get_unioned_bot_setP. apply /hasP.
      set x_out := ([ seq match eval_pfunc pfunc (to_var_values_seq p x_in) with | VTop | VBot => 0%Z | VVal v => v end | pfunc <- x_pf ]).
      set x_out_map := to_var_values_map p x_out.
      move: HIn => /(_ x_out_map) /negP /allPn [i Hi Hnotin].
      move: Hi. rewrite mem_iota => /andP[_ Hi]. rewrite add0n in Hi.
      rewrite {1}/to_var_values_seq (nth_map "") in Hnotin => //.
      rewrite /x_out_map to_var_values_mapP /x_out in Hnotin => //.
      erewrite (nth_map top_pfunc) in Hnotin; last by rewrite H_pf.
      move: Hnotin. case Heval: (eval_pfunc _ _) => [ // | n | ]. by rewrite /in_V eq_refl.
      move => _. exists (nth top_pfunc x_pf i). apply mem_nth. by rewrite H_pf.
        by rewrite pfunc_get_bot_setP Heval.
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
    rewrite /gamma_seq_PFuncMap /= /allP in Hgamma.
    have Hiota : (i \in iota 0 (size (vars_in_program p))). rewrite mem_iota. apply /andP => //.
    move => /allP /(_ i Hiota) in Hgamma. rewrite /eval_pfunc in Hgamma.
    rewrite (get_intersected_assumed_setP n pf x_in) in Hintersected.
    move => /allP in Hintersected. move: Hgamma.
    rewrite Hintersected. case_match => [ v /= /eqP -> // | //].
    apply mem_nth. by rewrite Hpf_eq.
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

  (*
  Program Definition compose_relation_PFuncMap {p: Program} (pf1 pf2: PFuncMap p) : PFuncMap p :=
    let map1 := pfuncmap_to_map pf1 in
    let new_val := fun pf => f_apply_map_to_pw_aff map1 (is_single_valued_pfunc_map_to_map p pf1) (Val pf) in
    let new_assumed_pf1 := get_intersected_assumed_set (sval pf1) in
    let new_assumed_pf2 := fun pf => f_get_domain_map (f_intersect_range_map map1 (Assumed pf)) in
    let new_assumed := fun pf => f_intersect_set new_assumed_pf1 (new_assumed_pf2 pf) in
    [ seq (mkPFunc (new_val pf) (new_assumed pf)) | pf <- sval pf2 ].
  Next Obligation.
    rewrite size_map. by case pf2 => //.
  Defined. *)

  (* Fail Instance adom_relational_pmap (p: Program) : adom_relational (adom_pmap p) :=
    {
      id_relation := id_relation_PFuncMap p;
      id_relation_spec := id_relation_PFuncMapP p;

      compose_relation := compose_relation_with_bot_PFuncMap;
      compose_relation_spec := compose_relation_with_bot_PFuncMapP p;
      compose_bot := compose_relation_bot_PFuncMap p;
    }. *)

End PFuncMap.
