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

  Theorem to_var_values_map_equality :
    forall p s, point_equality (size (vars_in_program p)) (to_var_values_seq p (to_var_values_map p s)) s.
  Proof.
    move => p s i Hi.
    rewrite /to_var_values_seq (nth_map "") => //.
    by rewrite to_var_values_mapP.
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

  Theorem gamma_seq_PFuncMap_equality :
    forall p pf x y,
      let n := size (vars_in_program p) in
      point_equality n x.1 y.1 ->
      point_equality n x.2 y.2 ->
      @gamma_seq_PFuncMap p pf x = @gamma_seq_PFuncMap p pf y.
  Proof.
    move => p pf x y n Heq1 Heq2.
    rewrite /gamma_seq_PFuncMap.
    apply eq_in_all => i. rewrite mem_iota add0n => /andP[_ Hi].
    rewrite -(eval_pfunc_same _ _ x.1 y.1) => //.
    rewrite /point_equality in Heq2. move => /(_ i Hi) in Heq2. by rewrite Heq2.
  Qed.

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

  Definition get_intersected_assumed_set_with_involves {p: Program} (pf: PFuncMap p) (pfunc: PFunc (size (vars_in_program p))) :=
    let zip_seq := zip [ seq f_involves_dim_pfunc pfunc x | x <- iota 0 (size (vars_in_program p)) ] (sval pf) in
    let seq := unzip2 (filter (fun x => x.1) zip_seq) in
    get_intersected_assumed_set seq.

  Theorem get_intersected_assumed_set_with_involvesP :
    forall p (pf: PFuncMap p) pfunc i,
      i < size (vars_in_program p) ->
      f_involves_dim_pfunc pfunc i ->
      forall x, x \ins get_intersected_assumed_set_with_involves pf pfunc ->
           forall default, x \ins (Assumed (nth default (sval pf) i)).
  Proof.
    move => p pf pfunc i Hi Hinvolves x Hin default.
    rewrite /get_intersected_assumed_set_with_involves in Hin.
    rewrite get_intersected_assumed_setP in Hin.
    move => /allP in Hin. apply Hin.
    apply /mapP. exists (true, nth default (sval pf) i) => //.
    rewrite mem_filter /=.
    set zip' := zip _ _.
    have -> : (true, nth default (sval pf) i) = nth (true, default) zip' i.
    - rewrite nth_zip; last first. rewrite size_map size_iota. by case: (pf) => [x_pf /= /eqP ->].
      erewrite (nth_map 0); last by rewrite size_iota.
      rewrite nth_iota => //. by rewrite add0n Hinvolves.
    - apply mem_nth. rewrite /zip' size_zip size_map size_iota leq_min.
      rewrite Hi. move: (pf) => [x_pf /= /eqP ->]. by apply Hi.
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
      move => /(_ top_pfunc) in Hpfunc_in. move: Hpfunc_in => [i Hi Hnth].
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

  Definition get_result_pfuncmap {p: Program} (pf: PFuncMap p) (x_in: seq Z) :=
    [seq if eval_pfunc pfunc x_in is VVal v then v else 0%Z | pfunc <- sval pf].

  Theorem get_result_pfuncmapP :
    forall p pf x_in,
      ~~(x_in \ins get_unioned_bot_set (sval pf)) ->
      let x_out := @get_result_pfuncmap p pf x_in in
      In _ (gamma_seq_PFuncMap pf) (x_in, x_out).
  Proof.
    move => p pf x_in Hnot_bot x_out. rewrite /In /gamma_seq_PFuncMap.
    apply /allP => i. rewrite mem_iota add0n => /andP [_ Hi] /=.
    rewrite /x_out /get_result_pfuncmap /eval_pfunc /=.
    set top_pfunc := {| Val := _ |}.
    erewrite (nth_map top_pfunc); last by case: (pf) => /= Hpf /eqP ->.
    case_if => [ /= | // ].
    case Heval: (f_eval_pw_aff _ _) => [ v | ]. by rewrite /=.
    rewrite get_unioned_bot_setP in Hnot_bot.
    have Hin: (nth top_pfunc (sval pf) i) \in sval pf. apply mem_nth. by case: (pf) => /= Hpf /eqP ->.
    move => /hasPn /(_ _ Hin) in Hnot_bot.
      by rewrite pfunc_get_bot_setP /eval_pfunc H Heval in Hnot_bot.
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
    rewrite Hintersected. case_match => [ /= /eqP -> // | //].
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

  Program Definition pfuncmap_to_map_with_involves {p: Program} (pf: PFuncMap p) (pfunc: PFunc (size (vars_in_program p))) :
    PMap (size (vars_in_program p)) (size (vars_in_program p)) :=
    let n := size (vars_in_program p) in
    let pairs := zip (iota 0 n) (sval pf) in
    let map := f_concat_map [seq
                               if f_involves_dim_pfunc pfunc p.1 then
                                 (f_map_from_pw_aff (Val p.2))
                               else
                                 f_map_from_pw_aff (f_pw_aff_from_aff (FAConst n 0))
                            | p <- pairs] in
    let bot_set := f_complement_set (get_unioned_bot_set (sval pf)) in
    f_intersect_domain_map (f_cast_map (Logic.eq_refl _) _ map) bot_set.
  Next Obligation.
    rewrite size_map size_zip size_iota. move: pf => [/= x_pf /eqP ->] /=. by rewrite minnn.
  Defined.

  Theorem is_single_valued_pfunc_map_to_map_with_involves :
    forall p pf pfunc, f_is_single_valued_map (@pfuncmap_to_map_with_involves p pf pfunc).
  Proof.
    move => p pf pfunc.
    rewrite f_is_single_valued_mapP => x v1 v2 Hv1 Hv2 i Hi.
    rewrite /pfuncmap_to_map_with_involves in Hv1 Hv2.
    rewrite !f_intersect_domain_mapP in Hv1 Hv2.
    move: Hv1 Hv2 => /andP[Hv1 _] /andP[Hv2 _].
    rewrite !f_cast_mapP in Hv1 Hv2.
    rewrite ->f_concat_mapP in Hv1, Hv2.
    move => /(_ i Hi) in Hv1. move => /(_ i Hi) in Hv2.
    case: pf Hv1 Hv2 => x_pf /= /eqP H_pf Hv1 Hv2.
    set top_pfunc := constant_pfunc (size (vars_in_program p)) VTop.
    erewrite (nth_map (0, top_pfunc)) in Hv1, Hv2; try (by rewrite size_zip size_iota H_pf minnn).
    rewrite nth_zip /= in Hv1; last by rewrite size_iota H_pf.
    rewrite nth_zip /= in Hv2; last by rewrite size_iota H_pf.
    move: Hv1 Hv2. rewrite nth_iota => //. rewrite add0n.
    case H_involves: (f_involves_dim_pfunc pfunc i).
    - by rewrite !f_map_from_pw_affP => -> [->].
    - by rewrite !f_map_from_pw_affP f_pw_aff_from_affP /= => [->] [->].
  Qed.

  Theorem pfuncmap_to_map_with_involves_in :
    forall p pf pfunc x_in x_out,
      let x_in_seq := to_var_values_seq p x_in in
      let x_out_seq := to_var_values_seq p x_out in
      x_in_seq \ins get_intersected_assumed_set_with_involves pf pfunc ->
      (x_in_seq, x_out_seq) \inm (@pfuncmap_to_map_with_involves p pf pfunc) ->
      exists x_out', In _ (gamma_PFuncMap pf) (x_in, x_out') /\
                (forall i, i < size (vars_in_program p) ->
                      f_involves_dim_pfunc pfunc i ->
                      nth 0%Z x_out_seq i = nth 0%Z (to_var_values_seq p x_out') i).
  Proof.
    move => p pf pfunc x_in x_out x_in_seq x_out_seq Hassumed HIn.
    set x_out'_seq := (get_result_pfuncmap pf x_in_seq).
    exists (to_var_values_map p x_out'_seq).
    rewrite /pfuncmap_to_map_with_involves in HIn.
    rewrite /In /gamma_PFuncMap /=.
    erewrite (gamma_seq_PFuncMap_equality _ _ _ (_, _)); last first. rewrite /=. apply to_var_values_map_equality.
      by apply point_equality_sym.
    rewrite /= /x_out'_seq. rewrite f_intersect_domain_mapP in HIn. move: HIn => /andP[HIn Hnot_in_bot].
    split. apply get_result_pfuncmapP. by rewrite f_complement_setP in Hnot_in_bot.
    move => i Hi Hinvolves.
    move: (to_var_values_map_equality p) => Hequal. rewrite Hequal => //.
    move: (get_result_pfuncmapP p pf x_in_seq).
    rewrite f_complement_setP in Hnot_in_bot. move => /(_ Hnot_in_bot) /= HIn_gamma.
    rewrite f_cast_mapP in HIn. move => /f_concat_mapP /(_ i Hi) /= in HIn.
    rewrite (nth_map (0%N,pfunc)) in HIn; last first. rewrite size_zip size_iota. case: (pf) => x_pf /= /eqP ->. by rewrite minnn.
    rewrite nth_zip /= in HIn; last first. rewrite size_iota. by case: (pf) => x_pf /= /eqP ->.
    rewrite nth_iota in HIn => //. rewrite add0n Hinvolves /= in HIn.
    apply f_map_from_pw_affP in HIn. rewrite /= in HIn. rewrite /get_result_pfuncmap.
    rewrite (nth_map pfunc); last by case: (pf) => x_pf /= /eqP ->.
    rewrite /eval_pfunc. rewrite HIn.
    erewrite get_intersected_assumed_set_with_involvesP; eauto.
  Qed.

  Theorem pfuncmap_to_map_with_involvesP :
    forall p pf pfunc x_in v,
      let n := size (vars_in_program p) in
      let map := pfuncmap_to_map_with_involves pf pfunc in
      let map_single_valued := is_single_valued_pfunc_map_to_map_with_involves p pf pfunc in
      let new_pfunc := apply_map_to_pfunc map map_single_valued pfunc in
      let top_set := get_intersected_assumed_set_with_involves pf pfunc in
      let x_in_seq := to_var_values_seq p x_in in
      x_in_seq \ins top_set ->
      (v \inV eval_pfunc (apply_map_to_pfunc map map_single_valued pfunc) x_in_seq
      <-> (exists x_mid, In _ (gamma_PFuncMap pf) (x_in, x_mid) /\ v \inV eval_pfunc pfunc (to_var_values_seq p x_mid))).
  Proof.
    move => p pf pfunc x_in v n map map_single_valued new_pfunc top_set x_in_seq H_not_top.
    split => [ HvIn | [x_mid [Hx_midIn HvIn]]].
    - apply apply_map_to_pfuncP in HvIn. case: HvIn => x_mid [Hmid_in_map Hv].
      move: (pfuncmap_to_map_with_involves_in _ pf pfunc x_in (to_var_values_map p x_mid)) => /=.
      move => /(_ H_not_top). rewrite f_eval_pmap_same_out; last by apply to_var_values_map_equality.
      move => /(_ Hmid_in_map) => [[x_out' [HIn Heq_x_out']]].
      exists x_out'. split; auto.
      erewrite eval_pfunc_same_involves. eauto.
      move => i Hi Hinvolves. move => /(_ i Hi Hinvolves) in Heq_x_out'. rewrite -Heq_x_out'.
        by rewrite to_var_values_map_equality => //.
    - rewrite apply_map_to_pfuncP.
      set x_mid_seq := to_var_values_seq p x_mid.
      exists ([seq if f_involves_dim_pfunc pfunc x.1 then x.2 else 0%Z | x <- (zip (iota 0 n) x_mid_seq)]).
      split.
      + rewrite /map /pfuncmap_to_map_with_involves.
        simpl_finite_presburger. apply /andP. split; last first.
          apply /negP. rewrite get_unioned_bot_set_pfuncmapP => /(_ x_mid). auto.
        rewrite f_concat_mapP => i Hi /=.
        erewrite (nth_map (0%N, _)); last first. rewrite size_zip size_iota leq_min. case: (pf) => x_pf /= /eqP ->. autossr.
        rewrite nth_zip /=; last first. rewrite size_iota. by case: (pf) => x_pf /= /eqP ->.
        rewrite nth_iota => //. rewrite add0n.
        case Hi_x_mid: (i < size x_mid_seq).
        * rewrite (nth_map (0%N, 0%Z)); last first. rewrite size_zip size_iota /n leq_min Hi_x_mid. autossr.
          rewrite nth_zip_cond. rewrite size_zip size_iota /n leq_min Hi Hi_x_mid /=.
          rewrite nth_iota => //. rewrite add0n.
          case Hinvolves: (f_involves_dim_pfunc pfunc i); last first. rewrite f_map_from_pw_affP. by simpl_finite_presburger.
          rewrite f_map_from_pw_affP.
          move: Hx_midIn. rewrite /In /gamma_PFuncMap /gamma_seq_PFuncMap.
          have Hiota: (i \in iota 0 (size (vars_in_program p))). rewrite mem_iota. apply /andP. split; auto.
          move => /allP /(_ i Hiota) /=.
          set top_pfunc := {| Val := _ |}.
          rewrite /eval_pfunc.
          erewrite get_intersected_assumed_set_with_involvesP; eauto.
          case_match => //.
          rewrite /= => /eqP ->. eauto.
        * rewrite [nth 0%Z _ _]nth_default; last first. rewrite size_map size_zip geq_min [size x_mid_seq <= _]leqNgt Hi_x_mid. autossr.
          case Hinvolves: (f_involves_dim_pfunc pfunc i); last first. rewrite f_map_from_pw_affP. by simpl_finite_presburger.
          rewrite f_map_from_pw_affP.
          move: Hx_midIn. rewrite /In /gamma_PFuncMap /gamma_seq_PFuncMap.
          have Hiota: (i \in iota 0 (size (vars_in_program p))). rewrite mem_iota. apply /andP. split; auto.
          move => /allP /(_ i Hiota) /=.
          set top_pfunc := {| Val := _ |}.
          rewrite /eval_pfunc.
          erewrite get_intersected_assumed_set_with_involvesP; eauto.
          case_match => //.
          rewrite H. rewrite nth_default; last first. rewrite leqNgt. by rewrite Hi_x_mid.
          rewrite /= => /eqP ->. eauto.
      + rewrite (eval_pfunc_same_involves _ _ _ x_mid_seq) => //.
        move => i Hi Hinvolves.
        case Hi_x_mid: (i < size x_mid_seq).
        * rewrite (nth_map (0%N, 0%Z)); last first. rewrite size_zip size_iota /n leq_min. autossr.
          rewrite nth_zip_cond size_zip size_iota /n leq_min Hi Hi_x_mid /= nth_iota => //.
            by rewrite add0n Hinvolves.
        * rewrite nth_default. rewrite nth_default => //. by rewrite leqNgt Hi_x_mid.
          rewrite size_map size_zip size_iota /n geq_min [in X in _ || X]leqNgt Hi_x_mid.
          autossr.
  Qed.


  Program Definition compose_relation_PFuncMap {p: Program} (pf1 pf2: PFuncMap p) : PFuncMap p :=
    let n := size (vars_in_program p) in
    let map1 : PFunc n -> PMap n n := fun pf => pfuncmap_to_map_with_involves pf1 pf in
    let map1_single_valued := fun pf => is_single_valued_pfunc_map_to_map_with_involves p pf1 pf in
    let bot_inputs := get_unioned_bot_set (sval pf1) in
    let new_assumed_pf1 := fun pf => get_intersected_assumed_set_with_involves (sval pf1) pf in
    let new_pfunc := fun pf => apply_map_to_pfunc (map1 pf) (map1_single_valued pf) pf in
    let new_pfunc' := fun pf => intersect_assumed (new_pfunc pf) (new_assumed_pf1 pf) in
    [ seq (new_pfunc' pf) | pf <- sval pf2 ].
  Next Obligation.
      by case pf1 => x_pf ->.
  Defined.
  Next Obligation.
    rewrite size_map. by case pf2 => x_pf ->.
  Defined.

  Definition compose_relation_PFuncMap_with_bot {p: Program} (pf1 pf2: PFuncMap p) : PFuncMap p :=
    if pf2 == bot_PFuncMap p then
      bot_PFuncMap p
    else
      compose_relation_PFuncMap pf1 pf2.

  Theorem compose_relation_PFuncMapP :
    forall p x1 x0 x2 (a1 a2: PFuncMap p),
      In _ (gamma_PFuncMap a1) (x0, x1) ->
      In _ (gamma_PFuncMap a2) (x1, x2) ->
      In _ (gamma_PFuncMap (compose_relation_PFuncMap a1 a2)) (x0, x2).
  Proof.
    move => p x1 x0 x2 a1 a2 HIn1 HIn2.
    have Ha1_size: (size (sval a1) = size (vars_in_program p)). by case: (a1) => x_a1 /= /eqP ->.
    have Ha2_size: (size (sval a2) = size (vars_in_program p)). by case: (a2) => x_a2 /= /eqP ->.
    rewrite /In /gamma_PFuncMap /gamma_seq_PFuncMap /=.
    apply /allP => i. rewrite mem_iota add0n => /andP[_ Hi] /=.
    erewrite nth_map; last by rewrite Ha2_size. rewrite intersect_assumedP.
    case_if => //.
    rewrite pfuncmap_to_map_with_involvesP => //.
    exists x1. split; auto.
    rewrite /In /gamma_PFuncMap /gamma_seq_PFuncMap in HIn2.
    have Hiota: (i \in iota 0 (size (vars_in_program p))). rewrite mem_iota add0n. apply /andP. split; auto.
    move => /allP /(_ i Hiota) /= in HIn2.
    eauto.
  Qed.

  Theorem compose_relation_PFuncMap_with_botP :
    forall p x1 x0 x2 (a1 a2: PFuncMap p),
      In _ (gamma_PFuncMap a1) (x0, x1) ->
      In _ (gamma_PFuncMap a2) (x1, x2) ->
      In _ (gamma_PFuncMap (compose_relation_PFuncMap_with_bot a1 a2)) (x0, x2).
  Proof.
    move => p x1 x0 x2 a1 a2 HIn1 HIn2.
    rewrite /compose_relation_PFuncMap_with_bot.
    case: (a2 =P bot_PFuncMap p) => Hbot; last by eapply compose_relation_PFuncMapP; eauto.
    exfalso. subst. eapply gamma_bot_PFuncMap; eauto.
  Qed.

  Theorem compose_relation_bot_PFuncMap :
    forall p a, compose_relation_PFuncMap_with_bot a (bot_PFuncMap p) = (bot_PFuncMap p).
  Proof.
    move => p a. rewrite /compose_relation_PFuncMap_with_bot.
      by rewrite eq_refl.
  Qed.

  (*
  Fail Instance adom_relational_pmap (p: Program) : adom_relational (adom_pmap p) :=
    {
      id_relation := id_relation_PFuncMap p;
      id_relation_spec := id_relation_PFuncMapP p;

      compose_relation := compose_relation_PFuncMap_with_bot;
      compose_relation_spec := compose_relation_PFuncMap_with_botP p;
      compose_bot := compose_relation_bot_PFuncMap p;
    }.*)

End PFuncMap.
