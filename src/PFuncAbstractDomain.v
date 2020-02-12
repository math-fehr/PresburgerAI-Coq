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

  Theorem to_var_values_seqP :
    forall p R v, v \in vars_in_program p ->
      nth 0%Z (to_var_values_seq p R) (index v (vars_in_program p)) = R v.
  Proof.
    move => p R v Hin.
    rewrite (nth_map ""); last by rewrite index_mem.
    by rewrite nth_index.
  Qed.

  Theorem to_var_values_seq_update_neq :
    forall p R v c i, i <> index v (vars_in_program p) ->
      nth 0%Z (to_var_values_seq p (v !-> c; R)) i =
      nth 0%Z (to_var_values_seq p R) i.
  Proof.
    move => p R v c i Hindex.
    case Hi: (size (vars_in_program p) <= i).
      rewrite !nth_default => [ // | | ]; by rewrite size_map.
    rewrite leqNgt in Hi. move => /negb_false_iff in Hi.
    rewrite !(nth_map ""); try (by []).
    apply t_update_neq.
    apply /eqP => Hv. subst. rewrite index_uniq in Hindex; autossr.
      by [].
      by apply uniq_vars_in_program.
  Qed.

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

  Theorem to_var_values_map_index :
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

  Theorem to_var_values_mapP :
    forall p s v, v \in (vars_in_program p) ->
                   (to_var_values_map p s) v =
                   nth 0%Z s (index v (vars_in_program p)).
  Proof.
    move => p s v Hin.
    rewrite <-(to_var_values_map_index p); last by rewrite index_mem.
    by rewrite nth_index.
  Qed.

  Theorem to_var_values_map_equality :
    forall p s, point_equality (size (vars_in_program p)) s (to_var_values_seq p (to_var_values_map p s)).
  Proof.
    move => p s. apply /allP => i Hiota. simplssr.
    rewrite /to_var_values_seq (nth_map "") => //.
    by rewrite to_var_values_map_index.
  Qed.

  Theorem to_var_values_map_equality_sym :
    forall p s, point_equality (size (vars_in_program p)) (to_var_values_seq p (to_var_values_map p s)) s.
  Proof.
    move => p s. rewrite point_equality_sym.
    apply to_var_values_map_equality.
  Qed.

  Hint Resolve to_var_values_map_equality to_var_values_map_equality_sym : core.

  Ltac rewrite_to_var_values_map_equality p s :=
    move: (to_var_values_map_equality p s);
    let Htmp := fresh "tmp" in
    intros Htmp;
    rewrite_point_H Htmp;
    move: Htmp => _.

  Ltac rewrite_to_var_values_map_equality_sym p s :=
    move: (to_var_values_map_equality_sym p s);
    let Htmp := fresh "tmp" in
    intros Htmp;
    rewrite_point_H Htmp;
    move: Htmp => _.

  Theorem to_var_values_seq_update :
    forall p v c x,
      v \in vars_in_program p ->
      point_equality (size (vars_in_program p)) (to_var_values_seq p (v !-> c; to_var_values_map p x))
                     (set_nth 0%Z x (index v (vars_in_program p)) c).
  Proof.
    move => p v c x Hv_in. apply /allP => i Hiota.
    rewrite (nth_map ""); last by autossr.
    rewrite nth_set_nth /=.
    case: (i =P index v (vars_in_program p)) => Hi.
    - subst. rewrite nth_index; auto_map.
    - rewrite t_update_neq; last first. apply /eqP => Hv. subst.
        rewrite index_uniq in Hi. by []. by simplssr. by apply uniq_vars_in_program.
      rewrite to_var_values_map_index; by autossr.
  Qed.

  Definition PFuncMap (p: Program) :=
    let n := size (vars_in_program p) in
    { x: seq (PFunc_eqType n) | size x == n}.

  Program Definition nseq_pfuncmap (p: Program) (pf: PFunc (size (vars_in_program p))) : PFuncMap p :=
    nseq (size (vars_in_program p)) pf.
  Next Obligation.
    by rewrite size_nseq.
  Defined.

  Definition bot_PFuncMap (p: Program) : PFuncMap p :=
    let n := size (vars_in_program p) in
    nseq_pfuncmap p (constant_pfunc n VBot).

  Definition top_PFuncMap (p: Program) : PFuncMap p :=
    let n := size (vars_in_program p) in
    nseq_pfuncmap p (constant_pfunc n VTop).

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
    all (fun i => nth 0%Z x.2 i \in (eval_pfunc (nth (constant_pfunc _ VTop) (sval pf) i) x.1)) (iota 0 n).

  Theorem gamma_seq_PFuncMap_equality :
    forall p pf x y,
      let n := size (vars_in_program p) in
      point_equality n x.1 y.1 ->
      point_equality n x.2 y.2 ->
      @gamma_seq_PFuncMap p pf x = @gamma_seq_PFuncMap p pf y.
  Proof.
    move => p pf x y n Heq1 Heq2. apply eq_in_all => i Hiota.
    rewrite -/n in Hiota. rewrite /eval_pfunc.
    rewrite_point x.1 y.1.
    by rewrite_point x.2 y.2.
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

  Theorem id_relation_PFuncMap_precise :
    forall p x y, In _ (gamma_PFuncMap (id_relation_PFuncMap p)) (x, y) ->
             point_equality (size (vars_in_program p)) (to_var_values_seq p x) (to_var_values_seq p y).
  Proof.
    move => p x y. rewrite /In /gamma_PFuncMap /gamma_seq_PFuncMap => HIn.
    apply /allP => i Hi. move => /allP /(_ i Hi) /= in HIn.
    rewrite nth_mkseq in HIn; last by autossr.
    move: HIn. simpl_pfunc. by rewrite eq_sym.
  Qed.

  Definition get_intersected_assumed_set {n: nat} (pf: seq (PFunc n)) : PSet n :=
    foldl (fun acc val => f_intersect_set acc val) (f_universe_set _) [seq Assumed val | val <- pf].

  Theorem get_intersected_assumed_setP :
    forall n pf x, x \in (@get_intersected_assumed_set n pf) = all (fun pfunc => x \in (Assumed pfunc)) pf.
  Proof.
    move => n pf x. rewrite /get_intersected_assumed_set.
    pose A := fun (s: PSet n) => (x \in s).
    have HA : forall s, A s = (x \in s). by rewrite /A.
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
      forall x, x \in get_intersected_assumed_set_with_involves pf pfunc ->
           forall default, x \in (Assumed (nth default (sval pf) i)).
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
    forall n pf x, x \in (@get_unioned_bot_set n pf) = has (fun pfunc => x \in (pfunc_get_bot_set pfunc)) pf.
  Proof.
    move => n pf x.
    pose A := fun (s: PSet n) => (x \in s).
    have HA : forall s, A s = (x \in s). by rewrite /A.
    rewrite -HA fold_union /=.
    - rewrite /A. simpl_pfunc. by rewrite has_map.
    - move => acc a. rewrite /A. by simpl_pfunc.
  Qed.

  Theorem get_unioned_bot_set_indexP :
    forall n (pf: seq (PFunc n)) x,
      x \in (get_unioned_bot_set pf) =
      has (fun i => x \in (pfunc_get_bot_set (nth (constant_pfunc _ VTop) pf i))) (iota 0 (size pf)).
  Proof.
    move => n pf x. rewrite get_unioned_bot_setP.
    apply /idP/idP.
    - move => /hasP [pfunc Hin Hin_bot]. apply /hasP.
      exists (index pfunc pf). simplssr.
      + by rewrite -index_mem in Hin.
      + by rewrite nth_index.
    - move => /hasP [i Hiota Hin_bot]. apply /hasP.
      exists (nth (constant_pfunc _ VTop) pf i) => //.
      apply mem_nth. by autossr.
  Qed.

  Theorem get_unioned_bot_set_pfuncmapP :
    forall p pf x_in, (to_var_values_seq p x_in) \in (get_unioned_bot_set (sval pf)) <-> forall x_out, ~ (In _ (@gamma_PFuncMap p pf) (x_in, x_out)).
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
      rewrite /x_out_map to_var_values_map_index /x_out in Hnotin => //.
      erewrite (nth_map top_pfunc) in Hnotin; last by rewrite H_pf.
      move: Hnotin. case Heval: (eval_pfunc _ _) => [ // | n | ]. by simpl_pfunc.
      move => _. exists (nth top_pfunc x_pf i). apply mem_nth. by rewrite H_pf.
        by rewrite pfunc_get_bot_setP Heval.
  Qed.

  Theorem get_unioned_bot_set_pfuncmap_intro :
    forall p pf x_in x_out, (In _ (@gamma_PFuncMap p pf) (x_in, x_out)) ->
                       (to_var_values_seq p x_in) \notin (get_unioned_bot_set (sval pf)).
  Proof.
    move => p pf x_in x_out HIn.
    apply /negP => Hin.
    apply get_unioned_bot_set_pfuncmapP in HIn => //.
  Qed.

  Theorem get_unioned_bot_set_pw_aff_some :
    forall p (pf: PFuncMap p) x_in_map,
      let default := constant_pfunc _ VTop in
      let x_in := to_var_values_seq p x_in_map in
      (x_in \notin (get_unioned_bot_set (sval pf))) ->
      forall i, i < size (vars_in_program p) ->
        x_in \in Assumed (nth default (sval pf) i) ->
        exists x_out, f_eval_pw_aff (Val (nth default (sval pf) i)) (x_in) = Some x_out.
  Proof.
    move => p pf x_in_map default x_in Hx_notin i Hi Hassumed.
    exists (match f_eval_pw_aff (Val (nth default (sval pf) i)) x_in with | Some v => v | _ => 0%Z end).
    case_match => //.
    move => /negP /get_unioned_bot_set_pfuncmapP in Hx_notin.
    have Hiota: (i \in iota 0 (size (vars_in_program p))). autossr.
    exfalso. apply Hx_notin => x_out /allP /(_ i Hiota) /=.
    rewrite /eval_pfunc. by rewrite Hassumed H.
  Qed.

  Definition get_result_pfuncmap {p: Program} (pf: PFuncMap p) (x_in: seq Z) :=
    [seq if eval_pfunc pfunc x_in is VVal v then v else 0%Z | pfunc <- sval pf].

  Theorem get_result_pfuncmapP :
    forall p pf x_in,
      ~~(x_in \in get_unioned_bot_set (sval pf)) ->
      let x_out := @get_result_pfuncmap p pf x_in in
      In _ (gamma_seq_PFuncMap pf) (x_in, x_out).
  Proof.
    move => p pf x_in Hnot_bot x_out. rewrite /In /gamma_seq_PFuncMap.
    apply /allP => i. rewrite mem_iota add0n => /andP [_ Hi] /=.
    rewrite /x_out /get_result_pfuncmap /eval_pfunc /=.
    set top_pfunc := {| Val := _ |}.
    erewrite (nth_map top_pfunc); last by case: (pf) => /= Hpf /eqP ->.
    case_if => [ /= | // ].
    case Heval: (f_eval_pw_aff _ _) => [ v | ]. by simpl_pfunc.
    rewrite get_unioned_bot_setP in Hnot_bot.
    have Hin: (nth top_pfunc (sval pf) i) \in sval pf. apply mem_nth. by case: (pf) => /= Hpf /eqP ->.
    move => /hasPn /(_ _ Hin) in Hnot_bot.
      by rewrite pfunc_get_bot_setP /eval_pfunc H Heval in Hnot_bot.
  Qed.

  Program Definition pfuncmap_to_map {p: Program} (pf: PFuncMap p) :
    PMap (size (vars_in_program p)) (size (vars_in_program p)) :=
    if pf == bot_PFuncMap p then
      f_empty_map _ _
    else
      let map := f_concat_map [seq pfunc_to_map x | x <- sval pf] in
      f_cast_map (Logic.eq_refl _) _ map.
  Next Obligation.
    case: pf => x /eqP H /=.
      by rewrite size_map H.
  Defined.

  Theorem pfuncmap_to_mapP :
    forall p (pf: PFuncMap p) x_in x_out,
      gamma_seq_PFuncMap pf (x_in, x_out) =
      ((x_in, x_out) \in (pfuncmap_to_map pf)).
  Proof.
    move => p pf x_in x_out. rewrite /gamma_seq_PFuncMap /pfuncmap_to_map.
    case: (pf =P bot_PFuncMap p) => Hbot.
    - set n := size (vars_in_program p).
      move: (f_empty_mapP n n x_in x_out) => /negb_true_iff ->.
      rewrite Hbot /=. apply /allP => Hall.
      have Hiota: 0 \in iota 0 n. rewrite mem_iota add0n. apply /andP. split; auto. apply size_vars_in_program.
      move => /(_ 0 Hiota) in Hall. move: Hall.
      rewrite nth_nseq /eval_pfunc. by simpl_pfunc.
    - simpl_pfunc. apply eq_in_all => i Hiota.
      erewrite nth_map; last by case: (pf) => /= [x_pf /eqP ->]; autossr.
        by rewrite -pfunc_to_mapP.
  Qed.

  Program Definition map_to_pfuncmap {p: Program} (map: PMap (size (vars_in_program p)) (size (vars_in_program p))) : PFuncMap p :=
    [ seq map_to_pfunc (f_extract_dimension_map map i) | i <- iota 0 (size (vars_in_program p))].
  Next Obligation.
    by rewrite size_map size_iota.
  Defined.

  Theorem map_to_pfuncmapP :
    forall p map x_in x_out, ((to_var_values_seq p x_in, to_var_values_seq p x_out) \in map) ->
                        In _ (@gamma_PFuncMap p (map_to_pfuncmap map)) (x_in, x_out).
  Proof.
    move => p map x_in x_out Hinmap.
    rewrite /In /gamma_PFuncMap /gamma_seq_PFuncMap.
    apply /allP => i Hiota /=.
    rewrite (nth_map 0); last by rewrite size_iota; autossr.
    rewrite map_to_pfuncP. left.
    rewrite f_extract_dimension_mapP.
    exists (to_var_values_seq p x_out).
    split; auto. rewrite nth_iota; auto. autossr.
  Qed.

  Theorem map_to_pfuncmap_le :
    forall p map1 map2,
      f_is_subset_map map1 map2 ->
      le (@map_to_pfuncmap p map1) (@map_to_pfuncmap p map2).
  Proof.
    move => p map1 map2 Hsubset x.
    rewrite /In /gamma /= /gamma_PFuncMap /gamma_seq_PFuncMap /= => HIn.
    apply /allP => i Hiota. move => /allP /(_ i Hiota) in HIn.
    rewrite !(nth_map 0) in HIn *; try (by rewrite size_iota; autossr).
    move: (map_to_pfunc_le). setoid_rewrite le_V_spec. apply; eauto.
      by apply f_extract_dimension_map_le.
  Qed.

  Program Definition compose_relation_PFuncMap {p: Program} (pf1 pf2: PFuncMap p) : PFuncMap p :=
    let n := size (vars_in_program p) in
    let map1 := pfuncmap_to_map pf1 in
    let map2 := pfuncmap_to_map pf2 in
    let app_map := f_apply_range_map map1 map2 in
    map_to_pfuncmap app_map.

  Theorem compose_relation_PFuncMapP :
    forall p x1 x0 x2 (a1 a2: PFuncMap p),
      In _ (gamma_PFuncMap a1) (x0, x1) ->
      In _ (gamma_PFuncMap a2) (x1, x2) ->
      In _ (gamma_PFuncMap (compose_relation_PFuncMap a1 a2)) (x0, x2).
  Proof.
    move => p x1 x0 x2 a1 a2 HIn1 HIn2.
    rewrite /In /gamma_PFuncMap in HIn1 HIn2 *.
    rewrite !pfuncmap_to_mapP /= in HIn1 HIn2.
    apply /allP => i Hiota /=.
    rewrite (nth_map 0); last by rewrite size_iota; by autossr.
    rewrite map_to_pfuncP. left.
    rewrite f_extract_dimension_mapP.
    exists (to_var_values_seq p x2).
    split; last first. rewrite nth_iota; by autossr.
    rewrite f_apply_range_mapP. eexists. apply /andP. eauto.
  Qed.

  Theorem compose_relation_bot_PFuncMap :
    forall p (pf: PFuncMap p),
      compose_relation_PFuncMap pf (bot_PFuncMap p) = bot_PFuncMap p.
  Proof.
    move => p pf.
    rewrite /compose_relation_PFuncMap.
    apply val_inj. rewrite /bot_PFuncMap /=.
    eapply eq_from_nth. by rewrite size_map size_iota size_nseq.
    rewrite size_map size_iota => i Hi.
    rewrite (nth_map 0); last by rewrite size_iota.
    rewrite nth_nseq Hi. rewrite nth_iota => [ | //]. rewrite add0n.
    rewrite /map_to_pfunc.
    set val := f_extract_dimension_map _ _.
    set assumed := f_complement_set _.
    have Hval: val = f_empty_map _ _.
      rewrite /val. apply f_empty_map_uniq => [[x_in x_out]]. apply /negP.
      have Heq: (point_equality 1 x_out [::nth 0%Z x_out 0]). apply /allP. by case.
      rewrite_point_H Heq.
      rewrite f_extract_dimension_mapP => [[x_out']].
      rewrite f_apply_range_mapP => [[[x_mid] /andP [_]]].
      rewrite_to_var_values_map_equality p x_mid.
      rewrite_to_var_values_map_equality p x_out'.
      rewrite -pfuncmap_to_mapP => HIn.
      move: (gamma_bot_PFuncMap p (to_var_values_map p x_mid, to_var_values_map p x_out')).
      by move => /(_ HIn).
    rewrite Hval in assumed *.
    have ->: assumed = f_universe_set _.
      apply f_universe_set_uniq => x.
      rewrite /assumed. simpl_pfunc.
      apply /negP. rewrite f_get_domain_mapP => [[x_out]].
      rewrite f_subtract_mapP => /andP [Hempty].
      move: (f_empty_mapP (size (vars_in_program p)) 1 x x_out).
      by rewrite Hempty.
    have ->: f_map_witness (f_empty_map _ _) = f_empty_pw_aff _.
      move => n. apply f_empty_pw_aff_uniq => x.
      rewrite f_map_witness_none => x_out.
      by apply f_empty_mapP.
    by [].
  Unshelve.
    apply (constant_pfunc _ VTop).
  Qed.

  Theorem compose_relation_le_PFuncMapP :
    forall p (a a1 a2: PFuncMap p),
      le a1 a2 ->
      le (compose_relation_PFuncMap a a1) (compose_relation_PFuncMap a a2).
  Proof.
    move => p a a1 a2. rewrite /le /Included => Hle [x_in x_out].
    rewrite /In /gamma /= /gamma_PFuncMap /gamma_seq_PFuncMap => HIn.
    apply /allP => i Hiota. move: HIn => /allP /(_ i Hiota) /=.
    rewrite !(nth_map 0); try (rewrite size_iota; autossr).
    rewrite !map_to_pfuncP. move => [HIn | [x_out1 [x_out2 [Hne [HIn1 HIn2]]]]].
    - left. move: HIn => /f_extract_dimension_mapP [x_out' [/f_apply_range_mapP [x_mid /andP [Ha Ha1] Hnth]]].
      apply f_extract_dimension_mapP. exists x_out'. split; auto.
      apply f_apply_range_mapP. exists x_mid. apply /andP. split; auto.
      rewrite -!pfuncmap_to_mapP in Ha1 *.
      move => /(_ (to_var_values_map p x_mid, to_var_values_map p x_out')) in Hle.
      rewrite /In /gamma /= /gamma_PFuncMap /= in Hle.
      rewrite (gamma_seq_PFuncMap_equality _ _ _ (x_mid, x_out')) in Hle; simpl; auto.
      move => /(_ Ha1) in Hle.
      rewrite (gamma_seq_PFuncMap_equality _ _ _ (x_mid, x_out')) in Hle; simpl; auto.
    - right. exists x_out1. exists x_out2. split; auto.
      move: HIn1 => /f_extract_dimension_mapP [x_out1' [/f_apply_range_mapP [x_mid1 /andP [Ha1 Ha1'] Hnth1]]].
      move: HIn2 => /f_extract_dimension_mapP [x_out2' [/f_apply_range_mapP [x_mid2 /andP [Ha2 Ha2'] Hnth2]]].
      split.
      + apply /f_extract_dimension_mapP. exists x_out1'. split; auto.
        rewrite f_apply_range_mapP. exists x_mid1. apply /andP. split; auto.
        move => /(_ (to_var_values_map p x_mid1, to_var_values_map p x_out1')) in Hle.
        rewrite /In /gamma /= /gamma_PFuncMap /= in Hle.
        rewrite (gamma_seq_PFuncMap_equality _ _ _ (x_mid1, x_out1')) in Hle; simpl; eauto.
        rewrite -pfuncmap_to_mapP in Ha1'. move => /(_ Ha1') in Hle.
        rewrite (gamma_seq_PFuncMap_equality _ _ _ (x_mid1, x_out1')) in Hle; simpl; eauto.
          by rewrite -pfuncmap_to_mapP.
      + apply /f_extract_dimension_mapP. exists x_out2'. split; auto.
        rewrite f_apply_range_mapP. exists x_mid2. apply /andP. split; auto.
        move => /(_ (to_var_values_map p x_mid2, to_var_values_map p x_out2')) in Hle.
        rewrite /In /gamma /= /gamma_PFuncMap /= in Hle.
        rewrite (gamma_seq_PFuncMap_equality _ _ _ (x_mid2, x_out2')) in Hle; simpl; eauto.
        rewrite -pfuncmap_to_mapP in Ha2'. move => /(_ Ha2') in Hle.
        rewrite (gamma_seq_PFuncMap_equality _ _ _ (x_mid2, x_out2')) in Hle; simpl; eauto.
          by rewrite -pfuncmap_to_mapP.
  Qed.

  Theorem compose_relation_le_left_PFuncMapP :
    forall p (a1 a2 a: PFuncMap p),
      le a1 a2 ->
      le (compose_relation_PFuncMap a1 a) (compose_relation_PFuncMap a2 a).
  Proof.
    move => p a1 a2 a. rewrite /le /Included => Hle [x_in x_out].
    rewrite /In /gamma /= /gamma_PFuncMap /gamma_seq_PFuncMap => HIn.
    apply /allP => i Hiota. move: HIn => /allP /(_ i Hiota) /=.
    rewrite !(nth_map 0); try (rewrite size_iota; autossr).
    rewrite !map_to_pfuncP. move => [HIn | [x_out1 [x_out2 [Hne [HIn1 HIn2]]]]].
    - left. move: HIn => /f_extract_dimension_mapP [x_out' [/f_apply_range_mapP [x_mid /andP [Ha Ha1] Hnth]]].
      apply f_extract_dimension_mapP. exists x_out'. split; auto.
      apply f_apply_range_mapP. exists x_mid. apply /andP. split; auto.
      rewrite -!pfuncmap_to_mapP in Ha *.
      move => /(_ (x_in, to_var_values_map p x_mid)) in Hle.
      rewrite /In /gamma /= /gamma_PFuncMap /= in Hle.
      rewrite (gamma_seq_PFuncMap_equality _ _ _ (to_var_values_seq p x_in, x_mid)) in Hle; simpl; auto; last by apply point_equality_refl.
      move => /(_ Ha) in Hle.
      rewrite (gamma_seq_PFuncMap_equality _ _ _ (to_var_values_seq p x_in, x_mid)) in Hle; simpl; auto; last by apply point_equality_refl.
    - right. exists x_out1. exists x_out2. split; auto.
      move: HIn1 => /f_extract_dimension_mapP [x_out1' [/f_apply_range_mapP [x_mid1 /andP [Ha1 Ha1'] Hnth1]]].
      move: HIn2 => /f_extract_dimension_mapP [x_out2' [/f_apply_range_mapP [x_mid2 /andP [Ha2 Ha2'] Hnth2]]].
      split.
      + apply /f_extract_dimension_mapP. exists x_out1'. split; auto.
        rewrite f_apply_range_mapP. exists x_mid1. apply /andP. split; auto.
        move => /(_ (x_in, to_var_values_map p x_mid1)) in Hle.
        rewrite /In /gamma /= /gamma_PFuncMap /= in Hle.
        rewrite (gamma_seq_PFuncMap_equality _ _ _ (to_var_values_seq p x_in, x_mid1)) in Hle; simpl; auto; last by apply point_equality_refl.
        rewrite -pfuncmap_to_mapP in Ha1. move => /(_ Ha1) in Hle.
        rewrite (gamma_seq_PFuncMap_equality _ _ _ (to_var_values_seq p x_in, x_mid1)) in Hle; simpl; auto; last by apply point_equality_refl.
          by rewrite -pfuncmap_to_mapP.
      + apply /f_extract_dimension_mapP. exists x_out2'. split; auto.
        rewrite f_apply_range_mapP. exists x_mid2. apply /andP. split; auto.
        move => /(_ (x_in, to_var_values_map p x_mid2)) in Hle.
        rewrite /In /gamma /= /gamma_PFuncMap /= in Hle.
        rewrite (gamma_seq_PFuncMap_equality _ _ _ (to_var_values_seq p x_in, x_mid2)) in Hle; simpl; auto; last by apply point_equality_refl.
        rewrite -pfuncmap_to_mapP in Ha2. move => /(_ Ha2) in Hle.
        rewrite (gamma_seq_PFuncMap_equality _ _ _ (to_var_values_seq p x_in, x_mid2)) in Hle; simpl; auto; last by apply point_equality_refl.
          by rewrite -pfuncmap_to_mapP.
  Qed.

  Definition compose_transitive_closure_PFuncMap {p: Program} (pf1 pf2: PFuncMap p) :=
    let map1 := pfuncmap_to_map pf1 in
    let map2 := pfuncmap_to_map pf2 in
    map_to_pfuncmap (f_apply_range_map (f_transitive_closure_map map1) map2).

  Theorem compose_transitive_closure_id_PFuncMap :
    forall p (pf: PFuncMap p),
      le (compose_transitive_closure_PFuncMap pf pf) (compose_transitive_closure_PFuncMap pf (id_relation_PFuncMap p)).
  Proof.
    move => p pf.
    rewrite /compose_transitive_closure_PFuncMap.
    apply map_to_pfuncmap_le.
    eapply f_is_subset_map_trans. apply f_transitive_closure_map_ge_compose.
    apply f_is_subset_mapP => x y HIn.
    apply f_apply_range_mapP. exists y. apply /andP. split; auto.
    rewrite -pfuncmap_to_mapP.
    move: (id_relation_PFuncMapP p (to_var_values_map p y)).
    rewrite /In /gamma_PFuncMap /= => Hgamma.
    erewrite gamma_seq_PFuncMap_equality; eauto; simpl; auto.
  Qed.

  Theorem compose_transitive_closure_ge_id_PFuncMap :
    forall p (pf: PFuncMap p),
      le (id_relation_PFuncMap p) (compose_transitive_closure_PFuncMap pf (id_relation_PFuncMap p)).
  Proof.
    move => p pf [x y] HIn.
    apply id_relation_PFuncMap_precise in HIn.
    rewrite /compose_transitive_closure_PFuncMap.
    apply map_to_pfuncmapP.
    apply f_apply_range_mapP. exists (to_var_values_seq p y).
    apply /andP. rewrite_point_H HIn.
    split.
    - move :f_transitive_closure_map_ge_id. setoid_rewrite f_is_subset_mapP. apply. auto_pfunc. apply point_equality_refl.
    - rewrite -pfuncmap_to_mapP. by move: (id_relation_PFuncMapP p y).
  Qed.

  Theorem compose_transitive_closure_bot_PFuncMap :
    forall p pf, @compose_transitive_closure_PFuncMap p pf (bot_PFuncMap p) = (bot_PFuncMap p).
  Proof.
    move => p pf.
    rewrite /compose_transitive_closure_PFuncMap.
    rewrite /pfuncmap_to_map. simplssr.
    rewrite f_apply_range_map_empty.
    rewrite /map_to_pfuncmap /bot_PFuncMap.
    apply val_inj => /=.
    eapply eq_from_nth. by rewrite size_nseq size_map size_iota.
    rewrite size_map size_iota => i Hi.
    rewrite (nth_map 0); last by rewrite size_iota.
    rewrite nth_nseq Hi.
    rewrite /map_to_pfunc.
    set val := f_map_witness _.
    set assumed := f_complement_set _.
    have Hval: (val = f_empty_pw_aff _).
      apply f_empty_pw_aff_uniq => x.
      rewrite /val. rewrite f_map_witness_none => x_out.
      apply /negP.
      have Hx_out: point_equality 1 x_out [::nth 0%Z x_out 0]. apply /allP. case => //.
      rewrite_point_H Hx_out.
      rewrite f_extract_dimension_mapP => [[x_out' [HIn _]]].
      by move: (f_empty_mapP (size (vars_in_program p)) (size (vars_in_program p)) x x_out') => /negP.
    rewrite Hval.
    have Hassumed: (assumed = f_universe_set _).
      apply f_universe_set_uniq => x. rewrite /assumed.
      simpl_pfunc. apply /negP. rewrite f_get_domain_mapP => [[x_out]].
      simpl_pfunc. move => /andP [Hextract Heval].
      have Hx_out: point_equality 1 x_out [::nth 0%Z x_out 0]. apply /allP. case => //.
      rewrite_point_in Hextract x_out [:: nth 0%Z x_out 0].
      move => /f_extract_dimension_mapP in Hextract.
      move: Hextract => [x_out' [Hempty _]].
      move: (f_empty_mapP (size (vars_in_program p)) (size (vars_in_program p)) x x_out').
      autossr.
    by rewrite Hassumed.
  Unshelve.
    apply constant_pfunc. apply VTop.
  Qed.

  Theorem compose_transitive_closure_le_PFuncMap :
    forall p (pf pf1 pf2: PFuncMap p),
      le pf1 pf2 ->
      le (compose_transitive_closure_PFuncMap pf pf1) (compose_transitive_closure_PFuncMap pf pf2).
  Proof.
    move => p pf pf1 pf2 Hle [x_in x_out].
    apply (map_to_pfuncmap_le).
    apply f_apply_range_map_le.
    apply f_is_subset_mapP => x y.
    rewrite_to_var_values_map_equality p x.
    rewrite_to_var_values_map_equality p y.
    rewrite -!pfuncmap_to_mapP => HIn.
    rewrite /le /Included in Hle.
    by apply (Hle (to_var_values_map p x, to_var_values_map p y)).
  Qed.

  Instance adom_relational_PFuncMap (p: Program) : adom_relational (adom_pmap p) :=
    {
      id_relation := (id_relation_PFuncMap p);
      id_relation_spec := (id_relation_PFuncMapP p);

      compose_relation := compose_relation_PFuncMap;
      compose_relation_spec := (compose_relation_PFuncMapP p);

      compose_bot := (compose_relation_bot_PFuncMap p);
      compose_relation_le := (compose_relation_le_PFuncMapP p);
      compose_relation_quotient_right := (compose_relation_le_PFuncMapP p);
      compose_relation_quotient_left := (compose_relation_le_left_PFuncMapP p);

      compose_transitive_closure := compose_transitive_closure_PFuncMap;
      compose_transitive_closure_id := (compose_transitive_closure_id_PFuncMap p);
      compose_transitive_closure_ge_id := (compose_transitive_closure_ge_id_PFuncMap p);
      compose_transitive_closure_bot := (compose_transitive_closure_bot_PFuncMap p);
      compose_transitive_closure_le := (compose_transitive_closure_le_PFuncMap p);
    }.

End PFuncMap.
