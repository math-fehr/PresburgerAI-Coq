From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat.
From PolyAI Require Export RelationalTransferFunction LSSA Tactic.
From Coq Require Import Lists.List.
From mathcomp.ssreflect Require Import seq.

Require Import Lia.

Local Open Scope string_scope.

Section AbstractInterpreter.

  Ltac simpl_ai :=
    repeat (autorewrite with airw; simpl_map; simplssr).
  Ltac auto_ai := intros ; simpl_ai ; autossr.

  Context {ab: eqType}
          {p: Program}
          {ad: adom (prod_eqType RegisterMap RegisterMap) ab p}
          {adr: adom_relational ad}
          (tf: transfer_function_relational adr p).

  (* Associate for every control location an abstract state *)
  Notation ASValues := (@total_map_d bbid_eqType (@total_map_d nat_eqType ab bot) (_ |-> bot)).
  Notation ASEdges := (@total_map_d bbid_eqType (@total_map_d bbid_eqType ab bot) (_ |-> bot)).
  Notation ASEdgesP := (@partial_map bbid_eqType (@total_map_d bbid_eqType ab bot)).
  Definition AS : Type := ASValues * ASEdges.

  (* Properties we want at the end of our analysis *)
  Definition inst_fixpoint (stateV: ASValues) (bb_id: bbid) (pos: nat) :=
    forall bb, p bb_id = Some bb ->
          forall inst, nth_error bb.1.2 pos = Some inst ->
                  le (transfer_inst inst (stateV bb_id pos)) (stateV bb_id (S pos)).

  Definition inst_fixpoint' (stateV: ASValues) (bb_id: bbid) (pos: nat) :=
    forall bb, p bb_id = Some bb ->
          forall inst, nth_error bb.1.2 pos = Some inst ->
                  forall R R', reachable_states p R (bb_id, pos, R') ->
                          Ensembles.In _ (gamma (stateV bb_id pos)) (R, R') ->
                          forall R'', inst_step inst R' R'' ->
                                 Ensembles.In _ (gamma (stateV bb_id (S pos))) (R, R'').

  Definition term_fixpoint (state: AS) (bb_id: bbid) :=
    forall bb, p bb_id = Some bb ->
          forall abbbid, (abbbid \in (transfer_term bb.2 (state.1 bb_id (length bb.1.2)))) ->
                    le abbbid.1 (state.2 bb_id abbbid.2).

  Definition term_fixpoint' (state: AS) (bb_id: bbid) :=
    forall bb, p bb_id = Some bb ->
          let pos := size bb.1.2 in
          forall R R', reachable_states p R (bb_id, pos, R') ->
                  Ensembles.In _ (gamma (state.1 bb_id pos)) (R, R') ->
                  forall bb_id' R'', term_step p bb.2 R' (bb_id', R'') ->
                                Ensembles.In _ (gamma (state.2 bb_id bb_id')) (R, R'').

  Definition edge_fixpoint (state: AS) (bb_id: bbid) :=
    forall in_id, le (state.2 in_id bb_id) (state.1 bb_id 0).

  Definition edge_fixpoint' (state: AS) (bb_id_out: bbid) :=
    forall bb_in bb_id_in, p bb_id_in = Some bb_in ->
          let pos := size bb_in.1.2 in
          forall R R', reachable_states p R (bb_id_in, pos, R') ->
                  Ensembles.In _ (gamma (state.2 bb_id_in bb_id_out)) (R, R') ->
                  Ensembles.In _ (gamma (state.1 bb_id_out 0)) (R, R').

  Definition edges_invariant_some (stateE: ASEdges) :=
    forall in_id in_bb, p in_id = Some in_bb ->
      forall out_id, out_id \notin term_successors in_bb.2 ->
                stateE in_id out_id = bot.

  Definition edges_invariant_none (stateE: ASEdges) :=
    forall in_id, p in_id = None ->
             forall out_id, stateE in_id out_id = bot.

  Definition edges_invariant (stateE: ASEdges) :=
    edges_invariant_some stateE /\ edges_invariant_none stateE.

  (*   _           _   _ _     _    *)
  (*  (_)_ __  ___| |_| (_)___| |_  *)
  (*  | | '_ \/ __| __| | / __| __| *)
  (*  | | | | \__ \ |_| | \__ \ |_  *)
  (*  |_|_| |_|___/\__|_|_|___/\__| *)

  (* interpretation of a list of instruction *)
  Fixpoint abstract_interpret_inst_list (l: list Inst) (bb_id: bbid) (pos: nat) (stateV: ASValues) :=
    match l with
    | nil => stateV
    | inst::l' => let new_ab := transfer_inst inst (stateV bb_id pos) in
                let new_state := (bb_id |-> (S pos |-> new_ab; stateV bb_id); stateV) in
                abstract_interpret_inst_list l' bb_id (S pos) new_state
    end.

  Theorem abstract_interpret_inst_list_spec (bb: BasicBlock) (bb_id: bbid):
    Some bb = p bb_id ->
    forall (l: list Inst) pos, (forall n, nth_error l n = nth_error bb.1.2 (n + pos)) ->
      forall stateV, (forall n', n' < pos -> inst_fixpoint stateV bb_id n') ->
        forall n'', inst_fixpoint (abstract_interpret_inst_list l bb_id pos stateV) bb_id n''.
  Proof.
    move => Hbb.
    elim => [ /= pos Hnth stateV Hfixpoint n''| inst l Hind pos Hnth stateV Hfixpoint n'' /=].
    - case_eq (n'' < pos) => [/Hfixpoint // | /negb_true_iff Hge].
      rewrite /inst_fixpoint -Hbb => bb0 [<-] inst.
      move: (Hnth (n'' - pos)). rewrite -leqNgt in Hge. rewrite subnK => [<- | //].
      by case (n'' - pos).
    - apply Hind => [n | n' Hn'ltpos1]. by rewrite addnS; apply (Hnth n.+1).
      case (@idP (n' < pos)) => [Heqn'pos bb0 Hbb0 inst0 Hinst0 | /negP Hn'gepos bb0 Hbb0 inst0 Hinst0].
      + simpl_map. by eapply Hfixpoint; eauto.
      + simpl_map.
        have Heq : (n' = pos) by liassr. subst.
        move: Hbb0 (Hnth 0) => /=.
        rewrite -Hbb => [[->]].
          by rewrite add0n Hinst0 => [[->]].
  Qed.

  Theorem abstract_interpret_inst_listP (bb: BasicBlock) (bb_id: bbid) :
    p bb_id = Some bb ->
    forall (l: seq Inst) pos, (forall n, nth_error l n = nth_error bb.1.2 (n + pos)) ->
      forall stateV, (forall n', n' < pos -> inst_fixpoint' stateV bb_id n') ->
        forall n'', inst_fixpoint' (abstract_interpret_inst_list l bb_id pos stateV) bb_id n''.
  Proof.
    move => Hbb. elim.
    - move => pos Hnth stateV Hfixpoint n''.
      case Hn''pos: (n'' < pos). by autossr.
      move => bb_same Hbb_same inst Hinst. exfalso. bigsubst.
      move => /negb_true_iff in Hn''pos. rewrite -leqNgt in Hn''pos.
      move: (Hnth (n'' - pos)). rewrite subnK => [ | //]. rewrite /= Hinst.
        by case (n'' - pos).
    - move => inst l Hind pos Hnth stateV Hfixpoint n''.
      apply Hind => [n | n' Hn'ltpos1]. by rewrite addnS; apply (Hnth n.+1).
      case Hn'pos: (n' < pos) => /=.
      + have Hn'posne: (pos.+1 != n'.+1). rewrite eqSS neq_ltn Hn'pos. by autossr.
        rewrite /inst_fixpoint'. simpl_map.
          by apply Hfixpoint.
      + have Heq : (n' = pos). rewrite leq_eqVlt ltnS Hn'pos orb_false_r eqSS in Hn'ltpos1. autossr.
        rewrite /inst_fixpoint'. simpl_map.
        move => bb0 Hbb0 inst0 Hinst0 R R' Hreachable HIn R'' Hstep.
        bigsubst. move: (Hnth 0) => /=. rewrite add0n Hinst0. case => ->.
          by eapply transfer_inst_sound; eauto.
  Qed.

  Theorem abstract_interpret_inst_list_0_unchanged (l: list Inst) (bb_id bb_id': bbid) (pos: nat) (stateV: ASValues) :
    (abstract_interpret_inst_list l bb_id pos stateV) bb_id' 0 = stateV bb_id' 0.
  Proof.
    elim: l stateV pos => [ // | i l Hind stateV pos]. move: Hind.
    case (bb_id' =P bb_id) => [-> | Hne] ->; by auto_map.
  Qed.

  Theorem abstract_interpret_inst_list_bb_unchanged (l: list Inst) (bb_id: bbid) :
    forall bb_id', bb_id != bb_id' ->
              forall state pos n, (abstract_interpret_inst_list l bb_id pos state) bb_id' n = state bb_id' n.
  Proof.
    move => bb_id' Hbb_ne.
    elim: l => [ // | i l Hind state pos n].
    rewrite Hind. auto_map.
  Qed.

  Hint Rewrite abstract_interpret_inst_list_0_unchanged abstract_interpret_inst_list_bb_unchanged using by first [liassr | autossr ] : airw.

  (*  _                               _             *)
  (* | |_ ___ _ __ _ __ ___   ___  __| | __ _  ___  *)
  (* | __/ _ \ '__| '_ ` _ \ / _ \/ _` |/ _` |/ _ \ *)
  (* | ||  __/ |  | | | | | |  __/ (_| | (_| |  __/ *)
  (*  \__\___|_|  |_| |_| |_|\___|\__,_|\__, |\___| *)
  (*                                    |___/       *)

  (* Interpretation of a terminator *)
  Definition abstract_interpret_term_join_edges (stateE: ASEdges) (bb_id: bbid) (edges: list (ab * bbid)) :=
    fold_right (fun (abid: (ab * bbid)) state =>
                  let (ab, out_id) := abid in (bb_id |-> (out_id |-> join ab (state bb_id out_id); state bb_id); state)
               ) stateE edges.

  Theorem abstract_interpret_term_join_edges_spec (in_id: bbid) (stateE: ASEdges) (edges: list (ab * bbid)):
    forall a out_id, (a, out_id) \in edges ->
                le a (abstract_interpret_term_join_edges stateE in_id edges in_id out_id).
  Proof.
    elim edges => [ // | [a out_id] l Hind a0 out_id0].
    simpl_ai.
    move => /orP[ /eqP [-> ->] | HIn].
    + by auto_map.
    + apply Hind in HIn.
      by case (out_id =P out_id0) => [ -> | /eqP Hne ]; auto_map.
  Qed.

  Hint Resolve abstract_interpret_term_join_edges_spec : core.

  Theorem abstract_interpret_term_join_edges_out_unchanged (in_id out_id: bbid) (stateE: ASEdges) (edges: list (ab * bbid)):
    (forall a , (a, out_id) \notin edges) ->
    forall id, (abstract_interpret_term_join_edges stateE in_id edges id out_id) = stateE id out_id.
  Proof.
    elim edges => [ // | /= [a id] l Hind HnotIn id0].
    move: (HnotIn a).
    rewrite in_cons => /norP [Hne HanotIn].
    have: (is_true (id != out_id)). apply /negP => /eqP Heq. by rewrite Heq eq_refl in Hne.
    move => Hneid.
    by case (in_id =P id0) => [ <- | /eqP Hneid0 ]; simpl_ai; apply Hind => a0; move: (HnotIn a0); autossr.
  Qed.

  Theorem abstract_interpret_term_join_edges_in_unchanged (id in_id: bbid) (stateE: ASEdges) (edges: list (ab * bbid)):
    in_id != id ->
    forall out_id, (abstract_interpret_term_join_edges stateE id edges in_id out_id) = stateE in_id out_id.
  Proof.
    move => Hne out_id.
    elim edges => [ // | [a out_id0] l Hind ].
    auto_ai.
  Qed.

  Hint Rewrite abstract_interpret_term_join_edges_out_unchanged abstract_interpret_term_join_edges_in_unchanged using by first [liassr | autossr ] : airw.

  (*  _                       *)
  (* | |_ ___ _ __ _ __ ___   *)
  (* | __/ _ \ '__| '_ ` _ \  *)
  (* | ||  __/ |  | | | | | | *)
  (*  \__\___|_|  |_| |_| |_| *)

  Definition abstract_interpret_term (bb: BasicBlock) (bb_id: bbid) (state: AS) :=
    let pos := length bb.1.2 in
    let new_edges := transfer_term bb.2 (state.1 bb_id pos) in
    abstract_interpret_term_join_edges state.2 bb_id new_edges.

  Theorem abstract_interpret_term_spec (bb: BasicBlock) (bb_id: bbid) (state: AS):
    p bb_id = Some bb ->
    term_fixpoint (state.1, (abstract_interpret_term bb bb_id state)) bb_id.
  Proof.
    move => Hbb. rewrite /term_fixpoint Hbb => bb0 [<-] [a out_id].
    rewrite /abstract_interpret_term /=.
    by auto.
  Qed.

  Theorem abstract_interpret_termP (bb: BasicBlock) (bb_id: bbid) (state: AS) :
    p bb_id = Some bb ->
    term_fixpoint' (state.1, (abstract_interpret_term bb bb_id state)) bb_id.
  Proof.
    move: state => [stateV stateE].
    move => Hbb /= bb0 Hbb0 pos R R' Hreachable_states /= HIn bb_id' R'' Hterm.
    bigsubst. rewrite /abstract_interpret_term /=.
    pose proof transfer_term_sound.
    move => /(_ _ _ _ _ Hterm _ _ HIn) in H.
    case: H => [a' [Hintransfer HIna']].
      by eapply abstract_interpret_term_join_edges_spec; eauto.
  Qed.

  Hint Resolve abstract_interpret_term_spec : core.

  Lemma abstract_interpret_term_bb_edge_out_unchanged (bb_id: bbid) (bb: BasicBlock):
    p bb_id = Some bb ->
    forall bb_id', bb_id' \notin (term_successors bb.2) ->
              forall state bb_id'', (abstract_interpret_term bb bb_id state) bb_id'' bb_id' = state.2 bb_id'' bb_id'.
  Proof.
    move => Hbb bb_id' /negP Hbb_not_term state bb_id''.
    rewrite /abstract_interpret_term.
    apply abstract_interpret_term_join_edges_out_unchanged => a.
    apply /negP => Hbb_not_transfer_term.
    apply Hbb_not_term.
    eapply transfer_term_only_successors; eauto.
  Qed.

  Hint Rewrite abstract_interpret_term_bb_edge_out_unchanged using first [ liassr ; autossr ] : airw.

  Fixpoint join_edges_cond_aux (stateE: ASEdges) (seen: seq bbid) (cond: bbid -> bool) (x: bbid) :=
    match stateE with
    | TDDefault => bot
    | TDUpdate stateE' k v =>
      if (k \in seen) && (cond k) then
        join_edges_cond_aux stateE' seen cond x
      else
        join (v x) (join_edges_cond_aux stateE' (k::seen) cond x)
    end.

  Theorem join_edges_cond_aux_spec (stateE: ASEdges) (seen: seq bbid) (cond: bbid -> bool) (x y: bbid):
    cond y ->
    y \notin seen ->
    le (stateE y x) (join_edges_cond_aux stateE seen cond x).
  Proof.
    elim: stateE seen => [ seen Hcond // | stateE' Hind k v seen Hcond Hnotin ].
    case (k =P y) => [ -> | /eqP Hne ]. by auto_map.
    simpl_map.
    case: (k \in seen) => /=.
    - case: (cond k). by autossr.
      eapply AbstractDomain.le_trans; last first.
      + by apply join_sound_r.
      + apply Hind => //.
        by autossr.
    - eapply AbstractDomain.le_trans; last first.
      + by apply join_sound_r.
      + apply Hind; by autossr.
  Qed.

  Definition join_edges_cond (stateE: ASEdges) (cond: bbid -> bool) (bb_id: bbid) :=
    join_edges_cond_aux stateE [::] cond bb_id.

  Theorem join_edges_cond_spec (stateE: ASEdges) (cond: bbid -> bool) (bb_id bb_id': bbid) :
    cond bb_id' ->
    le (stateE bb_id' bb_id) (join_edges_cond stateE cond bb_id).
  Proof.
    move => Hcond.
      by apply join_edges_cond_aux_spec.
  Qed.

  Definition join_edges (stateE: ASEdges) (bb_id: bbid) :=
    join_edges_cond_aux stateE [::] (fun _ => true) bb_id.

  Theorem join_edges_spec (stateE: ASEdges) (bb_id bb_id': bbid) :
    le (stateE bb_id' bb_id) (join_edges stateE bb_id).
  Proof.
      by apply join_edges_cond_aux_spec.
  Qed.

  Hint Resolve join_edges_cond_spec join_edges_spec : core.

  Theorem abstract_interpret_term_edges_invariant_kept (bb_id: bbid) (bb: BasicBlock) (state: AS):
    p bb_id = Some bb ->
    edges_invariant state.2 ->
    edges_invariant (abstract_interpret_term bb bb_id state).
  Proof.
    move => Hbb [Hinvariant_some Hinvariant_none].
    split => [ in_id in_bb Hinbb out_id Hnotinsucc | ].
    - move => /(_ in_id in_bb Hinbb out_id Hnotinsucc) in Hinvariant_some.
      rewrite /abstract_interpret_term.
      case (bb_id =P in_id) => [Heq | Hbb_ne ].
      + rewrite Heq abstract_interpret_term_join_edges_out_unchanged => [ // | a ].
        apply /negP => Hin. move => /negP in Hnotinsucc. apply Hnotinsucc.
        eapply transfer_term_only_successors.
        bigsubst. by eauto.
      + auto_ai.
    - move => in_id Hin_id out_id.
      move => /(_ in_id Hin_id out_id) in Hinvariant_none.
      rewrite /abstract_interpret_term.
      have Hne : (bb_id != in_id). apply /eqP. intro. bigsubst. by rewrite Hbb in Hin_id.
      by simpl_ai.
  Qed.

  Hint Resolve abstract_interpret_term_edges_invariant_kept : core.

  (*  ____            _      ____  _            _     *)
  (* | __ )  __ _ ___(_) ___| __ )| | ___   ___| | __ *)
  (* |  _ \ / _` / __| |/ __|  _ \| |/ _ \ / __| |/ / *)
  (* | |_) | (_| \__ \ | (__| |_) | | (_) | (__|   <  *)
  (* |____/ \__,_|___/_|\___|____/|_|\___/ \___|_|\_\ *)

  (* Interpretation of a basic block *)
  Definition abstract_interpret_bb (bb: BasicBlock) (bb_id: bbid) (state: AS) :=
    let stateV1 := ( bb_id |-> (0 |-> join (state.1 bb_id 0) (join_edges state.2 bb_id); state.1 bb_id) ; state.1) in
    let stateV2 := abstract_interpret_inst_list bb.1.2 bb_id 0 stateV1 in
    let stateE' := abstract_interpret_term bb bb_id (stateV2, state.2) in
    (stateV2, stateE').

  Theorem abstract_interpret_bb_spec_term (bb: BasicBlock) (bb_id: bbid) (state: AS):
    p bb_id = Some bb ->
    term_fixpoint (abstract_interpret_bb bb bb_id state) bb_id.
  Proof.
    move => Hbb.
    rewrite /abstract_interpret_bb.
    set state'Values := (abstract_interpret_inst_list _ _ _ _).
    set state' := (state'Values, state.2).
    have H : state'Values = (state').1. auto.
    rewrite H.
    by apply abstract_interpret_term_spec.
  Qed.

  Theorem abstract_interpret_bb_spec_inst (bb: BasicBlock) (bb_id: bbid) (state: AS):
    p bb_id = Some bb ->
    (forall n, inst_fixpoint (abstract_interpret_bb bb bb_id state).1 bb_id n).
  Proof.
    move => /= Hbb n.
    eapply abstract_interpret_inst_list_spec => [  | n0 | // ].
    - by eauto.
    - by rewrite addn0.
  Qed.

  Theorem abstract_interpret_bb_spec_edge (bb: BasicBlock) (bb_id: bbid) (state: AS):
    Some bb = p bb_id ->
    bb_id \notin (term_successors bb.2) ->
    edge_fixpoint (abstract_interpret_bb bb bb_id state) bb_id.
  Proof.
    move => Hbb Hotin /=.
    rewrite /edge_fixpoint => in_id.
    rewrite abstract_interpret_term_bb_edge_out_unchanged; auto.
    rewrite abstract_interpret_inst_list_0_unchanged.
    by auto_map.
  Qed.

  Hint Resolve abstract_interpret_bb_spec_term abstract_interpret_bb_spec_inst abstract_interpret_bb_spec_edge : core.

  Theorem abstract_interpret_bb_edge_in_unchanged (bb: BasicBlock) (bb_id in_id out_id: bbid) (state: AS):
    Some bb = p bb_id ->
    in_id != bb_id ->
    (abstract_interpret_bb bb bb_id state).2 in_id out_id = state.2 in_id out_id.
  Proof.
    move => Hbb Hbbne /=.
    rewrite /abstract_interpret_term /=.
      by auto_ai.
  Qed.

  Theorem abstract_interpret_bb_value_unchanged (bb: BasicBlock) (bb_id bb_id': bbid) (state: AS):
    Some bb = p bb_id ->
    bb_id != bb_id' ->
    forall pos, (abstract_interpret_bb bb bb_id state).1 bb_id' pos = state.1 bb_id' pos.
  Proof.
    move => Hbb Hbbne pos /=.
      by auto_ai.
  Qed.

  Theorem abstract_interpret_bb_edges_invariant_kept (bb_id: bbid) (bb: BasicBlock) (state: AS):
    p bb_id = Some bb ->
    edges_invariant state.2 ->
    edges_invariant (abstract_interpret_bb bb bb_id state).2.
  Proof.
    by auto_map.
  Qed.

  Hint Rewrite abstract_interpret_bb_edge_in_unchanged abstract_interpret_bb_value_unchanged using first [ liassr ; autossr ] : airw.
  Hint Resolve abstract_interpret_bb_edges_invariant_kept : core.

  (*  _                       *)
  (* | |    ___   ___  _ __   *)
  (* | |   / _ \ / _ \| '_ \  *)
  (* | |__| (_) | (_) | |_) | *)
  (* |_____\___/ \___/| .__/  *)
  (*                  |_|     *)

  Definition set_input_to_identity (state: AS) (entry_id: bbid) :=
    ((entry_id |-> (0 |-> id_relation ; state.1 entry_id); state.1), state.2).

  Program Definition compose_relation_in_program_edges (ps: ProgramStructure) (stateE: ASEdges) (relation: ab) :=
    td_pointwise_un_op_in_seq stateE (fun m => td_pointwise_un_op m (compose_relation relation)) (bbs_in_program ps).

  Theorem compose_relation_in_program_edges_spec (ps: ProgramStructure) (stateE: ASEdges) (relation: ab) (in_id out_id: bbid) :
    compose_relation_in_program_edges ps stateE relation in_id out_id =
    if (in_id \in bbs_in_program ps) then compose_relation relation (stateE in_id out_id) else stateE in_id out_id.
  Proof.
    rewrite td_pointwise_un_op_in_seq_spec.
    case: (in_id \in bbs_in_program ps) => [ /= | // ].
    rewrite /eq_rect. case (compose_relation_in_program_edges_obligation_1 relation).
    by auto_ai.
  Qed.

  Hint Rewrite compose_relation_in_program_edges_spec using first [ liassr ; autossr ] : airw.

  Theorem compose_relation_in_program_edges_edges_invariant_kept (ps: ProgramStructure) (stateE: ASEdges):
    edges_invariant stateE ->
    forall relation, edges_invariant (compose_relation_in_program_edges ps stateE relation).
  Proof.
    move => [Hinvariant_some Hinvariant_none] relation.
    split => [ in_id in_bb Hin_bb out_id Houtnotsucc | in_id Hin_bb out_id].
    - move => /(_ in_id in_bb Hin_bb out_id Houtnotsucc) in Hinvariant_some.
      simpl_ai.
      case: (in_id \in bbs_in_program ps) => //.
        by rewrite Hinvariant_some.
    - move => /(_ in_id Hin_bb out_id) in Hinvariant_none.
      simpl_ai.
      rewrite Hinvariant_none. simpl_ai.
      by case (_ \in _).
  Qed.

  Hint Resolve compose_relation_in_program_edges_edges_invariant_kept : core.

  Program Definition compose_relation_in_program_values (ps: ProgramStructure) (stateV: ASValues) (relation: ab) :=
    td_pointwise_un_op_in_seq stateV (fun m => td_pointwise_un_op m (compose_relation relation)) (bbs_in_program ps).

  Theorem compose_relation_in_program_values_spec (ps: ProgramStructure) (stateV: ASValues) (relation: ab) (bb_id: bbid) (pos: nat) :
    compose_relation_in_program_values ps stateV relation bb_id pos =
    if (bb_id \in bbs_in_program ps) then compose_relation relation (stateV bb_id pos) else stateV bb_id pos.
  Proof.
    rewrite td_pointwise_un_op_in_seq_spec.
    case: (bb_id \in bbs_in_program ps) => [ | // ].
    rewrite /eq_rect. case (compose_relation_in_program_values_obligation_1 relation).
    by auto_ai.
  Qed.

  Hint Rewrite compose_relation_in_program_values_spec : airw.

  Definition compose_relation_in_program (ps: ProgramStructure) (state: AS) (relation: ab) :=
    let stateV := compose_relation_in_program_values ps state.1 relation in
    let stateE := compose_relation_in_program_edges ps state.2 relation in
    (stateV, stateE).

  Definition compute_loop_effect (ps: ProgramStructure) (stateE: ASEdges) (header_id: bbid) :=
    let loop_sym_effect := join_edges_cond stateE (fun bb_id => bb_id \in (bbs_in_program ps)) header_id in
    transitive_closure loop_sym_effect.

  Definition compute_loop_effect_with_enter (ps: ProgramStructure) (stateE: ASEdges) (header_id: bbid) :=
    let loop_effect := compute_loop_effect ps stateE header_id in
    let entering_loop := join_edges_cond stateE (fun bb_id => bb_id \notin (bbs_in_program ps)) header_id in
    compose_relation entering_loop loop_effect.

  (*  ____                                       *)
  (* |  _ \ _ __ ___   __ _ _ __ __ _ _ __ ___   *)
  (* | |_) | '__/ _ \ / _` | '__/ _` | '_ ` _ \  *)
  (* |  __/| | | (_) | (_| | | | (_| | | | | | | *)
  (* |_|   |_|  \___/ \__, |_|  \__,_|_| |_| |_| *)
  (*                  |___/                      *)

  Fixpoint abstract_interpret_program (ps: ProgramStructure) (state: AS) :=
    match ps with
    | BB bb_id =>
      match p bb_id with
      | Some bb => abstract_interpret_bb bb bb_id state
      | None => state
      end
    | DAG ps1 ps2 =>
      abstract_interpret_program ps2 (abstract_interpret_program ps1 state)
    | Loop header_id body =>
      match p header_id with
      | None => state
      | Some header =>
        let state0 := set_input_to_identity state header_id in
        let state1 := abstract_interpret_bb header header_id state0 in
        let state2 := abstract_interpret_program body state1 in
        let loop_effect_with_enter := compute_loop_effect_with_enter ps state2.2 header_id in
        compose_relation_in_program ps state2 loop_effect_with_enter
      end
    end.

  Theorem abstract_interpret_program_edges_invariant_kept (ps: ProgramStructure) (state: AS):
    structure_sound p ps ->
    edges_invariant state.2 ->
    edges_invariant (abstract_interpret_program ps state).2.
  Proof.
    elim: ps state.
    - move => header body Hind state /= /andP[/andP[_ Hsound] _] Hinvariant /=.
      by case Hheader: (p header); auto_ai.
    - move => ps1 Hind1 ps2 Hind2 state /= /andP[/andP[_ Hsound1] Hsound2].
      by auto.
    - move => state bb_id /= Hsound Hinvariant.
      case_eq (p state) => [ bb Hbb | // ].
      by auto.
  Qed.

  Hint Resolve abstract_interpret_program_edges_invariant_kept : core.

  Theorem abstract_interpret_program_edge_in_unchanged (ps: ProgramStructure) (in_id out_id: bbid) (state: AS):
    structure_sound p ps ->
    in_id \notin (bbs_in_program ps) ->
    (abstract_interpret_program ps state).2 in_id out_id = state.2 in_id out_id.
  Proof.
    elim: ps state.
    - move => header_id body Hind state /= /andP [/andP[_ Hsound] _] Hnotin.
      case Hheader: (p header_id) => [ header_bb | // ].
      simpl_ai.
      rewrite Hind; autossr.
      by rewrite abstract_interpret_bb_edge_in_unchanged; autossr.
    - move => ps1 Hind1 ps2 Hind2 state /= /andP[/andP[_ Hsound1] Hsound2].
      rewrite mem_cat => /norP [Hnotin1 Hnotin2].
        by rewrite Hind2; auto.
    - move => bb_id state /=.
      case Hbb: (p bb_id) => [[[inputs insts] term] | // ] Hnotinterm Hnotin.
      simpl_ai.
      by rewrite abstract_interpret_bb_edge_in_unchanged; auto.
  Qed.

  Hint Rewrite abstract_interpret_program_edge_in_unchanged using by first [liassr | autossr ] : airw.

  Theorem abstract_interpret_program_value_unchanged (ps: ProgramStructure) (in_id: bbid) (state: AS):
    structure_sound p ps ->
    in_id \notin (bbs_in_program ps) ->
    forall pos, (abstract_interpret_program ps state).1 in_id pos = state.1 in_id pos.
  Proof.
    elim: ps state.
    - move => header_id body Hind state /= /andP[/andP[_ Hsound] _] /negb_true_iff Hnotin pos.
      case H: (p header_id) => //=.
      rewrite compose_relation_in_program_values_spec Hnotin /=.
      move: Hnotin. rewrite in_cons eq_sym => /orb_false_iff[/negb_true_iff Hne /negb_true_iff Hnotin].
      by rewrite Hind; auto_ai.
    - move => ps1 Hind1 ps2 Hind2 state /= /andP[/andP[_ Hsound1] Hsound2].
      rewrite /= mem_cat => /norP[Hnotin1 Hnotin2] pos.
      rewrite Hind2; auto.
    - move => bb_id state /=. case_eq (p bb_id); auto => bb Hbb _.
      rewrite mem_seq1 => Hne pos.
      by auto_ai.
  Qed.

  Hint Rewrite abstract_interpret_program_value_unchanged using by first [liassr | autossr ] : airw.

  Lemma abstract_interpret_program_term_fixpoint_kept (ps: ProgramStructure):
    structure_sound p ps ->
    forall bb_id, (bb_id \notin (bbs_in_program ps)) ->
             forall state, term_fixpoint state bb_id ->
                      term_fixpoint (abstract_interpret_program ps state) bb_id.
  Proof.
    move => Hsound bb_id Hbbnotin state Hterm bb Hbb [a out_id].
    move: Hterm => /(_ bb Hbb (a, out_id)).
    by simpl_ai.
  Qed.

  Theorem abstract_interpret_program_spec_term (ps: ProgramStructure):
    structure_sound p ps ->
    forall bb_id, (bb_id \in (bbs_in_program ps)) ->
             forall state, term_fixpoint (abstract_interpret_program ps state) bb_id.
  Proof.
    elim: ps.
    - move => header body Hind /= /andP[/andP[/andP[Hheadernotinbody _] Hsoundbody] HheaderSome] bb_id Hin state. move: HheaderSome.
      case Hheader: (p header) => [ bb | //] _ bb0 Hbb0 [x bb_id'] Hin2.
      simpl_ai.
      rewrite compose_relation_in_program_values_spec Hin in Hin2.
      apply transfer_term_compose in Hin2. move: Hin2 => [a'' [Hin2 Hle]] /=.
      eapply AbstractDomain.le_trans. exact Hle.
      apply compose_relation_le.
      move: Hin. rewrite in_cons => /orP [/eqP Heq | Hin].
      + bigsubst.
        rewrite abstract_interpret_program_edge_in_unchanged; auto.
        rewrite abstract_interpret_program_value_unchanged in Hin2; auto.
        move: (Hbb0) => Htransfer_bb.
        eapply abstract_interpret_bb_spec_term in Htransfer_bb.
        by move => /(_ bb Hbb0 (a'', bb_id') Hin2) /= in Htransfer_bb.
      + set state' := (abstract_interpret_bb _ _ _).
        by move => /(_ Hsoundbody bb_id Hin state' bb0 Hbb0 (a'', bb_id') Hin2) in Hind.
    - move => ps1 Hind1 ps2 Hind2 /= /andP[/andP[/andP[/andP[/allP Hnotsame1 Hnotsame2] HsoundDAG] Hsound1] Hsound2] bb_id.
      rewrite mem_cat => /orP[Hin1 | Hin2] state; [ | auto].
      move => /(_ bb_id Hin1) in Hnotsame1.
      apply abstract_interpret_program_term_fixpoint_kept => //.
      by apply Hind1.
    - move => bb_id /=. case Hbb: (p bb_id) => [bb | //] Hnotinsucc bb_id'.
      rewrite mem_seq1 => /eqP -> state.
      by apply abstract_interpret_bb_spec_term.
  Qed.

  Lemma abstract_interpret_program_inst_fixpoint_kept (ps: ProgramStructure):
    structure_sound p ps ->
    forall bb_id, (bb_id \notin (bbs_in_program ps)) ->
             forall state pos, inst_fixpoint state.1 bb_id pos ->
                          inst_fixpoint (abstract_interpret_program ps state).1 bb_id pos.
  Proof.
    move => Hsound bb_id Hbbnotin state pos Hinstfix bb Hbb inst Hinst.
    simpl_ai.
    by move: Hinstfix => /(_ bb Hbb inst Hinst).
  Qed.

  Theorem abstract_interpret_program_spec_inst (ps: ProgramStructure):
    structure_sound p ps ->
    forall bb_id, (bb_id \in (bbs_in_program ps)) ->
             forall state pos, inst_fixpoint (abstract_interpret_program ps state).1 bb_id pos.
  Proof.
    elim: ps.
    - move => header body Hind /= /andP[/andP[/andP[Hheadernotinbody _] Hsoundbody] HheaderSome] bb_id Hin state pos.
      move: HheaderSome. case Hheader : (p header) => [ bb_header | //] _ bb Hbb inst Hinst.
      simpl_ai.
      eapply AbstractDomain.le_trans. by apply transfer_inst_compose.
      apply compose_relation_le.
      move: Hin. rewrite in_cons => /orP [/eqP Heq | Hin].
      + bigsubst.
        rewrite !abstract_interpret_program_value_unchanged; auto.
        eapply abstract_interpret_bb_spec_inst in Hbb.
        by eapply Hbb; eauto.
      + set state' := (abstract_interpret_bb _ _ _).
        by move => /(_ Hsoundbody bb_id Hin state' pos bb Hbb inst Hinst) in Hind.
    - move => ps1 Hind1 ps2 Hind2 /= /andP[/andP[/andP[/andP[/allP Hnotsame1 Hnotsame2] HsoundDAG] Hsound1] Hsound2] bb_id.
      rewrite mem_cat => /orP[Hin1 | Hin2] state pos; [ | auto].
      move => /(_ bb_id Hin1) in Hnotsame1.
      apply abstract_interpret_program_inst_fixpoint_kept => //.
      by apply Hind1.
    - move => bb_id /=. case Hbb: (p bb_id) => [bb | //] Hnotinsucc bb_id0 Hne.
      move: Hne. rewrite mem_seq1 => /eqP -> state pos.
        by apply abstract_interpret_bb_spec_inst.
  Qed.

  Theorem abstract_interpret_program_spec_edge (ps: ProgramStructure):
    structure_sound p ps ->
    forall bb_id, (bb_id \in (bbs_in_program ps)) ->
             forall state, edges_invariant state.2 ->
                      edge_fixpoint (abstract_interpret_program ps state) bb_id.
  Proof.
    elim: ps.
    - move => header body Hind /= /andP[/andP[/andP[Hheadernotinbody Hnaturalloop] Hsoundbody] HheaderSome] bb_id Hin state Hinvariant.
      move: HheaderSome. case Hheader: (p header) => [ bb_header| //] _ in_id /=.
      set state' := (abstract_interpret_program _ _).
      simpl_ai.
      move: Hin. rewrite in_cons => /orP[/eqP Hbb_id | Hbbid_in].
      + subst. case (@idP (in_id \in bbs_in_program (Loop header body))) => [Hin_in | /negP /= Hin_notin]; simplssr.
        * rewrite abstract_interpret_program_value_unchanged => //.
          rewrite abstract_interpret_inst_list_0_unchanged. simpl_map.
          rewrite /compute_loop_effect_with_enter /compute_loop_effect.
          eapply AbstractDomain.le_trans. apply compose_assoc_r.
          eapply AbstractDomain.le_trans; last first. apply compose_assoc_l.
          apply compose_relation_le.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_quotient_right, join_sound_l.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_id.
          eapply AbstractDomain.le_trans; last first. apply transitive_closure_eq_compose.
          auto_ai.
        * rewrite /state' /compute_loop_effect_with_enter /compute_loop_effect.
          simpl_ai.
          eapply AbstractDomain.le_trans; last first. apply compose_assoc_l.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_quotient_right, compose_relation_quotient_right, join_sound_l.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_quotient_right, compose_relation_id.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_quotient_right, transitive_closure_ge_id.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_id.
          eapply AbstractDomain.le_trans; last first. apply join_edges_cond_spec. rewrite in_cons. apply /norP. split. apply H. exact Hin_notin.
          by auto_ai.
      + case (@idP (in_id \in bbs_in_program (Loop header body))) => [Hin_in | /negP Hin_notin]; simplssr.
        * apply compose_relation_le.
          have Hinvariant2 : (edges_invariant (set_input_to_identity state header).2) by [].
          eapply abstract_interpret_bb_edges_invariant_kept in Hinvariant2; last first. apply Hheader.
          by move: (Hind Hsoundbody bb_id Hbbid_in _ Hinvariant2 in_id).
        * have Hinvariant' : (edges_invariant state'.2).
            by apply abstract_interpret_program_edges_invariant_kept, abstract_interpret_bb_edges_invariant_kept => //.
          move => /allP /(_ bb_id Hbbid_in) /allP /(_ in_id) in Hnaturalloop.
          have -> // : (state'.2 in_id bb_id = bot).
          case: Hinvariant' => Hinvariant'_some Hinvariant'_none.
          case Hin_bb: (p in_id) => [[[in_inputs in_insts] in_term] | ]; [ | auto].
          eapply Hinvariant'_some; eauto.
          rewrite program_predecessors_spec Hin_bb in Hnaturalloop.
          apply /negP => Hinterm.
          apply Hnaturalloop in Hinterm.
            by rewrite Hinterm in Hin_notin.
    - move => ps1 Hind1 ps2 Hind2 /= /andP[/andP[/andP[/andP[/allP Hnotsame1 Hnotsame2] /allP HsoundDAG] Hsound1] Hsound2] bb_id.
      rewrite mem_cat => /orP[Hin1 | Hin2] state Hinvariant; last first. apply Hind2 => //. by apply abstract_interpret_program_edges_invariant_kept.
      move => in_id.
      case Hin_id: (p in_id) => [ [[in_inputs in_insts] in_term] | ].
      + simpl_ai.
        move => /(_ Hsound1 bb_id Hin1 state Hinvariant in_id) in Hind1.
        case (@idP (in_id \in bbs_in_program ps2)) => [ Hin2 | /negP Hnotin2 ]; [ | auto_ai ].
        * have Hnotinps2 : (bb_id \notin program_successors p ps2). apply /negP => Hinps2.
            by move => /(_ bb_id Hinps2) in HsoundDAG; rewrite Hin1 in HsoundDAG.
          apply abstract_interpret_program_edges_invariant_kept with (ps := ps1) in Hinvariant => //.
          apply abstract_interpret_program_edges_invariant_kept with (ps := ps2) in Hinvariant => //.
          case Hinvariant => [Hinvariant_some _].
          move => /(_ _ _ Hin_id bb_id) in Hinvariant_some.
          rewrite Hinvariant_some => //.
          apply /negP => Hinterm.
          move => /negP in Hnotinps2. apply Hnotinps2.
          apply program_successors_spec.
          exists in_id. rewrite Hin2. split; auto. by rewrite Hin_id.
      + apply abstract_interpret_program_edges_invariant_kept with (ps := ps1) in Hinvariant => //.
        apply abstract_interpret_program_edges_invariant_kept with (ps := ps2) in Hinvariant => //.
        case Hinvariant => [_ Hinvariant_none].
        move => /(_ _ Hin_id bb_id) in Hinvariant_none.
        by rewrite Hinvariant_none.
    - move => bb_id /= Hsound bb_id0. rewrite mem_seq1 => /eqP -> state.
      move: Hsound. case_eq (p bb_id) => [ [[bb_inputs bb_insts] bb_term] Hbb Hnotin Hinvariant | //].
        by apply abstract_interpret_bb_spec_edge.
  Qed.

  Definition input_state : AS :=
    (("entry" |-> (O |-> id_relation; _ |-> bot); (_ |-> (_ |-> bot))), (_ |-> (_ |-> bot))).

  Theorem abstract_interpret_program_spec (ps: ProgramStructure):
    structure_sound p (DAG (BB "entry") ps) ->
    (forall bb_id bb, p bb_id = Some bb <-> (bb_id \in (bbs_in_program (DAG (BB "entry") ps)))) ->
    forall R R' bb_id pos, reachable_states p R (bb_id, pos, R') ->
                      forall bb, p bb_id = Some bb ->
                      Ensembles.In _ (gamma ((abstract_interpret_program (DAG (BB "entry") ps) input_state).1 bb_id pos)) (R, R').
  Proof.
    move => /= /andP[/andP[/andP[/andP[/andP[Hnotsame1 _] Hnotsame2] HsoundDAG] Hsound1] Hsound2] Hallin R R' bb_id pos Hreachable_states bb Hbb.
    move: Hreachable_states. rewrite /reachable_states.
    move Hs : ("entry", O, R) => s.
    move Hs' : (bb_id, pos, R') => s'.
    set p'hack := (p, 0).
    move Hp : p'hack.1 => p'. rewrite /= in Hp.
    rewrite [in p "entry"]Hp [in multi_step _ _ _]Hp.
    move => Hmulti_step. move: Hs' Hs Hp.
    move: bb_id bb Hbb pos R'.
    elim Hmulti_step => [ p0 s0 bb_id bb Hbb pos R' <- [<- <- <-] <- | ].
    - case_eq (p "entry").
      + move => bb_entry Hbb_entry. rewrite abstract_interpret_program_value_unchanged => //=.
        rewrite abstract_interpret_inst_list_0_unchanged.
        rewrite /join_edges. rewrite /join_edges_cond_aux.
        simpl_map.
        by apply join_sound_l, id_relation_spec.
      + rewrite abstract_interpret_program_value_unchanged => //= _.
        simpl_map. by apply id_relation_spec.
    - move => p0 s0 [[bb_id' pos'] R'] s0'' Hmulti_step' Hind Hstep' bb_id'' bb Hbb pos'' R'' Hs0'' Hs0 Hp0.
      move: Hind. rewrite -Hp0. case_eq (p "entry") => [ bb_entry Hbb_entry | Hentry ].
      + inversion Hstep'.
        * rewrite -Hs0'' in H4. inversion H4. symmetry in Hp0. subst.
          move => /(_ bb_id'' bb Hbb pos' R' (erefl _) (erefl _) (erefl _)) Hind.
          move: (H3) => Hbb''.
          apply Hallin in H3. move: H3. rewrite in_cons => /orP[ /eqP Hentry'' | Hbb''_in ].
          { subst. rewrite abstract_interpret_program_value_unchanged => //.
            have: (inst_fixpoint (abstract_interpret_bb bb_entry "entry" input_state).1 "entry" pos') by apply abstract_interpret_bb_spec_inst.
            move => /(_ _ Hbb'' _ H5). apply.
            eapply transfer_inst_sound. apply H6. rewrite /abstract_interpret_bb in Hind.
              by rewrite abstract_interpret_program_value_unchanged in Hind. }
          { have: (inst_fixpoint (abstract_interpret_program ps (abstract_interpret_bb bb_entry "entry" input_state)).1 bb_id'' pos'). apply abstract_interpret_program_spec_inst => //.
            move => /(_ _ Hbb'' _ H5). apply.
            eapply transfer_inst_sound; eauto. }
        * rewrite -Hs0'' in H4. inversion H4. symmetry in Hp0. subst. move: (H3) => Hbb''.
          move => /(_ bb_id' (params, insts, term) Hbb'' pos' R' (erefl _) (erefl _) (erefl _)) Hind.
          apply Hallin in H3. move: H3. rewrite in_cons => /orP[ /eqP Hentry' | Hbb'_in ].
          { subst. apply Hallin in Hbb. move: Hbb. rewrite in_cons => /orP [/eqP Hentry'' | Hbb''_in].
            { subst. rewrite Hbb'' in Hsound1. inversion H6; subst; try by rewrite /= in Hsound1.
              rewrite /= in Hsound1. rewrite in_cons mem_seq1 eq_refl in Hsound1. move => /norP in Hsound1.
              by move: Hsound1 => [_ Hsound1]. }
            { move: (abstract_interpret_program_spec_edge ps Hsound2 bb_id'' Hbb''_in (abstract_interpret_bb bb_entry "entry" input_state)).
              move: (term_successors_spec _ _ _ _ _ H6) => Hin_term_succ.
              have Hinvariant : (edges_invariant (abstract_interpret_bb bb_entry "entry" input_state).2). by apply abstract_interpret_bb_edges_invariant_kept => //.
              move => /(_ Hinvariant "entry"). apply.
              move: (abstract_interpret_bb_spec_term (params, insts, term) "entry" input_state Hbb'').
              rewrite abstract_interpret_program_edge_in_unchanged => //.
              move: (Hmulti_step') => Hinbounds.
              apply reachable_states_pos in Hinbounds. rewrite /= Hbb'' in Hinbounds.
              apply nth_error_None in H5.
              have Hpos': (Datatypes.length insts = pos') by liassr.
              move => /(_ _ Hbb''). rewrite Hpos'.
              eapply transfer_term_sound in H6; last first. apply Hind.
              move: H6 => [a' [HInTerm HIn]] /(_ (a', bb_id'')).
              rewrite abstract_interpret_program_value_unchanged in HInTerm => //.
              rewrite Hbb_entry in Hbb''. inversion Hbb''. subst.
              move => /(_ HInTerm (R, R'') HIn). auto.
            }
          }
          {
            move: (Hbb) => Hbb_in. apply Hallin in Hbb_in. move: Hbb_in. rewrite in_cons => /orP [/eqP Hbb''' | Hbb''_in].
            {
              subst. apply term_successors_spec in H6. move => /allP /(_ "entry") in HsoundDAG.
              have: ("entry" \in program_successors p ps); last first. move => /HsoundDAG. by rewrite in_cons eq_refl.
              apply program_successors_spec.
              exists bb_id'. split; auto. by rewrite Hbb''.
            }
            {
              move: (abstract_interpret_program_spec_edge ps Hsound2 bb_id'' Hbb''_in (abstract_interpret_bb bb_entry "entry" input_state)).
              move: (term_successors_spec _ _ _ _ _ H6) => Hin_term_succ.
              have Hinvariant : (edges_invariant (abstract_interpret_bb bb_entry "entry" input_state).2). by apply abstract_interpret_bb_edges_invariant_kept.
              move => /(_ Hinvariant bb_id'). apply.
              move: (abstract_interpret_program_spec_term ps Hsound2 bb_id' Hbb'_in (abstract_interpret_bb bb_entry "entry" input_state)).
              move: (Hmulti_step') => Hinbounds.
              apply reachable_states_pos in Hinbounds. rewrite /= Hbb'' in Hinbounds.
              apply nth_error_None in H5.
              have Hpos': (Datatypes.length insts = pos') by liassr.
              move => /(_ _ Hbb''). rewrite Hpos'.
              eapply transfer_term_sound in H6; last first. apply Hind.
              move: H6 => [a' [HInTerm HIn]] /(_ (a', bb_id'')).
              move => /(_ HInTerm (R, R'') HIn). auto.
            }
          }
      + have: ("entry" \in "entry" :: (bbs_in_program ps)) by rewrite in_cons eq_refl.
        move => /Hallin. by rewrite Hentry => /(_ bb).
  Qed.

End AbstractInterpreter.
