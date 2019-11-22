From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat.
From PolyAI Require Export LRTransferFunction LSSA Tactic.
From Coq Require Import Lists.List.
From mathcomp.ssreflect Require Import seq.

Require Import Lia.

Local Open Scope string_scope.

Section AbstractInterpreter.

  Context {ab: eqType}
          {ad: adom (prod_eqType RegisterMap RegisterMap) ab}
          {adr: adom_relational ad}
          (tf: transfer_function_relational adr)
          (p: Program).

  (* Associate for every control location an abstract state *)
  Notation ASValues := (@total_map_d bbid_eqType (@total_map_d nat_eqType ab bot) (_ |-> bot)).
  Notation ASEdges := (@total_map_d bbid_eqType (@total_map_d bbid_eqType ab bot) (_ |-> bot)).
  Notation ASEdgesP := (@partial_map bbid_eqType (@total_map_d bbid_eqType ab bot)).
  Definition AS : Type := ASValues * ASEdges.

  (* Properties we want at the end of our analysis *)
  Definition inst_fixpoint (stateV: ASValues) (bb_id: bbid) (pos: nat) :=
    if p bb_id is Some bb then
      if nth_error bb.1.2 pos is Some inst then
        le (transfer_inst inst (stateV bb_id pos)) (stateV bb_id (S pos))
      else
        true
    else
      true.

  Definition term_fixpoint (state: AS) (bb_id: bbid) :=
    if p bb_id is Some bb then
      all (fun (abbbid: (ab * bbid)) => le abbbid.1 (state.2 bb_id abbbid.2))
              (transfer_term bb.2 (state.1 bb_id (length bb.1.2)))
    else
      true.

  Definition edge_fixpoint (state: AS) (bb_id: bbid) :=
    forall in_id,
      if p in_id is Some (_, _, t) then
        (bb_id \in (term_successors t)) ->
        le (state.2 in_id bb_id) (state.1 bb_id 0)
      else
        true.

  Definition edges_invariant (stateE: ASEdges) :=
    forall in_id, match p in_id with
             | None => true
             | Some (_, _, term) => forall out_id, out_id \notin term_successors term -> stateE in_id out_id == bot
             end.

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
      rewrite /inst_fixpoint -Hbb.
      move: (Hnth (n'' - pos)).
      rewrite -leqNgt in Hge.
      rewrite subnK => [<- | //].
      by case (n'' - pos).
    - apply Hind => [n | n' Hn'ltpos1]. by rewrite addnS; apply (Hnth n.+1).
      case_eq (n' < pos) => [Heqn'pos | ].
      + move: (Heqn'pos).
        apply Hfixpoint in Heqn'pos.
        rewrite /inst_fixpoint -Hbb in Heqn'pos *.
        case: (nth_error bb.1.2 n') Heqn'pos => [inst0 Hle | //].
        move: Hn'ltpos1.
        rewrite !ltn_neqAle => /andP[Hnen'pos _] /andP[Hnen'pos2 _].
        rewrite eq_sym in Hnen'pos2.
        by auto_map.
      + move: (Hn'ltpos1).
        rewrite ltnS leq_eqVlt => /orP [ Heq _ | Hne Hne']; last first. by rewrite Hne' in Hne.
        rewrite !(eqP Heq).
        rewrite /inst_fixpoint -Hbb.
        rewrite -(Hnth 0) /=.
        simpl_map.
        rewrite td_update_neq. by apply AbstractDomain.le_refl.
        rewrite eq_sym. by apply /eqP.
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
    simpl_map.
    move => /orP[ /eqP [-> ->] | HIn].
    + by auto_map.
    + apply Hind in HIn.
      by case (out_id =P out_id0) => [ -> | /eqP Hne ]; auto_map.
  Qed.

  Theorem abstract_interpret_term_join_edges_out_unchanged (in_id out_id: bbid) (stateE: ASEdges) (edges: list (ab * bbid)):
    (forall a , (a, out_id) \notin edges) ->
    forall id, stateE id out_id = (abstract_interpret_term_join_edges stateE in_id edges id out_id).
  Proof.
    elim edges => [ // | /= [a id] l Hind HnotIn id0].
    move: (HnotIn a).
    rewrite in_cons => /norP [Hne HanotIn].
    have: (is_true (id != out_id)). apply /negP => /eqP Heq. rewrite Heq in Hne. by rewrite eq_refl in Hne. move => Hneid.
    case (in_id =P id0) => [ <- | /eqP Hneid0 ]; simpl_map; apply Hind => a0; move: (HnotIn a0); by autossr.
  Qed.

  Theorem abstract_interpret_term_join_edges_in_unchanged (id in_id: bbid) (stateE: ASEdges) (edges: list (ab * bbid)):
    in_id != id ->
    forall out_id, (abstract_interpret_term_join_edges stateE id edges in_id out_id) = stateE in_id out_id.
  Proof.
    move => Hne out_id.
    elim edges => [ // | [a out_id0] l Hind ].
    auto_map.
  Qed.

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
    Some bb = p bb_id ->
    term_fixpoint (state.1, (abstract_interpret_term bb bb_id state)) bb_id.
  Proof.
    move => Hbb. rewrite /term_fixpoint -Hbb.
    apply/allP => [[a out_id]].
    rewrite /abstract_interpret_term.
    by apply abstract_interpret_term_join_edges_spec.
  Qed.

  Lemma abstract_interpret_term_bb_edge_out_unchanged (bb_id: bbid) (bb: BasicBlock):
    (p bb_id = Some bb) ->
    forall bb_id', bb_id' \notin (term_successors bb.2) ->
              forall state bb_id'', (abstract_interpret_term bb bb_id state) bb_id'' bb_id' = state.2 bb_id'' bb_id'.
  Proof.
    move => Hbb bb_id' /negP Hbb_not_term state bb_id''.
    rewrite /abstract_interpret_term. symmetry.
    apply abstract_interpret_term_join_edges_out_unchanged => a.
    apply /negP => Hbb_not_transfer_term.
    apply Hbb_not_term.
    eapply transfer_term_only_successors; eauto.
  Qed.

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

  Theorem abstract_interpret_term_edges_invariant_kept (bb_id: bbid) (state: AS):
    edges_invariant state.2 ->
    match p bb_id with
    | Some bb => edges_invariant (abstract_interpret_term bb bb_id state)
    | None => true
    end.
  Proof.
    rewrite /edges_invariant.
    case_eq (p bb_id) => [ [[inputs insts] term] Hbb Hinvariant in_id | //].
    move: Hinvariant => /(_ in_id).
    case_eq (p in_id) => [ [[in_inputs in_insts] in_term] Hin Hind out_id Hnotin | //].
    case (bb_id =P in_id) => [ Heq | Hne ].
    - rewrite Heq in Hind *.
      rewrite abstract_interpret_term_bb_edge_out_unchanged; autossr.
      subst. rewrite Hbb in Hin. by case: Hin => -> -> ->.
    - rewrite abstract_interpret_term_join_edges_in_unchanged; autossr.
  Qed.

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
    simpl_map.
    case (p in_id) => [ [[_ _] t] _ /= | //].
    by apply le_join_r, join_edges_spec.
  Qed.

  Theorem abstract_interpret_bb_monotone_0 (bb: BasicBlock) (bb_id bb_id': bbid) (state: AS):
    le (state.1 bb_id' 0) ((abstract_interpret_bb bb bb_id state).1 bb_id' 0).
  Proof.
    rewrite /abstract_interpret_bb.
    simpl_map.
    erewrite abstract_interpret_inst_list_0_unchanged.
    case (bb_id =P bb_id') => [ -> | Hne ]; by auto_map.
  Qed.

  Theorem abstract_interpret_bb_edge_in_unchanged (bb: BasicBlock) (bb_id in_id out_id: bbid) (state: AS):
    Some bb = p bb_id ->
    in_id != bb_id ->
    (abstract_interpret_bb bb bb_id state).2 in_id out_id = state.2 in_id out_id.
  Proof.
    move => Hbb Hbbne /=.
    by rewrite /abstract_interpret_term /= abstract_interpret_term_join_edges_in_unchanged.
  Qed.

  Theorem abstract_interpret_bb_value_unchanged (bb: BasicBlock) (bb_id bb_id': bbid) (state: AS):
    Some bb = p bb_id ->
    bb_id != bb_id' ->
    forall pos, (abstract_interpret_bb bb bb_id state).1 bb_id' pos = state.1 bb_id' pos.
  Proof.
    move => Hbb Hbbne pos /=.
    by rewrite abstract_interpret_inst_list_bb_unchanged; auto_map.
  Qed.

  Theorem abstract_interpret_bb_edges_invariant_kept (bb_id: bbid) (state: AS):
    edges_invariant state.2 ->
    match p bb_id with
    | None => true
    | Some bb => edges_invariant (abstract_interpret_bb bb bb_id state).2
    end.
  Proof.
    rewrite /abstract_interpret_bb => Hinvariant. move: (Hinvariant bb_id). simpl_map.
    case_eq (p bb_id) => [ [[inputs insts] term] Hbb Hterm in_id | // ].
    move: (abstract_interpret_term_edges_invariant_kept bb_id).
    rewrite Hbb. by apply.
  Qed.

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
  Obligation 1.
    by apply compose_bot.
  Qed.

  Theorem compose_relation_in_program_edges_spec (ps: ProgramStructure) (stateE: ASEdges) (relation: ab) (in_id out_id: bbid) :
    compose_relation_in_program_edges ps stateE relation in_id out_id =
    if (in_id \in bbs_in_program ps) then compose_relation relation (stateE in_id out_id) else stateE in_id out_id.
  Proof.
    rewrite td_pointwise_un_op_in_seq_spec.
    case: (in_id \in bbs_in_program ps) => [ /= | // ].
    rewrite /eq_rect. case (compose_relation_in_program_edges_obligation_1 relation).
    by apply td_pointwise_un_op_spec.
  Qed.

  Program Definition compose_relation_in_program_values (ps: ProgramStructure) (stateV: ASValues) (relation: ab) :=
    td_pointwise_un_op_in_seq stateV (fun m => td_pointwise_un_op m (compose_relation relation)) (bbs_in_program ps).
  Obligation 1.
    by apply compose_bot.
  Qed.

  Theorem compose_relation_in_program_values_spec (ps: ProgramStructure) (stateV: ASValues) (relation: ab) (bb_id: bbid) (pos: nat) :
    compose_relation_in_program_values ps stateV relation bb_id pos =
    if (bb_id \in bbs_in_program ps) then compose_relation relation (stateV bb_id pos) else stateV bb_id pos.
  Proof.
    rewrite td_pointwise_un_op_in_seq_spec.
    case: (bb_id \in bbs_in_program ps) => [ | // ].
    rewrite /eq_rect. case (compose_relation_in_program_values_obligation_1 relation).
    by apply td_pointwise_un_op_spec.
  Qed.

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

  Theorem abstract_interpret_program_edge_in_unchanged (ps: ProgramStructure) (in_id out_id: bbid) (state: AS):
    structure_sound p ps ->
    in_id \notin (bbs_in_program ps) ->
    (abstract_interpret_program ps state).2 in_id out_id = state.2 in_id out_id.
  Proof.
    elim: ps state.
    - move => header_id body Hind state /= /andP [/andP[/andP[Hsound _] _] _] /negb_true_iff Hnotin.
      case H: (p header_id) => //=.
      rewrite compose_relation_in_program_edges_spec Hnotin /=.
      move: Hnotin. rewrite in_cons => /orb_false_iff[/negb_true_iff Hne /negb_true_iff Hnotin].
      rewrite Hind; auto.
        by rewrite abstract_interpret_bb_edge_in_unchanged.
    - move => ps1 Hind1 ps2 Hind2 state /= /andP[/andP[_ Hsound1] Hsound2].
      rewrite mem_cat => /norP [Hnotin1 Hnotin2].
        by rewrite Hind2; auto.
    - move => bb_id state /=.
      case_eq (p bb_id); auto => bb Hsound Hbb /negb_true_iff Hnotin.
      rewrite mem_seq1 in Hnotin. move => /negb_true_iff in Hnotin.
      apply abstract_interpret_bb_edge_in_unchanged; auto.
  Qed.

  Theorem abstract_interpret_program_value_unchanged (ps: ProgramStructure) (in_id: bbid) (state: AS):
    structure_sound p ps ->
    in_id \notin (bbs_in_program ps) ->
    forall pos, (abstract_interpret_program ps state).1 in_id pos = state.1 in_id pos.
  Proof.
    elim: ps state.
    - move => header_id body Hind state /= /andP[/andP[/andP[Hsound _] _] _] /negb_true_iff Hnotin pos.
      case H: (p header_id) => //=.
      rewrite compose_relation_in_program_values_spec Hnotin /=.
      move: Hnotin. rewrite in_cons eq_sym => /orb_false_iff[/negb_true_iff Hne /negb_true_iff Hnotin].
      rewrite Hind; auto. rewrite abstract_interpret_bb_value_unchanged; auto.
      by auto_map.
    - move => ps1 Hind1 ps2 Hind2 state /= /andP[/andP[_ Hsound1] Hsound2].
      rewrite /= mem_cat => /norP[Hnotin1 Hnotin2] pos.
      rewrite Hind2; auto.
    - move => bb_id state /=. case_eq (p bb_id); auto => bb Hbb _.
      rewrite mem_seq1 => Hne pos. apply abstract_interpret_bb_value_unchanged; auto.
        by rewrite eq_sym.
  Qed.

  Theorem abstract_interpret_program_spec_term (ps: ProgramStructure):
    structure_sound p ps ->
    forall bb_id, (bb_id \in (bbs_in_program ps)) ->
             forall state, term_fixpoint (abstract_interpret_program ps state) bb_id.
  Proof.
    elim: ps.
    - move => header body Hind /= /andP[/andP[/andP[Hsound Hheadernotinbody] _] HheaderSome] bb_id Hin state.
      move: HheaderSome. case_eq (p header) => [ bb Hbb _ | //]. rewrite /term_fixpoint.
      case_eq (p bb_id) => [ bb2 Hbb2 | //]. apply /allP => [[x bb_id']] Hin2.
      rewrite compose_relation_in_program_edges_spec Hin.
      rewrite compose_relation_in_program_values_spec Hin in Hin2.
      apply transfer_term_compose in Hin2. move: Hin2 => [a'' [Hin2 Hle]] /=.
      eapply AbstractDomain.le_trans. apply Hle.
      apply compose_relation_le.
      move: Hin. rewrite in_cons => /orP [/eqP Heq | Hin].
      + rewrite -Heq in Hheadernotinbody.
        rewrite abstract_interpret_program_edge_in_unchanged; auto.
        rewrite abstract_interpret_program_value_unchanged in Hin2; auto.
        move: (Hbb) => Htransfer_bb.
        apply abstract_interpret_bb_spec_term with (state := (set_input_to_identity state header)) in Htransfer_bb.
        rewrite /term_fixpoint Hbb in Htransfer_bb. move => /allP in Htransfer_bb.
        rewrite Heq Hbb in Hbb2. move: Hbb2 => [Hbbeq]. subst.
        by move => /(_ (a'', bb_id') Hin2) in Htransfer_bb.
      + move => /(_ Hsound bb_id Hin (abstract_interpret_bb bb header (set_input_to_identity state header))) in Hind.
        rewrite /term_fixpoint Hbb2 in Hind.
        by move => /allP /(_ (a'', bb_id') Hin2) in Hind.
    - move => ps1 Hind1 ps2 Hind2 /= /andP[/andP[/andP[/andP[/allP Hnotsame1 Hnotsame2] HsoundDAG] Hsound1] Hsound2] bb_id.
      rewrite mem_cat => /orP[Hin1 | Hin2] state; last first. apply Hind2; auto.
      move: (Hin1) => Hin1'. apply Hind1 with (state := state) in Hin1'; auto.
      move: Hin1'. rewrite /term_fixpoint. case (p bb_id); auto => bb_id' /allP Hin1'.
      apply /allP => /= [[a bb_id''] Hin] /=.
      move => /(_ (a, bb_id'')) /= in Hin1'.
      rewrite abstract_interpret_program_edge_in_unchanged; auto. apply Hin1'.
      by rewrite abstract_interpret_program_value_unchanged in Hin; auto.
    - move => bb_id /=. case_eq (p bb_id) => [ bb Hbb Hnotinsucc bb_id0 Hne state | // ].
      move: Hne. rewrite mem_seq1 => /eqP ->.
      by apply abstract_interpret_bb_spec_term.
  Qed.

  Theorem abstract_interpret_program_spec_inst (ps: ProgramStructure):
    structure_sound p ps ->
    forall bb_id, (bb_id \in (bbs_in_program ps)) ->
             forall state pos, inst_fixpoint (abstract_interpret_program ps state).1 bb_id pos.
  Proof.
    elim: ps.
    - move => header body Hind /= /andP[/andP[/andP[Hsound Hheadernotinbody] _] HheaderSome] bb_id Hin state pos.
      move: HheaderSome. case_eq (p header) => [ bb Hbb _ | //]. rewrite /inst_fixpoint.
      case_eq (p bb_id) => [ bb2 Hbb2 | //]. case_eq (nth_error bb2.1.2 pos) => [ inst Hinst /= | //].
      rewrite !compose_relation_in_program_values_spec !Hin.
      eapply AbstractDomain.le_trans. apply transfer_inst_compose.
      apply compose_relation_le.
      move: Hin. rewrite in_cons => /orP [/eqP Heq | Hin].
       + rewrite Heq Hbb in Hbb2. move: Hbb2 => [Hbb2]. subst.
         rewrite !abstract_interpret_program_value_unchanged; auto.
         move: (Hbb) => Htransfer_bb.
         apply abstract_interpret_bb_spec_inst with (state := (set_input_to_identity state header)) (n := pos) in Htransfer_bb.
         by rewrite /inst_fixpoint Hbb Hinst in Htransfer_bb.
      + move => /(_ Hsound bb_id Hin (abstract_interpret_bb bb header (set_input_to_identity state header)) pos) in Hind.
        by rewrite /inst_fixpoint Hbb2 Hinst in Hind.
    - move => ps1 Hind1 ps2 Hind2 /= /andP[/andP[/andP[/andP[/allP Hnotsame1 Hnotsame2] HsoundDAG] Hsound1] Hsound2] bb_id.
      rewrite mem_cat => /orP[Hin1 | Hin2] state pos; last first. apply Hind2; auto.
      move: (Hin1) => Hin1'. apply Hind1 with (state := state) (pos := pos) in Hin1'; auto.
      move: Hin1'. rewrite /inst_fixpoint. case (p bb_id); auto => bb_id'.
      case (nth_error bb_id'.1.2 pos) => [ inst Hle1 | //].
      move => /(_ bb_id Hin1) in Hnotsame1.
        by rewrite !(abstract_interpret_program_value_unchanged ps2) => //.
    - move => bb_id /=. case_eq (p bb_id) => [ bb Hbb Hnotinsucc bb_id0 Hne state | // ].
      move: Hne. rewrite mem_seq1 => /eqP ->.
        by apply abstract_interpret_bb_spec_inst.
  Qed.

  Theorem abstract_interpret_program_spec_edge (ps: ProgramStructure):
    structure_sound p ps ->
    forall bb_id, (bb_id \in (bbs_in_program ps)) ->
             forall state, edge_fixpoint (abstract_interpret_program ps state) bb_id.
  Proof.
    elim: ps.
    - move => header body Hind /= /andP[/andP[/andP[Hsound /negb_true_iff Hheadernotinbody] Hnaturalloop] HheaderSome] bb_id Hin state.
      move: HheaderSome. case_eq (p header) => [ bb Hbb _ | //]. rewrite /edge_fixpoint => in_id /=.
      rewrite compose_relation_in_program_edges_spec compose_relation_in_program_values_spec Hin.
      set state' := (abstract_interpret_program _ _).
      case_eq (p in_id) => [ [[in_inputs in_insts] in_term] Hbb_some Hbb_in_term | //].
      move: Hin. rewrite in_cons => /orP[/eqP Hbb_id | Hbbid_in].
      + subst. case_eq (in_id \in bbs_in_program (Loop header body)) => [Hin_in | Hin_notin].
        * move: Hheadernotinbody => /negb_true_iff Hheadernotinbody.
          rewrite Hin_in. rewrite abstract_interpret_program_value_unchanged => //=.
          rewrite abstract_interpret_inst_list_0_unchanged. simpl_map.
          rewrite /compute_loop_effect_with_enter.
          eapply AbstractDomain.le_trans. apply compose_assoc_r.
          eapply AbstractDomain.le_trans; last first. apply compose_assoc_l.
          apply compose_relation_le. rewrite /compute_loop_effect.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_quotient_right, join_sound_l.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_id.
          eapply AbstractDomain.le_trans; last first. apply transitive_closure_eq_compose.
          apply compose_relation_le.
          apply join_edges_cond_spec. by rewrite Hin_in.
        * move: Hheadernotinbody => /negb_true_iff Hheadernotinbody.
          rewrite Hin_notin. rewrite abstract_interpret_program_value_unchanged => //=.
          move: Hin_notin => /negb_true_iff /=. rewrite in_cons => /norP[Hin_ne Hin_notin].
          rewrite abstract_interpret_inst_list_0_unchanged. simpl_map.
          rewrite /compute_loop_effect_with_enter /state'.
          rewrite abstract_interpret_program_edge_in_unchanged => //.
          rewrite abstract_interpret_bb_edge_in_unchanged => //=.
          eapply AbstractDomain.le_trans; last first. apply compose_assoc_l.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_quotient_right, compose_relation_quotient_right, join_sound_l.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_quotient_right, compose_relation_id.
          rewrite /compute_loop_effect.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_quotient_right, transitive_closure_ge_id.
          eapply AbstractDomain.le_trans; last first. apply compose_relation_id.
          eapply AbstractDomain.le_trans; last first. apply join_edges_cond_spec. rewrite in_cons. apply /norP. split. apply Hin_ne. auto.
          rewrite abstract_interpret_program_edge_in_unchanged => //.
            by rewrite abstract_interpret_bb_edge_in_unchanged.
      + case_eq (in_id \in bbs_in_program (Loop header body)) => [Hin_in | Hin_notin].
        * rewrite Hin_in. apply compose_relation_le.
          move: (Hind Hsound bb_id Hbbid_in (abstract_interpret_bb bb header (set_input_to_identity state header)) in_id). fold state'.
          by rewrite Hbb_some => /(_ Hbb_in_term).
        * move => /allP /(_ bb_id Hbbid_in) /allP /(_ in_id) in Hnaturalloop.
          rewrite program_predecessors_spec in Hnaturalloop.
          rewrite Hbb_some in Hnaturalloop.
          move => /(_ Hbb_in_term) in Hnaturalloop.
          by rewrite Hin_notin in Hnaturalloop.
    - move => ps1 Hind1 ps2 Hind2 /= /andP[/andP[/andP[/andP[/allP Hnotsame1 Hnotsame2] /allP HsoundDAG] Hsound1] Hsound2] bb_id.
      rewrite mem_cat => /orP[Hin1 | Hin2] state; last first. by apply Hind2.
      rewrite /edge_fixpoint => in_id.
      case_eq (p in_id) => [ [[in_inputs in_insts] in_term] Hin_id Hbb_in_succ_in | //].
      move => /(_ bb_id Hin1) in Hnotsame1.
      rewrite abstract_interpret_program_value_unchanged => //.
      move => /(_ Hsound1 bb_id Hin1 state in_id) in Hind1.
      rewrite Hin_id in Hind1.
      rewrite abstract_interpret_program_edge_in_unchanged => //. by apply Hind1.
      apply /negP => Hin_in2.
      have Hbb_in2: (bb_id \in program_successors p ps2).
      apply program_successors_spec.
      exists in_id. rewrite Hin_id => //.
      by move => /(_ bb_id Hbb_in2) /negP in HsoundDAG.
    - move => bb_id /= Hsound bb_id0. rewrite mem_seq1 => /eqP -> state.
      move: Hsound. case_eq (p bb_id) => [ [[bb_inputs bb_insts] bb_term] Hbb Hnotin | //].
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
    move: Hreachable_states.
    rewrite /reachable_states.
    move Hs : ("entry", O, R) => s.
    move Hs' : (bb_id, pos, R') => s'.
    move Hp : p => p'.
    move => Hmulti_step. move: Hs' Hs Hp.
    move: bb_id bb Hbb pos R'.
    elim Hmulti_step => [ p0 s0 bb_id bb Hbb pos R' <- [<- <- <-] <- | ].
    - case_eq (p "entry").
      + move => bb_entry Hbb_entry. rewrite abstract_interpret_program_value_unchanged => //=.
        rewrite abstract_interpret_inst_list_0_unchanged.
        rewrite /join_edges. rewrite /join_edges_cond_aux.
        simpl_map.
        have: (Ensembles.In _ (gamma id_relation) (R, R)) by apply id_relation_spec.
          by apply gamma_monotone.
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
            rewrite /inst_fixpoint Hbb'' /= H5 => /gamma_monotone. simpl_map. apply.
            eapply transfer_inst_sound. apply H6. rewrite /abstract_interpret_bb in Hind.
              by rewrite abstract_interpret_program_value_unchanged in Hind. }
          { have: (inst_fixpoint (abstract_interpret_program ps (abstract_interpret_bb bb_entry "entry" input_state)).1 bb_id'' pos'). apply abstract_interpret_program_spec_inst => //.
            rewrite /inst_fixpoint. rewrite Hbb'' H5 => /gamma_monotone. apply.
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
              move => /(_ "entry"). rewrite Hbb''. move => /(_ Hin_term_succ) /gamma_monotone. apply.
              move: (abstract_interpret_bb_spec_term (params, insts, term) "entry" input_state Hbb'').
              rewrite abstract_interpret_program_edge_in_unchanged => //.
              move: (Hmulti_step') => Hinbounds.
              apply reachable_states_pos in Hinbounds. rewrite /= Hbb'' in Hinbounds.
              apply nth_error_None in H5.
              have Hpos': (Datatypes.length insts = pos') by lia.
              rewrite /term_fixpoint Hbb'' => /allP. rewrite Hpos'.
              eapply transfer_term_sound in H6; last first. apply Hind.
              move: H6 => [a' [HInTerm HIn]] /(_ (a', bb_id'')).
              rewrite abstract_interpret_program_value_unchanged in HInTerm => //.
              rewrite Hbb_entry in Hbb''. inversion Hbb''. subst.
              move => /(_ HInTerm) => /gamma_monotone /(_ (R, R'') HIn). auto.
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
              move => /(_ bb_id'). rewrite Hbb''. move => /(_ Hin_term_succ) /gamma_monotone. apply.
              move: (abstract_interpret_program_spec_term ps Hsound2 bb_id' Hbb'_in (abstract_interpret_bb bb_entry "entry" input_state)).
              move: (Hmulti_step') => Hinbounds.
              apply reachable_states_pos in Hinbounds. rewrite /= Hbb'' in Hinbounds.
              apply nth_error_None in H5.
              have Hpos': (Datatypes.length insts = pos') by lia.
              rewrite /term_fixpoint Hbb'' => /allP. rewrite Hpos'.
              eapply transfer_term_sound in H6; last first. apply Hind.
              move: H6 => [a' [HInTerm HIn]] /(_ (a', bb_id'')).
              move => /(_ HInTerm) => /gamma_monotone /(_ (R, R'') HIn). auto.
            }
          }
      + have: ("entry" \in "entry" :: (bbs_in_program ps)) by rewrite in_cons eq_refl.
        move => /Hallin. by rewrite Hentry => /(_ bb).
  Qed.

End AbstractInterpreter.
