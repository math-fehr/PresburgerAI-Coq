From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat.
From PolyAI.LoopFormalization Require Export LTransferFunction LSSA.
From Coq Require Import Lists.List.

Definition AbstractState (ab: Type) := @total_map bbid_eqType (@total_map nat_eqType ab).

Definition inst_fixpoint {ab: Type} {ad: adom ab} {tf: transfer_function ad} (p: Program) (state: AbstractState ab)
           (bb_id: bbid) (pos: nat) :=
  forall bb, Some bb = p bb_id ->
        forall inst, Some inst = nth_error bb.1.2 pos ->
                le (transfer_inst inst (state bb_id pos)) (state bb_id (S pos)).

Definition term_fixpoint {ab: Type} {ad: adom ab} {tf: transfer_function ad}
           (p: Program) (state: AbstractState ab) (bb_id: bbid) :=
  forall bb, Some bb = p bb_id ->
        forallb (fun abbbid => match abbbid with
                            | (ab, out_id) => le ab (state out_id 0)
                            end )
                (transfer_term bb.2 (state bb_id (length bb.1.2))).

Fixpoint abstract_interpret_inst_list {ab: Type} {ad: adom ab} {tf: transfer_function ad}
         (l: list Inst) (bb_id: bbid) (pos: nat) (state: AbstractState ab) :=
  match l with
  | nil => state
  | inst::l' => let new_ab := transfer_inst inst (state bb_id pos) in
              let new_state := (bb_id !-> (S pos !-> new_ab; state bb_id); state) in
              abstract_interpret_inst_list l' bb_id (S pos) new_state
  end.

Theorem abstract_interpret_inst_list_spec {ab: Type} {ad: adom ab} {tf: transfer_function ad} :
  forall(p: Program) bb bb_id, Some bb = p bb_id ->
      forall (l: list Inst) pos , (forall n, nth_error l n = nth_error bb.1.2 (n + pos)) ->
          forall state, (forall n', n' < pos -> inst_fixpoint p state bb_id n') ->
              forall n'', inst_fixpoint p (abstract_interpret_inst_list l bb_id pos state) bb_id n''.
Proof.
  move => p bb bb_id Hbb.
  elim => [ /= pos Hnth state Hfixpoint n''| inst l Hind pos Hnth state Hfixpoint n''].
  - case_eq (n'' < pos) => [/Hfixpoint // | /negb_true_iff Hge].
    rewrite /inst_fixpoint => bb0 Hbb0 inst Hinst.
    rewrite -leqNgt in Hge.
    apply subnK in Hge.
    move: Hnth => /(_ (n'' - pos)) Hnth.
    rewrite Hge in Hnth.
    rewrite -Hbb in Hbb0.
    move: Hbb0 => [Hbb0].
    rewrite -Hbb0 -Hinst /nth_error in Hnth.
    move: Hnth.
      by case (n'' - pos).
  - rewrite /=.
    apply Hind => [ n | n' Hn'ltpos1]. by rewrite addnS; apply (Hnth n.+1).
    case_eq (n' < pos) => [Heqn'pos | ].
    + move: (Heqn'pos).
      rewrite ltn_neqAle => /andP[Hnen'pos _].
      rewrite eq_sym in Hnen'pos.
      apply Hfixpoint in Heqn'pos.
      rewrite /inst_fixpoint in Heqn'pos.
      move => [bb0 term Hbb0 inst0 Hinst0 ].
      move: Heqn'pos => /(_ bb Hbb inst0) Heqn'pos.
      rewrite -Hbb in Hbb0.
      move: Hbb0 => [Hbb0].
      rewrite Hbb0 in Hinst0.
      move: Heqn'pos => /(_ Hinst0) Heqn'pos.
      rewrite ltn_neqAle in Hn'ltpos1.
      move: Hn'ltpos1 => /andP[Hn'nepos1 _].
        by simpl_totalmap.
    + move: (Hn'ltpos1).
      rewrite ltnS leq_eqVlt => /orP [ Heq _ | Hne Hne']; last first.
        by rewrite Hne' in Hne.
        rewrite !(eqP Heq).
        move => bb0 Hbb0 inst0 Hinst0.
        simpl_totalmap.
        rewrite t_update_neq; last first. by rewrite eq_sym; apply /eqP.
        move: (Hnth 0) => /= Hinst.
        rewrite -Hbb in Hbb0.
        move: Hbb0 => [Hbbbb0].
        rewrite Hbbbb0 in Hinst0.
        rewrite [pos]/(0 + pos) in Hinst0.
        rewrite -Hinst0 in Hinst.
        move: Hinst => [->].
        apply LAbstractDomain.le_refl.
Qed.

Theorem abstract_interpret_inst_list_0_unchanged {ab: Type} {ad: adom ab} {tf: transfer_function ad}
         (l: list Inst) (bb_id bb_id': bbid) (pos: nat) (state: AbstractState ab) :
  state bb_id' 0 = (abstract_interpret_inst_list l bb_id pos state) bb_id' 0.
Proof.
  elim: l state pos => [ // | i l Hind state pos /=].
  case (bb_id' =P bb_id) => [ Heq | /eqP Hne ].
  - rewrite Heq in Hind *.
    rewrite -Hind.
      by simpl_totalmap.
  - rewrite -Hind.
      by simpl_totalmap.
Qed.

Theorem abstract_interpret_inst_list_bb_unchanged {ab: Type} {ad: adom ab} {tf: transfer_function ad}
        (p: Program) (l: list Inst) (bb_id: bbid) :
  forall bb_id', bb_id != bb_id' ->
            forall state pos n, (abstract_interpret_inst_list l bb_id pos state) bb_id' n = state bb_id' n.
Proof.
  move => bb_id' Hbb_ne.
  elim: l => [ // | i l Hind state pos n /=].
  rewrite Hind.
    by simpl_totalmap.
Qed.

Definition abstract_interpret_join_term_succ {ab: Type} {ad: adom ab} {tf: transfer_function ad}
           (state: AbstractState ab) (abs: list (ab * bbid)) :=
    fold_right (fun abid state =>
               match abid with
               | (ab, out_id) => (out_id !-> (O !-> join ab (state out_id O); state out_id); state)
               end
              ) state abs.

Lemma abstract_interpret_join_term_unchanged {ab: Type} {ad: adom ab} {tf: transfer_function ad}
      (state: AbstractState ab) (abs: list (ab * bbid)) (bb_id: bbid) (pos: nat) :
  pos != O -> (abstract_interpret_join_term_succ state abs) bb_id pos = state bb_id pos.
Proof.
  move => Hpos.
  elim: abs => [ // | [a out_id] l Hind ].
  case (out_id =P bb_id) => [-> | Hne]; by simpl_totalmap.
Qed.

Lemma abstract_interpret_join_term_bb_unchanged {ab: Type} {ad: adom ab} {tf: transfer_function ad}
      (p: Program) (bb_id: bbid):
  forall abs, (forall a', not (In (a', bb_id) abs)) ->
         forall state pos, (abstract_interpret_join_term_succ state abs) bb_id pos = state bb_id pos.
Proof.
  move => HnotIn.
  elim: HnotIn => [// | [a out_id] abs' Hind /=].
  case (bb_id =P out_id) => [<- /(_ a) /Decidable.not_or [Himpossible _]// | Hne HnotIn].
  have: (forall a', ~ In (a', bb_id) abs').
    by move => a'; move: HnotIn => /(_ a') /Decidable.not_or[_ Hgoal].
  move => HnotIn' state pos.
  apply Hind with (state := state) (pos := pos) in HnotIn'.
    by simpl_totalmap.
Qed.

Lemma abstract_interpret_join_term_monotone {ab: Type} {ad: adom ab} {tf: transfer_function ad}
      (state: AbstractState ab) (abs: list (ab * bbid)) (bb_id: bbid) (pos: nat) :
  le (state bb_id pos) ((abstract_interpret_join_term_succ state abs) bb_id pos).
Proof.
  elim: abs => [ /= | [a' bb] l /=]. by apply LAbstractDomain.le_refl.
  case (bb_id =P bb) => [-> | Hne Hind].
  - case pos => [Hind | n Hind].
    + simpl_totalmap.
      eapply LAbstractDomain.le_trans.
      * by apply Hind.
      * apply join_sound_r.
    + by simpl_totalmap.
  - by simpl_totalmap.
Qed.

Lemma abstract_interpret_join_term_join {ab: Type} {ad: adom ab} {tf: transfer_function ad}
      (abs: list (ab * bbid)) (a: ab) (bb_id: bbid) :
  In (a, bb_id) abs ->
  forall state, le a ((abstract_interpret_join_term_succ state abs) bb_id O).
Proof.
  elim: abs => [// | [a0 out_id] l Hind /= [[-> ->] | HIn] state].
  - simpl_totalmap. apply join_sound_l.
  - case (out_id =P bb_id) => [-> | Hne].
    + simpl_totalmap.
      eapply LAbstractDomain.le_trans.
      * by apply Hind.
      * apply join_sound_r.
    + simpl_totalmap.
        by apply Hind.
Qed.

Definition abstract_interpret_term {ab: Type} {ad: adom ab} {tf: transfer_function ad}
           (bb: BasicBlock) (bb_id: bbid) (state: AbstractState ab) :=
  let pos := length bb.1.2 in
  let new_abs := transfer_term bb.2 (state bb_id pos) in
  abstract_interpret_join_term_succ state new_abs.


Theorem abstract_interpret_term_spec {ab: Type} {ad: adom ab} {tf: transfer_function ad}
        (p: Program) (bb: BasicBlock) (bb_id: bbid) (state: AbstractState ab):
  Some bb = p bb_id ->
  ~~(list_string_in (term_successors bb.2) bb_id) ->
  term_fixpoint p (abstract_interpret_term bb bb_id state) bb_id.
Proof.
  move => Hbb Hbbnotsucc.
  move => bb0 Hbb0.
  rewrite -Hbb0 in Hbb.
  move: Hbb Hbb0 => [<-] => Hbb.
  apply forallb_forall => [[a out_id]].
  rewrite /abstract_interpret_term.
  move Hterm: bb.2 => term.
  rewrite Hterm in Hbbnotsucc.
  move Hpos: (length bb.1.2) => pos.
  move Htransfer: (transfer_term term ((state bb_id) pos)) => transfer.
  case (pos =P 0) => [Heq | /eqP Hne]; last first.
  - rewrite abstract_interpret_join_term_unchanged => [ | //].
    rewrite Htransfer => HIn.
      by apply abstract_interpret_join_term_join.
  - rewrite Heq in Hpos Htransfer *.
    case (out_id =P bb_id) => [-> HIn | Hne ].
    + have: (list_string_in (term_successors term) bb_id) => [ | Hcontra].
      * eapply transfer_term_only_successors.
        exists a.
        by apply HIn.
      * rewrite /is_true in Hcontra.
          by rewrite Hcontra in Hbbnotsucc.
    + move: (@abstract_interpret_join_term_bb_unchanged ab ad tf p bb_id transfer).
      have: (forall a' : ab, ~ In (a', bb_id) transfer).
      * move => a' HIn.
        rewrite -Htransfer in HIn.
        move: (@transfer_term_only_successors ab ad tf term bb_id (state bb_id 0)).
        have: ((exists a'0 : ab, In (a'0, bb_id) (transfer_term term ((state bb_id) 0)))).
          by exists a'.
        move => HexistsIn /(_ HexistsIn).
        rewrite /is_true.
        move => HbbInsucc.
          by rewrite HbbInsucc in Hbbnotsucc.
      * move => HnotIn /(_ HnotIn) Hunchanged.
        rewrite Hunchanged Htransfer => HIn.
        by apply abstract_interpret_join_term_join.
Qed.

Lemma abstract_interpret_term_monotone {ab: Type} {ad: adom ab} {tf: transfer_function ad}
      (state: AbstractState ab) (bb: BasicBlock) (bb_id bb_id': bbid) (pos: nat) :
  le (state bb_id' pos) ((abstract_interpret_term bb bb_id state) bb_id' pos).
Proof.
  rewrite /abstract_interpret_term.
  by apply abstract_interpret_join_term_monotone.
Qed.


Lemma abstract_interpret_term_bb_unchanged {ab: Type} {ad: adom ab} {tf: transfer_function ad}
      (p: Program) (bb_id: bbid) (bb: BasicBlock):
  (Some bb = p bb_id) ->
  forall bb_id', bb_id' != bb_id ->
    ~~(list_string_in (term_successors bb.2) bb_id') ->
            forall state pos, (abstract_interpret_term bb bb_id state) bb_id' pos = state bb_id' pos.
Proof.
  move => Hbb bb_id' Hbb_ne Hbb_not_term state pos.
  rewrite /abstract_interpret_term.
  rewrite abstract_interpret_join_term_bb_unchanged => //.
  move => a' HIn.
  have: (list_string_in (term_successors bb.2) bb_id').
  - eapply transfer_term_only_successors.
    eauto.
  - move => Himpossible.
    unfold is_true in Himpossible.
      by rewrite Himpossible in Hbb_not_term.
Qed.

Definition abstract_interpret_bb {ab: Type} {ad: adom ab} {tf: transfer_function ad}
           (bb: BasicBlock) (bb_id: bbid) (state: AbstractState ab) :=
  let state' := abstract_interpret_inst_list bb.1.2 bb_id 0 state in
  abstract_interpret_term bb bb_id state'.

Theorem abstract_interpret_bb_spec_term {ab: Type} {ad: adom ab} {tf: transfer_function ad}
        (p: Program) (bb: BasicBlock) (bb_id: bbid) (state: AbstractState ab) :
    Some bb = p bb_id ->
    ~~(list_string_in (term_successors bb.2) bb_id) ->
    term_fixpoint p (abstract_interpret_bb bb bb_id state) bb_id.
Proof.
  move => Hbb HnotIn.
    by apply abstract_interpret_term_spec.
Qed.

Theorem abstract_interpret_bb_spec_inst {ab: Type} {ad: adom ab} {tf: transfer_function ad}
        (p: Program) (bb: BasicBlock) (bb_id: bbid) (state: AbstractState ab) :
    Some bb = p bb_id ->
    ~~(list_string_in (term_successors bb.2) bb_id) ->
    (forall n, inst_fixpoint p (abstract_interpret_bb bb bb_id state) bb_id n).
Proof.
  move => Hbb HnotIn n.
  rewrite /abstract_interpret_bb.
  assert (inst_fixpoint p (abstract_interpret_inst_list bb.1.2 bb_id 0 state) bb_id n).
  - eapply abstract_interpret_inst_list_spec => [ | n0 | n' Hn0].
      + by apply Hbb.
      + by rewrite addn0.
      + by rewrite ltn0 in Hn0.
  - move: H. case: n => [ H | n H] bb0 Hbb0 inst0 Hinst0; last first.
    + rewrite !abstract_interpret_join_term_unchanged => //.
      rewrite /inst_fixpoint in H.
      eapply H.
        by apply Hbb0.
        by apply Hinst0.
    + rewrite (abstract_interpret_join_term_unchanged _ _ _ 1) => //.
      rewrite /abstract_interpret_term.
      rewrite -Hbb in Hbb0. move: Hbb0 => [Hbbeq].
      rewrite !Hbbeq in Hinst0 *.
      rewrite (abstract_interpret_join_term_bb_unchanged p bb_id) => //.
      * eapply abstract_interpret_inst_list_spec with (p0 := p) (bb1 := bb) (bb2 := bb) => //.
          move => n. by rewrite addn0.
      * move => a' HIna'.
        have: (exists a'0 : ab, In (a'0, bb_id) (transfer_term bb.2
              (((abstract_interpret_inst_list bb.1.2 bb_id 0 state) bb_id) (Datatypes.length bb.1.2)))).
        by eexists; apply HIna'.
        move => HexistsIn.
        apply transfer_term_only_successors in HexistsIn.
          by rewrite HexistsIn in HnotIn.
Qed.

Theorem abstract_interpret_bb_monotone_0 {ab: Type} {ad: adom ab} {tf: transfer_function ad}
        (bb: BasicBlock) (bb_id bb_id': bbid) (state: AbstractState ab):
  le (state bb_id' 0) ((abstract_interpret_bb bb bb_id state) bb_id' 0).
Proof.
  rewrite /abstract_interpret_bb.
  erewrite abstract_interpret_inst_list_0_unchanged.
  apply abstract_interpret_term_monotone.
Qed.

Fixpoint abstract_interpret_program {ab: Type} {ad: adom ab} {tf: transfer_function ad}
           (p: Program) (ps: ProgramStructure) (state: AbstractState ab) :=
  match ps with
  | BB bb_id =>
    match p bb_id with
    | Some bb => abstract_interpret_bb bb bb_id state
    | None => state
    end
  | DAG ps1 ps2 =>
    let state' := abstract_interpret_program p ps1 state in
    abstract_interpret_program p ps2 state'
  | _ => state
  end.

Theorem abstract_interpret_program_monotone_0 {ab: Type} {ad: adom ab} {tf: transfer_function ad}
        (p: Program) (ps: ProgramStructure) (state: AbstractState ab) (bb_id: bbid) :
  le (state bb_id 0) ((abstract_interpret_program p ps state) bb_id 0).
Proof.
  elim: ps state.
  - admit.
  - move => ps1 Hind1 ps2 Hind2 state /=.
    eapply LAbstractDomain.le_trans.
    + by apply Hind1.
    + by apply Hind2.
  - rewrite /abstract_interpret_program => bb state.
    case: (p bb) => [a | ].
    + by apply abstract_interpret_bb_monotone_0.
    + by apply LAbstractDomain.le_refl.
Admitted.

Theorem abstract_interpret_program_unchanged {ab: Type} {ad: adom ab} {tf: transfer_function ad}
        (p: Program) (ps: ProgramStructure) :
  structure_sound p ps ->
  forall bb_id, ~~(list_string_in (program_successors p ps) bb_id) ->
            ~~(list_string_in (bbs_in_program ps) bb_id) ->
            forall state pos, (abstract_interpret_program p ps state) bb_id pos = state bb_id pos.
Proof.
  elim: ps.
  - admit.
  - move => ps1 Hind1 ps2 Hind2 /= /andP[/andP[_ Hsound1] Hsound2] bb_id.
    rewrite !list_string_in_append => /norP[Hinsucc1 Hinsucc2] /norP[Hinprog1 Hinprog2] state pos.
    rewrite Hind2 => //.
    by rewrite Hind1 => //.
  - move => bb_id Hsound bb_id' Hnot_in_succ /norP [/eqP Hnebb _] state pos /=.
    case_eq (p bb_id) => [[[params insts] term] | //] => Hbb.
    move => /eqP in Hnebb.
    rewrite /abstract_interpret_bb.
    erewrite abstract_interpret_term_bb_unchanged; eauto.
    rewrite abstract_interpret_inst_list_bb_unchanged => //. by rewrite eq_sym.
    rewrite /= in Hnot_in_succ.
    rewrite Hbb in Hnot_in_succ.
      by [].
Admitted.

Theorem abstract_interpret_program_spec_term {ab: Type} {ad: adom ab} {tf: transfer_function ad}
        (p: Program) (ps: ProgramStructure):
  structure_sound p ps ->
  forall bb_id, list_string_in (bbs_in_program ps) bb_id ->
           forall state, term_fixpoint p (abstract_interpret_program p ps state) bb_id.
Proof.
  elim ps => [ | | bb_id' /=].
  - admit.
  - move => ps1 Hind1 ps2 Hind2 /= /andP[/andP[/andP[/andP[/andP[H2notin1 H1notin2] Hloops] Hdominance] Hsound1] Hsound2] bb_id.
    rewrite list_string_in_append => /orP [ HIn1 | HIn2 ] state; last first.
      by apply Hind2.
    have: (term_fixpoint p (abstract_interpret_program p ps1 state) bb_id) by apply Hind1.
    move => Hfixpoint1.
    rewrite /term_fixpoint in Hfixpoint1 *.
    move => bb Hbb.
    apply forallb_forall => [[a bb_id']] HIn.
    rewrite abstract_interpret_program_unchanged in HIn => //.
    + move: (Hfixpoint1 bb Hbb) => {Hfixpoint1} Hfixpoint1.
      eapply forallb_forall with (x := (a, bb_id')) in Hfixpoint1; auto.
      eapply LAbstractDomain.le_trans.
      apply Hfixpoint1.
      apply abstract_interpret_program_monotone_0.
    + move: HIn1. move => /list_string_in_spec HIn1.
      apply /list_string_in_spec => Hinsucc2.
      rewrite /is_true in Hdominance.
      eapply forallb_forall in Hdominance; eauto.
      move: Hdominance => /list_string_in_spec Hdominance.
      eauto.
    + eapply forallb_forall in H2notin1; eauto.
      by apply /list_string_in_spec.
  - case_eq (p bb_id') => [ [[params insts] term] Hbb Hbbnotinterm bb_id /orP [/eqP ->| //] state /= | //].
      by apply abstract_interpret_bb_spec_term.
Admitted.
