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
