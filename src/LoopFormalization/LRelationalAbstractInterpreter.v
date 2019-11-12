From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat.
From PolyAI.LoopFormalization Require Export LRTransferFunction LSSA.
From Coq Require Import Lists.List.

Require Import Lia.

Section AbstractInterpreter.

  Context {ab: Type}
          {ad: adom (RegisterMap * RegisterMap) ab}
          (tf: transfer_function_relational ad)
          (p: Program).

  (* Associate for every control location an abstract state *)
  Definition AbstractState : Type := @total_map bbid_eqType (@total_map nat_eqType ab).

  Definition inst_fixpoint (state: AbstractState) (bb_id: bbid) (pos: nat) :=
    if p bb_id is Some bb then
      if nth_error bb.1.2 pos is Some inst then
        le (transfer_inst inst (state bb_id pos)) (state bb_id (S pos))
      else
        true
    else
      true.

  Definition term_fixpoint (state: AbstractState) (bb_id: bbid) :=
    if p bb_id is Some bb then
      forallb (fun abbbid => match abbbid with
                          | (ab, out_id) => le ab (state out_id 0)
                          end)
              (transfer_term bb.2 (state bb_id (length bb.1.2)))
    else
      true.

  Fixpoint abstract_interpret_inst_list (state: AbstractState) (l: list Inst) (bb_id: bbid) (pos: nat) :=
    match l with
    | nil => state
    | inst::l' => let new_ab := transfer_inst inst (state bb_id pos) in
                let new_state := (bb_id !-> (S pos !-> new_ab; state bb_id); state) in
                abstract_interpret_inst_list new_state l' bb_id (S pos)
    end.

  Theorem abstract_interpret_inst_list_spec (bb: BasicBlock) (bb_id: bbid):
    Some bb = p bb_id ->
    forall (l: list Inst) pos, (forall n, nth_error l n = nth_error bb.1.2 (n + pos)) ->
      forall state, (forall n', n' < pos -> inst_fixpoint state bb_id n') ->
        forall n'', inst_fixpoint (abstract_interpret_inst_list state l bb_id pos) bb_id n''.
  Proof.
    move => Hbb.
    elim => [ /= pos Hnth state Hfixpoint n''| inst l Hind pos Hnth state Hfixpoint n'' /=].
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
        rewrite eq_sym in Hnen'pos.
        rewrite eq_sym in Hnen'pos2.
          by simpl_totalmap.
      + move: (Hn'ltpos1).
        rewrite ltnS leq_eqVlt => /orP [ Heq _ | Hne Hne']; last first. by rewrite Hne' in Hne.
        rewrite !(eqP Heq).
        rewrite /inst_fixpoint -Hbb.
        rewrite -(Hnth 0) /=.
        simpl_totalmap.
        rewrite t_update_neq. by apply AbstractDomain.le_refl.
        rewrite eq_sym.
        apply /eqP.
        auto.
  Qed.

End AbstractInterpreter.
