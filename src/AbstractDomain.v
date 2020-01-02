From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Ensembles.
From Coq Require Import ssrbool.
From mathcomp Require Export eqtype.
From PolyAI Require Export LSSA.

(* The abstract domain *)
Class adom (concrete_state abstract_state: eqType) (p: Program) :=
  {
    bot : abstract_state;
    top : abstract_state;
    join : abstract_state -> abstract_state -> abstract_state;

    gamma : abstract_state -> Ensemble concrete_state;

    gamma_top : forall x, Ensembles.In concrete_state (gamma top) x;
    gamma_bot : forall x, ~ Ensembles.In concrete_state (gamma bot) x;
    join_sound_l : forall a1 a2, Included _ (gamma a1) (gamma (join a1 a2));
    join_sound_r : forall a1 a2, Included _ (gamma a2) (gamma (join a1 a2));
  }.

Hint Resolve gamma_top join_sound_l join_sound_r : core.

Section AbstractDomainTheorems.

  Context {concrete_state abstract_state: eqType}
          {p: Program}
          {ad: adom concrete_state abstract_state p}.

  Definition le := (fun a1 a2 => Included _ (gamma a1) (gamma a2)).

  Theorem le_refl :
    forall a, le a a.
  Proof.
    move => a.
      by rewrite /le /Included.
  Qed.

  Theorem le_trans :
    forall a1 a2 a3, le a1 a2 -> le a2 a3 -> le a1 a3.
  Proof.
    move => a1 a2 a3 Hle1 Hle2 x Hin1.
      by auto.
  Qed.

  Theorem le_join_l :
    forall a1 a2 a3, le a1 a2 -> le a1 (join a2 a3).
  Proof.
    move => /= a1 a2 a3 Hle.
    eapply le_trans. apply Hle.
    by apply join_sound_l.
  Qed.

  Theorem le_join_r :
    forall a1 a2 a3, le a1 a2 -> le a1 (join a3 a2).
  Proof.
    move => a1 a2 a3 Hle.
    eapply le_trans. by apply Hle.
    by apply join_sound_r.
  Qed.

  Theorem le_bot :
    forall a, le bot a.
  Proof.
    move => a x Hin.
      by apply gamma_bot in Hin.
  Qed.

End AbstractDomainTheorems.

Hint Resolve le_refl le_join_l le_join_r le_bot : core.
