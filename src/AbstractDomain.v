From Coq Require Import ssreflect ssrfun ssrbool.
Require Export Coq.Sets.Ensembles.
From Coq Require Import ssrbool.
From mathcomp Require Export eqtype.

(* The abstract domain *)
Class adom (concrete_state abstract_state: eqType) :=
  {
    le : abstract_state -> abstract_state -> bool;
    bot : abstract_state;
    top : abstract_state;
    join : abstract_state -> abstract_state -> abstract_state;

    gamma : abstract_state -> Ensemble concrete_state;

    le_refl: forall a, le a a;
    le_trans: forall a1 a2 a3, le a1 a2 -> le a2 a3 -> le a1 a3;
    gamma_monotone : forall a1 a2, le a1 a2 <-> Included concrete_state (gamma a1) (gamma a2);
    gamma_top : forall x, Ensembles.In concrete_state (gamma top) x;
    gamma_bot : forall x, ~ Ensembles.In concrete_state (gamma bot) x;
    join_spec : forall a1 a2 x, Ensembles.In concrete_state (gamma (join a1 a2)) x <->
                         Ensembles.In concrete_state (gamma a1) x \/
                         Ensembles.In concrete_state (gamma a2) x;
    join_sound_l : forall a1 a2, le a1 (join a1 a2);
    join_sound_r : forall a1 a2, le a2 (join a1 a2);
  }.

Hint Resolve le_refl gamma_monotone gamma_top join_sound_l join_sound_r : core.

Theorem le_join_l {concrete_state abstract_state: eqType} (ad: adom concrete_state abstract_state) :
  forall a1 a2 a3, le a1 a2 -> le a1 (join a2 a3).
Proof.
  move => a1 a2 a3 Hle.
  eapply le_trans.
  - apply Hle.
  - auto.
Qed.

Theorem le_join_r {concrete_state abstract_state: eqType} (ad: adom concrete_state abstract_state) :
  forall a1 a2 a3, le a1 a2 -> le a1 (join a3 a2).
Proof.
  move => a1 a2 a3 Hle.
  eapply le_trans.
  - apply Hle.
  - auto.
Qed.

Theorem le_bot {concrete_state abstract_state: eqType} (ad: adom concrete_state abstract_state) :
  forall a, le bot a.
Proof.
  move => a.
  apply gamma_monotone => R HIn. exfalso.
    by eapply gamma_bot; eauto.
Qed.

Hint Resolve le_join_l le_join_r le_bot : core.

