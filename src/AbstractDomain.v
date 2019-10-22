Require Export Coq.Sets.Ensembles.
From Coq Require Import ssrbool.

(* The abstract domain *)
Class adom (concrete_state abstract_state: Type) :=
  {
    le : abstract_state -> abstract_state -> bool;
    bot : abstract_state;
    top : abstract_state;
    join : abstract_state -> abstract_state -> abstract_state;

    gamma : abstract_state -> Ensemble concrete_state;

    le_refl: forall a, le a a;
    le_trans: forall a1 a2 a3, le a1 a2 -> le a2 a3 -> le a1 a3;
    gamma_monotone : forall a1 a2, le a1 a2 -> Included concrete_state (gamma a1) (gamma a2);
    gamma_top : forall x, Ensembles.In concrete_state (gamma top) x;
    join_sound_l : forall a1 a2, le a1 (join a1 a2);
    join_sound_r : forall a1 a2, le a2 (join a1 a2);
  }.
