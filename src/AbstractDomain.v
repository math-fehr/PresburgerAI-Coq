From PolyAI Require Export SSA Presburger.
Require Export Coq.Sets.Ensembles.
From Coq Require Import ssreflect ssrfun ssrbool.

(* The abstract domain *)
Class adom (ab:Type) :=
  {
    le : ab -> ab -> bool;
    bot : ab;
    top : ab;
    join : ab -> ab -> ab;

    gamma : ab -> Ensemble RegisterMap;

    le_refl: forall a, le a a;
    le_trans: forall a1 a2 a3, le a1 a2 -> le a2 a3 -> le a1 a3;
    gamma_monotone : forall a1 a2, le a1 a2 -> Included RegisterMap (gamma a1) (gamma a2);
    gamma_top : forall x, Ensembles.In RegisterMap (gamma top) x;
    join_sound_l : forall a1 a2, le a1 (join a1 a2);
    join_sound_r : forall a1 a2, le a2 (join a1 a2);
  }.
