Require Export PolyAI.TotalMap.
Require Export Coq.Sets.Ensembles.
Require Import PolyAI.SSA.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
From Coq Require Import ssreflect ssrfun ssrbool.

Require Import String.
Open Scope string_scope.

(* The abstract domain *)
Class adom (ab:Type) :=
  {
    le : ab -> ab -> bool;
    top : ab;
    join : ab -> ab -> ab;

    le_refl: forall a, le a a = true;
    le_trans: forall a1 a2 a3, le a1 a2 = true -> le a2 a3 = true -> le a1 a3 = true;
    gamma : ab -> Ensemble RegisterMap;
    gamma_monotone : forall a1 a2, le a1 a2 = true -> Included RegisterMap (gamma a1) (gamma a2);
    gamma_top : forall x, Ensembles.In RegisterMap (gamma top) x;
    join_sound_l : forall a1 a2, le a1 (join a1 a2);
    join_sound_r : forall a1 a2, le a2 (join a1 a2);
  }.

(* Transfer functions for our language *)
Class transfer_function {ab: Type} (A: adom ab) :=
  {
    transfer : SSA -> ab -> label -> list (ab * label);
    transfer_sound :
      forall prog R l R' l',
        step prog (R, l) (R', l') ->
        forall a, Ensembles.In RegisterMap (gamma a) R ->
        exists a', In (a', l') (transfer (List.nth l prog (Const "X" 0)) a l) /\
              Ensembles.In RegisterMap (gamma a') R'
  }.

