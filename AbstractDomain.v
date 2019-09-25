Require Import PolyAI.SSA.
Require Export PolyAI.Presburger.
Require Export Coq.Sets.Ensembles.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
From Coq Require Import ssreflect ssrfun ssrbool.

Require Import String.
Open Scope string_scope.

(* The abstract domain *)
Class adom (ab:Type) :=
  {
    le : ab -> ab -> bool;
    bot : ab;
    top : ab;
    join : ab -> ab -> ab;

    gamma : ab -> Ensemble RegisterMap;

    le_refl: forall a, le a a = true;
    le_trans: forall a1 a2 a3, le a1 a2 = true -> le a2 a3 = true -> le a1 a3 = true;
    gamma_monotone : forall a1 a2, le a1 a2 = true -> Included RegisterMap (gamma a1) (gamma a2);
    gamma_top : forall x, Ensembles.In RegisterMap (gamma top) x;
    join_sound_l : forall a1 a2, le a1 (join a1 a2);
    join_sound_r : forall a1 a2, le a2 (join a1 a2);
  }.


(* Instance for the polyhedral abstract domain *)

Theorem gamma_presburger_monotone {s: Type} (P : PresburgerSet s) :
  forall p1 p2, is_subset p1 p2 = true ->
           Included (string -> nat)
                    (fun x => eval_point p1 x = true)
                    (fun x => eval_point p2 x = true).
Proof.
  move => p1 p2 /is_subset_spec Hsubset x Hin.
  rewrite /Ensembles.In in Hin *.
  by apply Hsubset, Hin.
Qed.

Theorem gamma_presburger_top {s: Type} (P : PresburgerSet s) :
  forall x, Ensembles.In (string -> nat) (eval_point universe_set) x.
Proof.
  move => x.
  rewrite /Ensembles.In.
  apply universe_set_spec.
Qed.

Instance PresburgerSetAD {s: Type} (P : PresburgerSet s) : adom s :=
  {
    le := is_subset;
    bot := empty_set;
    top := universe_set;
    join := union_set;

    gamma := eval_point;

    le_refl := is_subset_refl P;
    le_trans := is_subset_trans P;
    gamma_monotone := gamma_presburger_monotone P;
    gamma_top := gamma_presburger_top P;
    join_sound_l := is_subset_union_l P;
    join_sound_r := is_subset_union_r P;
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

