Require Export PolyAI.SSA.
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

Theorem gamma_presburger_monotone {PSet PwAff: Type} {P : PresburgerImpl PSet PwAff} :
  forall p1 p2, is_subset p1 p2 = true ->
           Included (total_map Z)
                    (fun x => eval_set p1 x = true)
                    (fun x => eval_set p2 x = true).
Proof.
  move => p1 p2 /is_subset_spec Hsubset x Hin.
  rewrite /Ensembles.In in Hin *.
  by apply Hsubset, Hin.
Qed.

Theorem gamma_presburger_top {PSet PwAff: Type} {P : PresburgerImpl PSet PwAff} :
  forall x, Ensembles.In (total_map Z) (fun x => eval_set universe_set x = true) x.
Proof.
  move => x.
  rewrite /Ensembles.In.
  apply universe_set_spec.
Qed.

Instance PresburgerSetAD {PSet PwAff: Type} (P : PresburgerImpl PSet PwAff) : adom PSet :=
  {
    le := is_subset;
    bot := empty_set;
    top := universe_set;
    join := union_set;

    gamma := fun p x => eval_set p x = true;

    le_refl := is_subset_refl;
    le_trans := is_subset_trans;
    gamma_monotone := gamma_presburger_monotone;
    gamma_top := gamma_presburger_top;
    join_sound_l := is_subset_union_l;
    join_sound_r := is_subset_union_r;
  }.
