From PolyAI Require Export Presburger AbstractDomain.
Require Import PolyAI.SSA.
Require Export Coq.Sets.Ensembles.
From Coq Require Import ssreflect ssrfun ssrbool.

Require Import String.
Open Scope string_scope.


Theorem gamma_presburger_monotone {PSet PwAff: Type} {P : PresburgerImpl PSet PwAff} :
  forall p1 p2, is_subset p1 p2 ->
           Included (total_map Z)
                    (fun x => eval_set p1 x)
                    (fun x => eval_set p2 x).
Proof.
  move => p1 p2 /is_subset_spec Hsubset x Hin.
  rewrite /Ensembles.In in Hin *.
  by apply Hsubset, Hin.
Qed.

Theorem gamma_presburger_top {PSet PwAff: Type} {P : PresburgerImpl PSet PwAff} :
  forall x, Ensembles.In (total_map Z) (fun x => eval_set universe_set x) x.
Proof.
  move => x.
  rewrite /Ensembles.In.
  by simpl_eval_presburger.
Qed.

Instance PresburgerSetAD {PSet PwAff: Type} (PI : PresburgerImpl PSet PwAff) : adom PSet :=
  {
    le := is_subset;
    bot := empty_set;
    top := universe_set;
    join := union_set;

    gamma := fun p x => eval_set p x;

    le_refl := is_subset_refl;
    le_trans := is_subset_trans;
    gamma_monotone := gamma_presburger_monotone;
    gamma_top := gamma_presburger_top;
    join_sound_l := is_subset_union_l;
    join_sound_r := is_subset_union_r;
  }.
