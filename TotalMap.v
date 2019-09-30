From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Import Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
From Coq Require Import ssreflect ssrfun ssrbool.

(* This code was taken from the programming language fundations book
 and was modified a bit *)

Local Open Scope string_scope.

(* _____     _        _ __  __             *)
(*|_   _|__ | |_ __ _| |  \/  | __ _ _ __  *)
(*  | |/ _ \| __/ _` | | |\/| |/ _` | '_ \ *)
(*  | | (_) | || (_| | | |  | | (_| | |_) |*)
(*  |_|\___/ \__\__,_|_|_|  |_|\__,_| .__/ *)
(*                                  |_|    *)

Inductive total_map (A: Type) :=
| TEmpty (v: A)
| TUpdate (m: total_map A) (x: string) (v: A)
.

Fixpoint eval_map {A: Type} (m: total_map A) (x: string) :=
  match m with
  | TEmpty _ v => v
  | TUpdate _ m' x' v => if x' =? x then v else eval_map m' x
  end.

Definition t_empty {A: Type} (v: A) :=
  TEmpty _ v.

Notation "'_' '!->' v" := (TEmpty _ v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (TUpdate _ m x v)
                              (at level 100, v at next level, right associativity).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    eval_map (_ !-> v) x = v.
Proof.
  by [].
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    eval_map (x !-> v ; m) x = v.
Proof.
  move => A m x v /=.
  by rewrite eqb_refl.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    eval_map (x1 !-> v ; m) x2 = eval_map m x2.
Proof.
  by move => A m x1 x2 v /eqb_neq /= ->.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    forall x', eval_map (x !-> v2 ; x !-> v1 ; m) x' = eval_map (x !-> v2 ; m) x'.
Proof.
  move => A m x v1 v2 x' /=.
  by case (x =? x').
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    forall x', eval_map (x !-> eval_map m x ; m) x' = eval_map m x'.
Proof.
  move => A m x x' /=.
  by case (eqb_spec x x') => [<- | _].
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    forall x', eval_map (x1 !-> v1 ; x2 !-> v2 ; m) x' =
          eval_map (x2 !-> v2 ; x1 !-> v1 ; m) x'.
Proof.
  move => A m v1 v2 x1 x2 /eqb_neq Hne x'.
  case (eqb_spec x1 x') => [ <- /= | ].
  - by rewrite eqb_refl Hne.
  - move=> /eqb_neq Hne' /=.
    by rewrite Hne'.
Qed.

Require Import Coq.ZArith.BinInt.

Ltac simpl_totalmap :=
  repeat (
      rewrite ?t_apply_empty ?t_update_eq ?t_update_shadow ?t_update_same ?eqb_refl%string /=
    ).

Ltac simpl_totalmap_Z :=
  repeat ( simpl_totalmap; rewrite ?Z.eqb_refl ).
