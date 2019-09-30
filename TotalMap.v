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


Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if x =? x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  auto.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros.
  unfold t_update.
  rewrite eqb_refl.
  reflexivity.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros.
  unfold t_update.
  rewrite <- eqb_neq in H.
  rewrite H.
  reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros.
  unfold t_update.
  extensionality x'.
  destruct (x =? x'); auto.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros.
  unfold t_update.
  extensionality x'.
  destruct (eqb_spec x x'); auto.
  rewrite e.
  auto.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros.
  unfold t_update.
  extensionality x'.
  destruct (eqb_spec x1 x'); auto.
  rewrite e in H.
  rewrite <- eqb_neq in H.
  rewrite H.
  auto.
Qed.

Require Import Coq.ZArith.BinInt.

Ltac simpl_totalmap :=
  repeat (
      rewrite ?t_apply_empty ?t_update_eq ?t_update_shadow ?t_update_same /=
    ).

Ltac simpl_totalmap_Z :=
  repeat ( simpl_totalmap; rewrite ?Z.eqb_refl ).
