From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Strings.String.
Local Set Warnings "-notation-overridden".
From mathcomp Require Export eqtype seq.
From PolyAI Require Import Tactic.

Local Open Scope string_scope.

(* Define a canonical structure for string with equality *)

Lemma eqstringP : Equality.axiom String.string_dec.
Proof.
  move => x y.
  by case (string_dec x y) => e /=; apply (iffP idP).
Qed.

Canonical string_eqType := Eval hnf in EqType string (EqMixin eqstringP).

Lemma ne_length_impl_ne :
  forall s1 s2, length s1 <> length s2 -> s1 <> s2.
Proof.
  move => s1 s2 HLength Heq.
  rewrite Heq in HLength.
    by case HLength.
Qed.

Lemma string_append_length :
  forall s1 s2, length (s1 ++ s2) = length s1 + length s2.
Proof.
  elim => [s2 // | a s1 Hind s2 /=].
    by rewrite Hind.
Qed.

Fixpoint repeat_string (n: nat) :=
  match n with
  | O => ""
  | S n' => "X" ++ (repeat_string n')
  end.

Lemma repeat_string_length :
  forall n, length (repeat_string n) = n.
Proof.
  elim => [// | n Hind /=].
  by auto.
Qed.

Fixpoint construct_not_in_list (l: list string) :=
  match l with
  | nil => "X"
  | a::l' => (repeat_string (length a)) ++ (construct_not_in_list l')
  end.

Lemma construct_not_in_list_length :
  forall l, 0 < length (construct_not_in_list l).
Proof.
  elim => [// | a l Hind /=].
  rewrite string_append_length.
  liassr.
Qed.

Theorem construct_not_in_list_length_forall :
  forall l x, x \in l -> length (construct_not_in_list l) > length x.
Proof.
  elim => [x Hin /= // | a l Hind x /=].
  rewrite in_cons => /orP [/eqP -> | Hinl].
  - rewrite string_append_length repeat_string_length.
    move: (construct_not_in_list_length l) => H.
    liassr.
  - rewrite string_append_length. move: (Hind x Hinl).
    by liassr.
Qed.

Theorem construct_not_in_list_spec:
  forall l, (construct_not_in_list l) \notin l.
Proof.
  move => l. apply /negP => HIn.
  apply construct_not_in_list_length_forall in HIn.
  by liassr.
Qed.
