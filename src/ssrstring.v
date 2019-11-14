From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Strings.String.
Local Set Warnings "-notation-overridden".
From mathcomp Require Export eqtype.

Local Open Scope string_scope.

(* Define a canonical structure for string with equality *)

Lemma eqstringP : Equality.axiom String.string_dec.
Proof.
  move => x y.
  by case (string_dec x y) => e /=; apply (iffP idP).
Qed.

Canonical string_eqMixin := EqMixin eqstringP.
Canonical string_eqType := Eval hnf in EqType string string_eqMixin.
