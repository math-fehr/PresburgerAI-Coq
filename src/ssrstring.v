From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Strings.String.
Local Set Warnings "-notation-overridden".
From mathcomp Require Export eqtype.

Local Open Scope string_scope.

Lemma eqstringP : Equality.axiom String.eqb.
Proof.
  rewrite /Equality.axiom.
  elim => [ | a s Hind]; case => [ | a0 s0]; apply (iffP idP) => //.
  - simpl.
      by case_eq (Ascii.eqb a a0) => [/Ascii.eqb_eq -> /eqb_spec -> | ].
  - move ->.
      by apply eqb_refl.
Qed.

Canonical string_eqMixin := EqMixin eqstringP.
Canonical string_eqType := Eval hnf in EqType string string_eqMixin.
