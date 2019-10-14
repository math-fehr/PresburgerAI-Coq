Local Set Warnings "-notation-overridden".
From mathcomp Require Export eqtype.
Require Export Coq.ZArith.BinInt.

Canonical Z_eqMixin := EqMixin Z.eqb_spec.
Canonical Z_eqType := Eval hnf in EqType Z Z_eqMixin.
