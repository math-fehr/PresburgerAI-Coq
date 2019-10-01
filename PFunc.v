From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Arith.Arith Strings.String.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.ssrnat.

Inductive V :=
| Top
| Val (n: nat)
| Bot.

Definition le_V (v1 v2: V) :=
  match (v1, v2) with
  | (_, Top) => true
  | (Bot, _) => true
  | (Val n1, Val n2) => n1 =? n2
  | _ => false
  end.

Class PFunc (pf: Type) :=
  {
    eval_pfunc : pf -> (string -> V) -> V;

    constant_pfunc : V -> pf;
    constant_pfunc_spec : forall v x, eval_pfunc (constant_pfunc v) x = v;

    le_pfunc : pf -> pf -> bool;
    le_pfunc_spec: forall p1 p2, le_pfunc p1 p2 <-> forall x, le_V (eval_pfunc p1 x) (eval_pfunc p2 x);

    join_pfunc : pf -> pf -> pf;
    join_pfunc_spec_l : forall p1 p2, le_pfunc p1 (join_pfunc p1 p2);
    join_pfunc_spec_r : forall p1 p2, le_pfunc p2 (join_pfunc p1 p2);
  }.
