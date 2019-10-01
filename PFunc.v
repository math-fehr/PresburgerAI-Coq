From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Arith.Arith Strings.String.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.ssrnat.

Inductive V :=
| VTop
| VVal (n: nat)
| VBot.

Definition le_V (v1 v2: V) :=
  match (v1, v2) with
  | (_, VTop) => true
  | (VBot, _) => true
  | (VVal n1, VVal n2) => n1 =? n2
  | _ => false
  end.

Class PFuncImpl (PFunc: Type) :=
  {
    eval_pfunc : PFunc -> (string -> V) -> V;

    constant_pfunc : V -> PFunc;
    constant_pfunc_spec : forall v x, eval_pfunc (constant_pfunc v) x = v;

    le_pfunc : PFunc -> PFunc -> bool;
    le_pfunc_spec: forall p1 p2, le_pfunc p1 p2 <-> forall x, le_V (eval_pfunc p1 x) (eval_pfunc p2 x);

    join_pfunc : PFunc -> PFunc -> PFunc;
    join_pfunc_spec_l : forall p1 p2, le_pfunc p1 (join_pfunc p1 p2);
    join_pfunc_spec_r : forall p1 p2, le_pfunc p2 (join_pfunc p1 p2);
  }.
