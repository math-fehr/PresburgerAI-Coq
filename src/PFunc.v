From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Strings.String ZArith.BinInt.
From PolyAI Require Export TotalMap ssrZ ssrstring.
Local Open Scope Z_scope.

Local Set Warnings "-notation-overridden".

(* V represent either an element in Z, no element, or all values in Z *)
Inductive V :=
| VTop
| VVal (n: Z)
| VBot.

Definition eqV (v1 v2: V) :=
  match (v1, v2) with
  | (VTop, VTop) => true
  | (VBot, VBot) => true
  | (VVal v1, VVal v2) => v1 == v2
  | _ => false
  end.

Lemma eqVP : Equality.axiom eqV.
Proof.
  case => [ | z1 | ]; case => [ | z2 | ]; apply (iffP idP) => //.
  - by rewrite /eqV => /eqP ->.
  - rewrite /eqV => [[->]].
      by auto.
Qed.

(* Canonical structure for V with ewuality *)

Canonical V_eqMixin := EqMixin eqVP.
Canonical V_eqType := Eval hnf in EqType V V_eqMixin.

(* Some useful definitions and proofs dealing with V *)

Definition in_V (n: Z) (v: V) :=
  match v with
  | VTop => true
  | VVal n' => n == n'
  | VBot => false
  end.

Definition le_V (v1 v2: V) :=
  match (v1, v2) with
  | (_, VTop) => true
  | (VBot, _) => true
  | (VVal n1, VVal n2) => n1 == n2
  | _ => false
  end.
Hint Unfold le_V: PFuncHint.

Theorem le_V_refl : forall v, (le_V v v).
Proof.
  case => // n.
  by apply eq_refl.
Qed.

Theorem le_V_trans :
  forall v1 v2 v3, le_V v1 v2 -> le_V v2 v3 -> le_V v1 v3.
Proof.
  move => v1 v2 v3.
  case v1; case v2; case v3 => //.
  rewrite /le_V => n3 n2 n1 /eqP H12 /eqP H23.
  rewrite H12 H23.
    by apply /eqP.
Qed.

Definition le_V_spec :
  forall v1 v2, le_V v1 v2 <-> forall n, in_V n v1 -> in_V n v2.
Proof.
  move => v1 v2.
  split. by case v1; case v2 => // n n0; rewrite /le_V => /eqP -> //.
  case v1; case v2 => //.
  - move => n /= /(_ (n+1) is_true_true) /eqP Himpossible.
      by apply Z.neq_succ_diag_l in Himpossible.
  - move => /= /(_ 0).
      by auto.
  - move => n n0 Hin.
    case (n =P n0) => [ -> | ].
    + by rewrite /le_V.
    + move => /eqP Hne.
      by move: (Hin n0) => /= /(_ (eq_refl n0)) Himpossible.
  - by move => n /(_ n (eq_refl n)) Hin.
Qed.

Definition binop_V (v1 v2: V) (op: Z -> Z -> Z):=
  match (v1, v2) with
  | (VBot, _) | (_, VBot) => VBot
  | (VTop, _) | (_, VTop) => VTop
  | (VVal v1, VVal v2) => VVal (op v1 v2)
  end.

Definition add_V v1 v2 :=
  binop_V v1 v2 Z.add.

Theorem add_V_spec :
  forall x1 v1, in_V x1 v1 ->
           forall x2 v2, in_V x2 v2 ->
                    in_V (x1 + x2) (add_V v1 v2).
Proof.
  move => x1 v1 H1 x2 v2 H2.
  rewrite /in_V /binop_V.
  by case: v1 H1 H2; case v2 => //= n n0 /eqP -> /eqP ->.
Qed.

Definition sub_V v1 v2 :=
  binop_V v1 v2 Z.sub.

Theorem sub_V_spec :
  forall x1 v1, in_V x1 v1 ->
           forall x2 v2, in_V x2 v2 ->
                    in_V (x1 - x2) (sub_V v1 v2).
Proof.
  move => x1 v1 H1 x2 v2 H2.
  rewrite /in_V /binop_V.
  by case: v1 H1 H2; case v2 => //= n n0 /eqP -> /eqP ->.
Qed.

Definition le_binop_V (v1 v2: V) :=
  binop_V v1 v2 (fun v1 v2 => if v1 <=? v2 then 1 else 0).

Theorem le_binop_V_spec :
  forall x1 v1, in_V x1 v1 ->
           forall x2 v2, in_V x2 v2 ->
                    in_V (if x1 <=? x2 then 1 else 0) (le_binop_V v1 v2).
Proof.
  move => x1 v1 H1 x2 v2 H2.
  rewrite /in_V /le_binop_V /binop_V.
  by case: v1 H1 H2; case v2 => //= n n0 /eqP -> /eqP ->.
Qed.

Definition unop_V (v: V) (op: Z -> Z) :=
  match v with
  | VVal v => VVal (op v)
  | other => other
  end.

Definition mul_V (z: Z) (v: V) :=
  unop_V v (fun v => z * v).

Hint Resolve le_V_refl add_V_spec sub_V_spec le_binop_V_spec: PFuncHint.

(* Specification of a PFunc *)

Class PFuncImpl (PFunc: Type) :=
  {
    eval_pfunc : PFunc -> (string -> V) -> V;

    constant_pfunc : V -> PFunc;
    constant_pfunc_spec : forall v, eval_pfunc (constant_pfunc v) = (fun x => v);

    le_pfunc : PFunc -> PFunc -> bool;
    le_pfunc_spec: forall p1 p2, le_pfunc p1 p2 <-> forall x, le_V (eval_pfunc p1 x) (eval_pfunc p2 x);

    join_pfunc : PFunc -> PFunc -> PFunc;
    join_pfunc_spec_l : forall p1 p2, le_pfunc p1 (join_pfunc p1 p2);
    join_pfunc_spec_r : forall p1 p2, le_pfunc p2 (join_pfunc p1 p2);

    is_constant_on_var: PFunc -> string -> bool;
    is_constant_on_var_spec:
      forall p v, is_constant_on_var p v <->
             forall m m', (forall v', v != v' -> m v' = m' v') -> eval_pfunc p m = eval_pfunc p m';

    add_pfunc: PFunc -> PFunc -> PFunc;
    add_pfunc_spec:
      forall p1 p2 x, eval_pfunc (add_pfunc p1 p2) x =
                 add_V (eval_pfunc p1 x) (eval_pfunc p2 x);

    sub_pfunc: PFunc -> PFunc -> PFunc;
    sub_pfunc_spec:
      forall p1 p2 x, eval_pfunc (sub_pfunc p1 p2) x =
                 sub_V (eval_pfunc p1 x) (eval_pfunc p2 x);

    mul_pfunc: Z -> PFunc -> PFunc;
    mul_pfunc_spec:
      forall n p x, eval_pfunc (mul_pfunc n p) x =
               mul_V n (eval_pfunc p x);

    le_binop_pfunc: PFunc -> PFunc -> PFunc;
    le_binop_pfunc_spec:
      forall p1 p2 x, eval_pfunc (le_binop_pfunc p1 p2) x =
                 le_binop_V (eval_pfunc p1 x) (eval_pfunc p2 x);

    pfunc_restrict_eq_set: PFunc -> Z -> PFunc;
    pfunc_restrict_eq_set_spec:
      forall p m v, eval_pfunc (pfunc_restrict_eq_set p v) m =
                 if in_V v (eval_pfunc p m) then
                   VVal v
                 else
                   VBot;

    pfunc_restrict_ne_set: PFunc -> Z -> PFunc;
    pfunc_restrict_ne_set_spec:
      forall p m v, eval_pfunc (pfunc_restrict_ne_set p v) m =
               if (eval_pfunc p m) == (VVal v) then
                 VBot
               else
                 (eval_pfunc p m);
  }.

Hint Resolve le_pfunc_spec join_pfunc_spec_l join_pfunc_spec_r: PFuncHint.

Theorem le_pfunc_refl {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a, le_pfunc a a.
Proof.
  move => a.
  apply le_pfunc_spec => x.
  by auto with PFuncHint.
Qed.

Theorem le_pfunc_trans {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a1 a2 a3, le_pfunc a1 a2 -> le_pfunc a2 a3 -> le_pfunc a1 a3.
Proof.
  move => a1 a2 a3 /le_pfunc_spec H12 /le_pfunc_spec H23.
  apply le_pfunc_spec => x.
  by eapply le_V_trans.
Qed.

Theorem is_constant_on_var_update_spec {PFunc: Type} {PI: PFuncImpl PFunc} :
      forall p v, is_constant_on_var p v ->
             forall z m, eval_pfunc p (v !-> z; m) = eval_pfunc p m.
Proof.
  move => p v Hconst z m.
  eapply is_constant_on_var_spec; eauto.
  by auto_map.
Qed.

(* A useful lemma used in the next tactic *)
Lemma t_update_other {Value: Type} (m : @total_map string_eqType Value):
    forall x v v', v != v' ->
              (v !-> x; m) v' = m v'.
Proof.
  by auto_map.
Qed.
