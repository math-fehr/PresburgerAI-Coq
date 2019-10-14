From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Strings.String ZArith.BinInt.
From PolyAI Require Export TotalMap ssrZ.
Local Open Scope Z_scope.

Local Set Warnings "-notation-overridden".

Inductive V :=
| VTop
| VVal (n: Z)
| VBot.

Definition eq_V (v1 v2: V) :=
  match (v1, v2) with
  | (VTop, VTop) => true
  | (VBot, VBot) => true
  | (VVal v1, VVal v2) => v1 == v2
  | _ => false
  end.

Definition le_V (v1 v2: V) :=
  match (v1, v2) with
  | (_, VTop) => true
  | (VBot, _) => true
  | (VVal n1, VVal n2) => n1 == n2
  | _ => false
  end.

Theorem le_V_refl : forall v, (le_V v v).
Proof.
  case => // n.
  by apply Z.eqb_refl.
Qed.

Theorem le_V_trans :
  forall v1 v2 v3, le_V v1 v2 -> le_V v2 v3 -> le_V v1 v3.
Proof.
  move => v1 v2 v3.
  case v1; case v2; case v3 => //.
  rewrite /le_V.
  move => n3 n2 n1 /Z.eqb_spec H12 /Z.eqb_spec H23.
  rewrite H12 H23.
    by apply /Z.eqb_spec.
Qed.

Definition in_V (n: Z) (v: V) :=
  match v with
  | VTop => true
  | VVal n' => n == n'
  | VBot => false
  end.

Definition le_V_spec :
  forall v1 v2, le_V v1 v2 <-> forall n, in_V n v1 -> in_V n v2.
Proof.
  move => v1 v2.
  split.
  - case v1; case v2 => // n n0.
    rewrite /le_V => /Z.eqb_spec -> //.
  - case v1; case v2 => //.
    + move => n /= /(_ (n+1) is_true_true) /eqP Himpossible.
      by apply Z.neq_succ_diag_l in Himpossible.
    + move => Hle.
        by have /Hle : (in_V 0 VTop) by [] => Himpossible.
    + move => n n0 Hin.
      case (Z.eqb_spec n n0).
      * move => Heq.
          by rewrite Heq /le_V.
      * move => /Z.eqb_spec Hne.
        move: (Hin n0) => Himpossible.
        have /Himpossible : (in_V n0 (VVal n0)); by rewrite /in_V.
    + move => n Hin.
      move: (Hin n) => Hin'.
      have /Hin' : (in_V n (VVal n)). by rewrite /in_V.
        by move => Himpossible.
Qed.

Definition binop_V (v1 v2: V) (op: Z -> Z -> Z):=
  match (v1, v2) with
  | (VBot, _) | (_, VBot) => VBot
  | (VTop, _) | (_, VTop) => VTop
  | (VVal v1, VVal v2) => VVal (op v1 v2)
  end.

Definition add_V (v1 v2: V) :=
  binop_V v1 v2 Z.add.

Theorem add_V_spec :
  forall x1 v1, in_V x1 v1 ->
           forall x2 v2, in_V x2 v2 ->
                    in_V (x1 + x2) (add_V v1 v2).
Proof.
  move => x1 v1 H1 x2 v2 H2.
  rewrite /in_V /add_V /binop_V.
  case v1 eqn:Hv1; case v2 eqn:Hv2 => //.
  rewrite /= in H1 H2.
  by move: H1 H2 => /eqP -> /eqP ->.
Qed.

Definition sub_V (v1 v2: V) :=
  binop_V v1 v2 Z.sub.

Theorem sub_V_spec :
  forall x1 v1, in_V x1 v1 ->
           forall x2 v2, in_V x2 v2 ->
                    in_V (x1 - x2) (sub_V v1 v2).
Proof.
  move => x1 v1 H1 x2 v2 H2.
  rewrite /in_V /sub_V /binop_V.
  case v1 eqn:Hv1; case v2 eqn:Hv2 => //.
  rewrite /= in H1 H2.
  by move: H1 H2 => /eqP -> /eqP ->.
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
  case v1 eqn:Hv1; case v2 eqn:Hv2 => //.
  rewrite /= in H1 H2.
  by move: H1 H2 => /eqP -> /eqP ->.
Qed.

Definition unop_V (v: V) (op: Z -> Z) :=
  match v with
  | VVal v => VVal (op v)
  | other => other
  end.

Definition mul_V (z: Z) (v: V) :=
  unop_V v (fun v => z * v).

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
               if eq_V (eval_pfunc p m) (VVal v) then
                 VBot
               else
                 (eval_pfunc p m);
  }.

Theorem le_pfunc_refl {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a, le_pfunc a a.
Proof.
  move => a.
  apply le_pfunc_spec => x.
  apply le_V_refl.
Qed.

Theorem le_pfunc_trans {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a1 a2 a3, le_pfunc a1 a2 -> le_pfunc a2 a3 -> le_pfunc a1 a3.
Proof.
  move => a1 a2 a3 /le_pfunc_spec H12 /le_pfunc_spec H23.
  apply le_pfunc_spec => x.
    by apply (le_V_trans _ (eval_pfunc a2 x)).
Qed.

Theorem is_constant_on_var_update_spec {PFunc: Type} {PI: PFuncImpl PFunc} :
      forall p v, is_constant_on_var p v ->
             forall z m, eval_pfunc p (v !-> z; m) = eval_pfunc p m.
Proof.
  move => p v Hconst z m.
  apply (iffLR (is_constant_on_var_spec _ _)) with
        (m0 := eval_map m)
        (m' := eval_map (v !-> z; m))
      in Hconst => [ // | v' Hne ].
    by simpl_totalmap.
Qed.

(* A useful lemma used in the next tactic *)
Lemma t_update_other {Value: Type} (m : @total_map string_eqType Value):
    forall x v v', v != v' ->
              (v !-> x; m) v' = m v'.
Proof.
  move => x v v' Hne.
    by simpl_totalmap.
Qed.


Ltac simpl_pfunc :=
  repeat match goal with
         | [ |- context[le_V ?v ?v] ] => rewrite le_V_refl
         | [ |- context[eval_pfunc (constant_pfunc _)]] => rewrite constant_pfunc_spec
         | [ |- context[le_pfunc ?p (join_pfunc ?p _)]] => rewrite join_pfunc_spec_l
         | [ |- context[le_pfunc ?p (join_pfunc _ ?p)]] => rewrite join_pfunc_spec_r
         | [ |- context[le_pfunc ?p ?p]] => rewrite le_pfunc_refl
         | [ |- context[eval_pfunc (add_pfunc _ _) _]] => rewrite add_pfunc_spec
         | [ |- context[eval_pfunc (sub_pfunc _ _) _]] => rewrite sub_pfunc_spec
         | [ |- context[eval_pfunc (mul_pfunc _ _) _]] => rewrite mul_pfunc_spec
         | [ |- context[eval_pfunc (le_binop_pfunc _ _) _]] => rewrite le_binop_pfunc_spec
         | [ |- context[eval_pfunc (pfunc_restrict_eq_set _ _) _]] => rewrite pfunc_restrict_eq_set_spec
         | [ |- context[eval_pfunc (pfunc_restrict_ne_set _ _) _]] => rewrite pfunc_restrict_ne_set_spec
         | [ H: is_true (is_constant_on_var ?p ?v) |- context[eval_pfunc ?p (?v !-> ?z; ?m)]] =>
           rewrite (is_constant_on_var_update_spec p v H z m)
         | [ H: is_true (is_constant_on_var ?p ?v) |- context[eval_pfunc ?p (eval_map (?v !-> ?x; ?m))]] =>
           rewrite ((iffLR (is_constant_on_var_spec p v)) H (v !-> x; m) m (t_update_other m x v))
         | [ H1: is_true (in_V ?x1 ?v1), H2: is_true (in_V ?x2 ?v2) |- context[in_V (?x1 + ?x2) (add_V ?v1 ?v2)]] =>
           rewrite (add_V_spec x1 v1 H1 x2 v2 H2)
         | [ H1: is_true (in_V ?x1 ?v1), H2: is_true (in_V ?x2 ?v2) |- context[in_V (if (?x1 <=? ?x2)%Z then 1%Z else _) (le_binop_V ?v1 ?v2)]] =>
           rewrite (le_binop_V_spec x1 v1 H1 x2 v2 H2)
         | _ => simpl_totalmap
         end.
