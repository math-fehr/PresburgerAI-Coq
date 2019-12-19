From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Strings.String ZArith.BinInt.
From Coq Require Import Logic.FunctionalExtensionality.
From PolyAI Require Export TotalMap ssrZ ssrstring Tactic Presburger.
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

Theorem le_V_spec :
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

Definition join_V (v1 v2: V) :=
  match (v1, v2) with
  | (VBot, _) => v2
  | (_, VBot) => v1
  | (VTop, _) => VTop
  | (_, VTop) => VTop
  | (VVal z1, VVal z2) => if z1 == z2 then VVal z1 else VTop
  end.

Theorem join_V_leftP :
  forall v1 v2, le_V v1 (join_V v1 v2).
Proof.
  case => [ | n1 | ]; case => [ | n2 | ] => //=; rewrite /join_V /le_V //.
    by case (n1 =P n2).
Qed.

Theorem join_V_rightP :
  forall v1 v2, le_V v2 (join_V v1 v2).
Proof.
  case => [ | n1 | ]; case => [ | n2 | ] => //=; rewrite /join_V /le_V //.
  case (n1 =P n2); by autossr.
Qed.

Section PFuncDefinition.

  Context {PMap PSet PwAff: eqType}
          {PI: PresburgerImpl PMap PSet PwAff}.

  Record PFunc := mkPFunc {
    Val : PwAff;
    Assumed : PSet;
  }.

  Definition eval_pfunc (P: PFunc) (x: string -> Z) :=
    match (eval_pset (Assumed P) x, eval_pw_aff (Val P) x) with
    | (false, _ ) => VTop
    | (true, Some v) => VVal v
    | (true, None) => VBot
    end.

  Definition in_pfunc (P: PFunc) (m: string -> Z) (z: Z) :=
    in_V z (eval_pfunc P m).

  Definition constant_pfunc (v: V) :=
    match v with
    | VBot => mkPFunc empty_pw_aff universe_set
    | VTop => mkPFunc empty_pw_aff empty_set
    | VVal z => mkPFunc (pw_aff_from_aff (AConst z)) universe_set
    end.

  Theorem constant_pfuncP :
    forall v, eval_pfunc (constant_pfunc v) = (fun x => v).
  Proof.
      by case => [ | z | ]; rewrite /eval_pfunc /=; extensionality x; auto_presburger.
  Qed.

  Definition join_pfunc (p1 p2: PFunc) :=
    let assumed_inter := intersect_set (Assumed p1) (Assumed p2) in
    let assumed_join := subtract_set assumed_inter (ne_set (Val p1) (Val p2)) in
    let val_join := union_pw_aff (Val p1) (Val p2) in
    mkPFunc val_join assumed_join.

  Theorem join_pfuncP :
    forall p1 p2 x, eval_pfunc (join_pfunc p1 p2) x = join_V (eval_pfunc p1 x) (eval_pfunc p2 x).
  Proof.
    move => p1 p2 x. rewrite /join_pfunc /eval_pfunc /=. simpl_presburger.
    case: (eval_pset (Assumed p1) x); case: (eval_pset (Assumed p2) x);
    case (eval_pw_aff (Val p2) x); case (eval_pw_aff (Val p1) x) => //=.
      by move => z z0; case (z =P z0) => [ -> | ] /=; rewrite /join_V; autossr.
  Qed.

  Definition binop_pfunc (f: PwAff -> PwAff -> PwAff) (p1 p2: PFunc) :=
    let assumed_join := intersect_set (Assumed p1) (Assumed p2) in
    let val_join := f (Val p1) (Val p2) in
    mkPFunc val_join assumed_join.

  Definition add_pfunc :=
    binop_pfunc add_pw_aff.

  Theorem add_pfuncP :
    forall p1 x z1, in_pfunc p1 x z1 ->
               forall p2 z2, in_pfunc p2 x z2 ->
                        in_pfunc (add_pfunc p1 p2) x (z1 + z2).
  Proof.
    move => p1 x z1 Hin1 p2 z2. move: Hin1.
    rewrite /in_pfunc /add_pfunc /eval_pfunc /=.
    simpl_presburger.
    case: (eval_pset (Assumed p1)); case: (eval_pset (Assumed p2));
      case: (eval_pw_aff (Val p2) x); case: (eval_pw_aff (Val p1) x) => //=.
    by autossr.
  Qed.

  Definition le_binop_pfunc :=
    binop_pfunc (fun p1 p2 => indicator_function (le_set p1 p2)).

  Theorem le_binop_pfuncP :
    forall p1 x z1, in_pfunc p1 x z1 ->
               forall p2 z2, in_pfunc p2 x z2 ->
                        in_pfunc (le_binop_pfunc p1 p2) x (if z1 <=? z2 then 1 else 0).
  Proof.
    move => p1 x z1 Hin1 p2 z2. move: Hin1.
    rewrite /in_pfunc /add_pfunc /eval_pfunc /=.
    simpl_presburger.
    case: (eval_pset (Assumed p1)); case: (eval_pset (Assumed p2));
      case: (eval_pw_aff (Val p2) x); case: (eval_pw_aff (Val p1) x) => //=.
    move => a a0 /eqP -> /eqP ->. by case (a <=? a0).
  Qed.

End PFuncDefinition.

Definition eq_PFunc {PSet PwAff: eqType} (P1 P2: @PFunc PSet PwAff) :=
  (Val P1 == Val P2) && (Assumed P1 == Assumed P2).

Lemma eqPFuncP {PSet PwAff: eqType} : Equality.axiom (@eq_PFunc PSet PwAff).
Proof.
  rewrite /eq_PFunc => x y.
  case: x => Vx Ax. case: y => Vy Ay /=.
  case (Vx =P Vy); case (Ax =P Ay); intros; apply (iffP idP); autossr; by case.
Qed.

Canonical PFunc_eqType {PSet PwAff: eqType} := Eval hnf in EqType PFunc (EqMixin (@eqPFuncP PSet PwAff)).

Hint Rewrite @constant_pfuncP @join_pfuncP @join_V_leftP @join_V_rightP using by first [liassr | autossr] : pfuncrw.
Hint Resolve @add_pfuncP @le_binop_pfuncP : core.

Ltac simpl_pfunc_ := repeat (autorewrite with maprw; autorewrite with pfuncrw; simplssr).
Ltac simpl_pfunc := reflect_ne_in simpl_pfunc_.

Ltac auto_pfunc := intros; simpl_pfunc; autossr.
