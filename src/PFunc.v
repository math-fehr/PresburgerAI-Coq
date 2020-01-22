From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Export Strings.String ZArith.BinInt.
From Coq Require Import Logic.FunctionalExtensionality.
From PolyAI Require Export TotalMap ssrZ ssrstring Tactic FinitePresburger.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat.
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

Notation "z \inV v" := (in_V z v) (at level 70, no associativity).

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
  forall v1 v2, le_V v1 v2 <-> forall n, n \inV v1 -> n \inV v2.
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

Module PFuncImpl (FPI: FPresburgerImpl).
  Import FPI.

  Record PFunc (n: nat) := mkPFunc {
    Val : PwAff n;
    Assumed : PSet n;
  }.
  Arguments Val {n}.
  Arguments Assumed {n}.
  Arguments mkPFunc {n}.

  Definition eval_pfunc {n: nat} (P: PFunc n) (x: seq Z) :=
    match (x \ins (Assumed P), f_eval_pw_aff (Val P) x) with
    | (false, _ ) => VTop
    | (true, Some v) => VVal v
    | (true, None) => VBot
    end.

  Theorem eval_pfunc_same :
    forall n P x y, point_equality n x y ->
               @eval_pfunc n P x = @eval_pfunc n P y.
  Proof.
    move => n P x y Heq. rewrite /eval_pfunc.
    by rewrite_point x y.
  Qed.

  Ltac rewrite_point_pfunc_aux x1 x2 n H :=
    rewrite ?(eval_pfunc_same _ _ x1 x2 H);
    rewrite_point_aux x1 x2 n H.

  Ltac rewrite_point x1 x2 ::= rewrite_point_tac x1 x2 rewrite_point_pfunc_aux.

  Ltac rewrite_point_H H ::= rewrite_point_H_tac H rewrite_point_pfunc_aux.

  Definition in_pfunc {n: nat} (P: PFunc n) (m: seq Z) (z: Z) :=
    z \inV (eval_pfunc P m).

  Definition constant_pfunc (n: nat) (v: V) :=
    match v with
    | VBot => mkPFunc (f_empty_pw_aff n) (f_universe_set n)
    | VTop => mkPFunc (f_empty_pw_aff n) (f_empty_set n)
    | VVal z => mkPFunc (f_pw_aff_from_aff (FAConst n z)) (f_universe_set n)
    end.

  Theorem constant_pfuncP :
    forall n v, eval_pfunc (constant_pfunc n v) = (fun x => v).
  Proof.
    move => n.
    by case => [ | z | ]; rewrite /eval_pfunc /=; extensionality x; auto_finite_presburger.
  Qed.

  Definition constant_var_pfunc (n var: nat) :=
    mkPFunc (f_pw_aff_from_aff (FAVar n var)) (f_universe_set n).

  Theorem constant_var_pfuncP :
    forall n v, eval_pfunc (constant_var_pfunc n v) = (fun x => VVal (nth 0 x v)).
  Proof.
    move => n v. rewrite /eval_pfunc /=.
    extensionality x.
    by auto_finite_presburger.
  Qed.

  Definition join_pfunc {n: nat} (p1 p2: PFunc n) :=
    let assumed_inter := f_intersect_set (Assumed p1) (Assumed p2) in
    let assumed_join := f_subtract_set assumed_inter (f_ne_set (Val p1) (Val p2)) in
    let val_join := f_union_pw_aff (Val p1) (Val p2) in
    mkPFunc val_join assumed_join.

  Theorem join_pfuncP :
    forall n {p1 p2: PFunc n} x, eval_pfunc (join_pfunc p1 p2) x = join_V (eval_pfunc p1 x) (eval_pfunc p2 x).
  Proof.
    move => n p1 p2 x. rewrite /join_pfunc /eval_pfunc /=. simpl_finite_presburger.
    case: (x \ins (Assumed p1)); case: (x \ins (Assumed p2));
    case (f_eval_pw_aff (Val p2) x); case (f_eval_pw_aff (Val p1) x) => //=.
      by move => z z0; case (z =P z0) => [ -> | ] /=; rewrite /join_V; autossr.
  Qed.

  Definition binop_pfunc {n: nat} (f: PwAff n -> PwAff n -> PwAff n) (p1 p2: PFunc n) :=
    let assumed_join := f_intersect_set (Assumed p1) (Assumed p2) in
    let val_join := f (Val p1) (Val p2) in
    mkPFunc val_join assumed_join.

  Definition add_pfunc {n: nat} :=
    @binop_pfunc n f_add_pw_aff.

  Theorem add_pfuncP :
    forall n (p1: PFunc n) x z1, in_pfunc p1 x z1 ->
      forall p2 z2, in_pfunc p2 x z2 ->
        in_pfunc (add_pfunc p1 p2) x (z1 + z2).
  Proof.
    move => n p1 x z1 Hin1 p2 z2. move: Hin1.
    rewrite /in_pfunc /add_pfunc /eval_pfunc /=.
    simpl_finite_presburger.
    case: (f_eval_pset (Assumed p1) x); case: (f_eval_pset (Assumed p2) x);
      case: (f_eval_pw_aff (Val p2) x); case: (f_eval_pw_aff (Val p1) x) => //=.
    by autossr.
  Qed.

  Definition le_binop_pfunc {n: nat} :=
    binop_pfunc (fun p1 p2 => @f_indicator_function n (f_le_set p1 p2)).

  Theorem le_binop_pfuncP :
    forall n {p1: PFunc n} x z1, in_pfunc p1 x z1 ->
      forall p2 z2, in_pfunc p2 x z2 ->
        in_pfunc (le_binop_pfunc p1 p2) x (if z1 <=? z2 then 1 else 0).
  Proof.
    move => n p1 x z1 Hin1 p2 z2. move: Hin1.
    rewrite /in_pfunc /add_pfunc /eval_pfunc /=.
    simpl_finite_presburger.
    case: (f_eval_pset (Assumed p1) x); case: (f_eval_pset (Assumed p2) x);
      case: (f_eval_pw_aff (Val p2) x); case: (f_eval_pw_aff (Val p1) x) => //=.
    move => a a0 /eqP -> /eqP ->. by case (a <=? a0).
  Qed.

  Definition intersect_assumed {n: nat} (p: PFunc n) (s: PSet n) :=
    mkPFunc (Val p) (f_intersect_set s (Assumed p)).

  Theorem intersect_assumedP :
    forall n p s x, eval_pfunc (@intersect_assumed n p s) x =
               if x \ins s then eval_pfunc p x else VTop.
  Proof.
    move => n p s x.
    rewrite /eval_pfunc.
    rewrite /intersect_assumed /=.
    simpl_finite_presburger.
      by case: (x \ins s); case (x \ins Assumed p).
  Qed.

  Definition pfunc_get_bot_set {n: nat} (p: PFunc n) :=
    f_intersect_set (Assumed p) (f_complement_set (f_get_domain_pw_aff (Val p))).

  Theorem pfunc_get_bot_setP :
    forall n p x, x \ins (@pfunc_get_bot_set n p) = (eval_pfunc p x == VBot).
  Proof.
    move => n p x. rewrite /pfunc_get_bot_set /eval_pfunc. simpl_finite_presburger.
    case: (x \ins Assumed p) => [ /= | // ].
      by case_match.
  Qed.

  Definition f_involves_dim_pfunc {n: nat} (p: PFunc n) (d: nat) :=
    f_involves_dim_pw_aff (f_intersect_domain (Val p) (Assumed p)) d || f_involves_dim_set (Assumed p) d.

  Theorem f_involves_dim_pfuncP :
    forall n p d, ~~ (@f_involves_dim_pfunc n p d) <-> forall x v, eval_pfunc p x = eval_pfunc p (set_nth 0 x d v).
  Proof.
    move => n p d. split => [ | ].
    - move => /norP [Hval Hassumed] x v.
      move => /f_involves_dim_setP /(_ x v) in Hassumed.
      move => /f_involves_dim_pw_affP /(_ x v) in Hval.
      rewrite !f_intersect_domainP in Hval. rewrite -Hassumed in Hval.
      rewrite /eval_pfunc. rewrite -Hassumed.
      case_if => //. by rewrite -Hval.
    - rewrite /eval_pfunc => Heq.
      rewrite /f_involves_dim_pfunc. apply /norP. split.
      + apply f_involves_dim_pw_affP => x v. move: (Heq x v).
        rewrite !f_intersect_domainP.
        repeat (case_if); repeat (case_match) => //. by move => [->]. by [].
      + apply f_involves_dim_setP => x v. move: (Heq x v).
        by repeat (case_if); repeat (case_match) => //.
  Qed.

  Theorem eval_pfunc_same_involves :
    forall (n: nat) (p: PFunc n) x y,
      (forall (i: nat), (i < n)%N -> f_involves_dim_pfunc p i -> nth 0%Z x i = nth 0%Z y i) ->
      eval_pfunc p x = eval_pfunc p y.
  Proof.
    move => n p x y Heq. rewrite /eval_pfunc.
    have Heq_assumed: (forall d : nat, (d < n)%N -> f_involves_dim_set (Assumed p) d -> nth 0 x d = nth 0 y d).
    move => i Hi Hinvolves. rewrite Heq => //. rewrite /f_involves_dim_pfunc Hinvolves. autossr.
    rewrite (f_eval_pset_same_involves _ _ _ _ Heq_assumed).
    case Hassumed_y: (y \ins Assumed p) => //.
    have Hassumed_x: (x \ins Assumed p). by rewrite (f_eval_pset_same_involves _ _ _ _ Heq_assumed).
    move: (f_eval_pw_aff_same_involves n (f_intersect_domain (Val p) (Assumed p)) x y) => Heq'.
    rewrite !f_intersect_domainP Hassumed_y Hassumed_x in Heq'.
    rewrite Heq' => //.
    - move => i Hi Hinvolves. rewrite Heq => //.
      rewrite /f_involves_dim_pfunc. autossr.
  Qed.

  Definition apply_map_to_pfunc {n m: nat} (map: PMap n m) (H: f_is_single_valued_map map) (pf: PFunc m) : PFunc n :=
    mkPFunc (f_apply_map_to_pw_aff map H (Val pf))
            (f_complement_set (f_get_domain_map (f_intersect_range_map map (f_complement_set (Assumed pf))))).

  Theorem apply_map_to_pfuncP :
    forall n m map H pf x_in v,
      v \inV eval_pfunc (@apply_map_to_pfunc n m map H pf) x_in
      <-> exists x_mid, (x_in, x_mid) \inm map /\ (v \inV eval_pfunc pf x_mid).
  Proof.
    move => n m map H pf x_in v.
    split => [ Heval | [x_mid [HInMap Heval]]].
    - rewrite /apply_map_to_pfunc /eval_pfunc /= in Heval.
      rewrite f_complement_setP in Heval.
      move: Heval. case_if => [ | _].
      + move => /negP in H0. rewrite ->f_get_domain_mapP in H0.
        case_match => //. rewrite /= => /eqP Heq. subst.
        rewrite ->f_apply_map_to_pw_affP in H1. move: H1 => [[H1 _] // | H1].
        case: H1 => x_mid [HInMap Heval].
        exists x_mid. split; auto.
        rewrite /eval_pfunc Heval. case_if => //. by rewrite /=.
      + move: H0. move => /negbFE /f_get_domain_mapP [x_mid].
        simpl_finite_presburger.
        move => /andP[HInMap HNotAssumed].
        exists x_mid. split; auto. rewrite /eval_pfunc. by autossr.
    - rewrite /apply_map_to_pfunc /eval_pfunc /=.
      case HInAssumed: (x_in \ins _) => //.
      case_match.
      + apply f_apply_map_to_pw_affP in H0.
        move: H0 => [[H0 _] // | [x_mid' [HInMap' Heval']]].
        move: Heval. rewrite /eval_pfunc. case_if.
        * rewrite_point x_mid x_mid'. by rewrite Heval'.
        * exfalso.
          rewrite f_complement_setP in HInAssumed. move => /negP in HInAssumed. apply HInAssumed.
          apply f_get_domain_mapP.
          exists x_mid. rewrite f_intersect_range_mapP. apply /andP.
          split; auto.
          simpl_finite_presburger. by rewrite H0.
      + exfalso.
        apply f_apply_map_to_pw_affP in H0.
        move: H0 =>  [ [ _ /(_ x_mid) H0 ] | [x_mid' [HInMap' Heval']] ].
          by rewrite HInMap in H0.
          move: Heval. rewrite /eval_pfunc.
          case_if.
        * rewrite_point x_mid x_mid'. by rewrite Heval'.
        * move => _.
          rewrite f_complement_setP in HInAssumed. move => /negP in HInAssumed. apply HInAssumed.
          apply f_get_domain_mapP.
          exists x_mid. rewrite f_intersect_range_mapP. apply /andP.
          split; auto.
          simpl_finite_presburger. by rewrite H0.
  Qed.


  Definition eq_PFunc {n: nat} (P1 P2: PFunc n) :=
    (Val P1 == Val P2) && (Assumed P1 == Assumed P2).
  Lemma eqPFuncP {n: nat} : Equality.axiom (@eq_PFunc n).
  Proof.
    rewrite /eq_PFunc => x y.
    case: x => Vx Ax. case: y => Vy Ay /=.
    case (Vx =P Vy); case (Ax =P Ay); intros; apply (iffP idP); autossr; by case.
  Qed.

  Canonical PFunc_eqType (n: nat) := Eval hnf in EqType (@PFunc n) (EqMixin (@eqPFuncP n)).

  Hint Rewrite @constant_pfuncP @constant_var_pfuncP @join_pfuncP @join_V_leftP @join_V_rightP using by first [liassr | autossr] : pfuncrw.
  Hint Resolve @add_pfuncP @le_binop_pfuncP : core.

  Ltac simpl_pfunc_ := repeat (autorewrite with maprw; autorewrite with pfuncrw; autorewrite with prw; simplssr).
  Ltac simpl_pfunc := reflect_ne_in simpl_pfunc_.

  Ltac auto_pfunc := intros; simpl_pfunc; autossr.

End PFuncImpl.
