Require Export PolyAI.TotalMap.
Require Export Coq.Sets.Ensembles.
Require Import PolyAI.SSA.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
From Coq Require Import ssreflect ssrfun ssrbool.

Require Import String.
Open Scope string_scope.

(* The abstract domain *)
Class adom (ab:Type) :=
  {
    le : ab -> ab -> bool;
    top : ab;
    join : ab -> ab -> ab;

    gamma : ab -> Ensemble RegisterMap;
    gamma_monotone : forall a1 a2, le a1 a2 = true -> Included RegisterMap (gamma a1) (gamma a2);
    gamma_top : forall x, Ensembles.In RegisterMap (gamma top) x;
    join_sound : forall x y, Included RegisterMap (Union RegisterMap (gamma x) (gamma y)) (gamma (join x y))
  }.

(* Transfer functions for our language *)
Class transfer_function {ab: Type} (A: adom ab) :=
  {
    transfer : SSA -> ab -> label -> list (ab * label);
    transfer_sound :
      forall prog R l R' l',
        step prog (R, l) (R', l') ->
        forall a, Ensembles.In RegisterMap (gamma a) R ->
        exists a', In (a', l') (transfer (List.nth l prog (Const "X" 0)) a l) /\
              Ensembles.In RegisterMap (gamma a') R'
  }.

(* replace a[label] with join a[label] a_join *)
Fixpoint join_label {ab: Type} {A: adom ab} (T: transfer_function A) (a: list ab) (a_join: ab) (label: nat) :=
  match (a, label) with
  | (x::a', S label') => x::(join_label T a' a_join label')
  | (x::a', O) => (join x a_join)::a'
  | (nil, _) => nil
  end.

Theorem join_label_neq {ab: Type} {A: adom ab} (T: transfer_function A):
  forall label a a_join l default,
    l <> label -> List.nth l a default = List.nth l (join_label T a a_join label) default.
Proof.
  elim => [a a_join l default | n Hind a a_join l default Hneq].
  - case a => [// | a0 l0].
    case l => //.
  - case a => [// | a0 l0].
    case: l Hneq => [// | l' Hneq].
    simpl.
    apply Hind.
    auto.
Qed.

Theorem join_label_eq {ab: Type} {A: adom ab} (T: transfer_function A):
  forall label a a_join default,
    List.length a > label ->
    join (List.nth label a default) a_join = List.nth label (join_label T a a_join label) default.
Proof.
  elim => [a a_join default Hlength | n H a a_join default Hlength].
  - case: a Hlength => [| //].
    move => Hnillength.
    simpl in Hnillength.
    apply PeanoNat.Nat.nlt_0_r in Hnillength.
    by case Hnillength.
  - case: a Hlength => [ Hlength | x l Hlength].
    + simpl in Hlength.
      apply PeanoNat.Nat.nlt_0_r in Hlength.
      by case Hlength.
    + apply H.
      apply Gt.gt_S_n.
      by apply Hlength.
Qed.

Theorem join_label_same_size {ab: Type} {A: adom ab} (T: transfer_function A):
  forall label a a_join,
    List.length a = List.length (join_label T a a_join label).
Proof.
  elim => [ a a_join | label' Hind a a_join].
  - case a => //.
  - case a => [//| a0 a'].
    simpl.
    by apply eq_S, Hind.
Qed.

Definition one_step {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) (a: list ab) (label: nat) :=
  top :: nil.

Definition interpret {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :=
  List.repeat top (List.length prog).

Theorem interpret_has_same_length {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :
  List.length prog = List.length (interpret T prog).
Proof.
  Admitted.

Theorem interpret_has_initial_state_top {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :
  le top (List.nth 0 (interpret T prog) top) = true.
Proof.
  Admitted.

Theorem interpret_compute_fixpoint {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :
  forall l, l < List.length prog ->
       forall l', l' < List.length prog ->
             forall a', List.In (a', l') (transfer (List.nth l prog (Const "X" 0)) (List.nth l (interpret T prog) top) l) ->
                   le a' (List.nth l' (interpret T prog) top) = true.
Proof.
  Admitted.

Theorem interpret_step_sound {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :
  forall R1 l1 R2 l2, step prog (R1, l1) (R2, l2) ->
                 Ensembles.In RegisterMap (gamma (List.nth l1 (interpret T prog) top)) R1 ->
                 Ensembles.In RegisterMap (gamma (List.nth l2 (interpret T prog) top)) R2.
Proof.
  move=> R1 l1 R2 l2 Hstep Hprevious.
  inversion Hstep. subst.
  move: (@transfer_sound ab A T prog R1 l1 R2 l2 Hstep _ Hprevious) => [a' [Ha'in HR2in]].
  move: (interpret_compute_fixpoint T prog l1 H4 l2 H5 a' Ha'in) => Hsteps.
  apply (@gamma_monotone ab A) in Hsteps.
  apply Hsteps.
  exact HR2in.
Qed.

Theorem interpret_sound {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :
  forall R l, l < List.length prog ->
         reachable_states prog (R, l) ->
         Ensembles.In RegisterMap (gamma (List.nth l (interpret T prog) top)) R.
Proof.
  move => R l Hinbounds Hreachable.
  inversion Hreachable => {Hreachable}. subst.
  move: {2}(_,_) (erefl (R0, 0)) => R00 R00eq.
  move: {2}(_,_) (erefl (R, l)) => Rl Rleq.
  rewrite R00eq Rleq in H.
  elim: H R0 R l Rleq R00eq Hinbounds => [p R l|].
  - move=> R0 R1 l0 [-> ->] [<- <-] l0_small.
    move: (interpret_has_initial_state_top T p) => H0top.
    apply gamma_monotone in H0top.
    apply: H0top.
    apply: gamma_top.
  - move=> p [R0 l0] [R1 l1] [R2 l2] Hmsteps Hind Hstep R0' R2' l2' [H1 H2] [H3 H4] Hl_small.
    move: H1 H2 H3 H4 => -> -> <- <- in Hmsteps Hind Hstep Hl_small *.
    inversion Hstep. subst.
    move: (Hind R0' R1 l1 eq_refl eq_refl H4) => {Hind}Hind.
    apply: (interpret_step_sound T p R1 l1 R2 l2); auto.
Qed.
