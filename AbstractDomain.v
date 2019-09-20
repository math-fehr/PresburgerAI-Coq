Require Export PolyAI.TotalMap.
Require Export Coq.Sets.Ensembles.
Require Import PolyAI.SSA.
Require Import Coq.Program.Equality.

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
    gamma_top : forall x, In RegisterMap (gamma top) x;
    join_sound : forall x y, Included RegisterMap (Union RegisterMap (gamma x) (gamma y)) (gamma (join x y))
  }.

(* Transfer functions for our language *)
Class transfer_function {ab: Type} (A: adom ab) :=
  {
    transfer : SSA -> ab -> label -> list (ab * label);
    transfer_sound :
      forall prog R l R' l' a inst,
        In RegisterMap (gamma a) R ->
        step prog (R, l) (R', l') ->
        inst = List.nth l prog (Const "X" 0) ->
        exists a', List.In (a', l') (transfer inst a l) /\
              In RegisterMap (gamma a') R'
  }.

Definition interpret {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :=
   @nil ab.

Theorem interpret_has_same_length {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :
  List.length prog = List.length (interpret T prog).
Proof.
  Admitted.

Theorem interpret_has_initial_state_top {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :
  le top (List.nth 0 (interpret T prog) top) = true.
Proof.
  Admitted.

Theorem interpret_compute_fixpoint {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :
  forall l l' a', l < List.length prog ->
             l' < List.length prog ->
             let a_dom := interpret T prog in
             let inst := List.nth l prog (Const "X" 0) in
             let a := List.nth l a_dom top in
             List.In (a', l') (transfer inst a l) ->
             le a' (List.nth l' a_dom top) = true.
Proof.
Admitted.


Theorem interpret_sound {ab: Type} {A: adom ab} (T: transfer_function A) (prog: Program) :
  forall R l, l < List.length prog ->
         reachable_states prog (R, l) ->
         In RegisterMap (gamma (List.nth l (interpret T prog) top)) R.
Proof.
  intros R l Hinbounds Hreachable.
  inversion Hreachable.
  subst.
  generalize_eqs H.
  generalize dependent l.
  generalize dependent R.
  generalize dependent R0.
  induction H.
  - intros.
    apply JMeq_eq in H. injection H. intros.
    apply JMeq_eq in H0. injection H0. intros.
    subst.
    pose proof (interpret_has_initial_state_top T p).
    apply gamma_monotone in H1.
    apply H1.
    apply gamma_top.
  - intros.
    apply JMeq_eq in H1. apply JMeq_eq in H2. subst.
    destruct s'.
    inversion H0. subst.
    pose proof H6 as Hl0.
    apply (IHmulti_step R0 r) in H6; auto;
      try (apply Reachable with (R := R0); auto).
    pose proof (transfer_sound p r l0 R l) as H1.
    apply H1 with (inst := (List.nth l0 p (Const "X" 0))) in H6; auto.
    destruct H6. destruct H2.
    pose proof (interpret_compute_fixpoint T p l0 l x).
    apply H4 in Hl0; auto.
    apply gamma_monotone in Hl0.
    apply Hl0.
    exact H3.
Qed.
