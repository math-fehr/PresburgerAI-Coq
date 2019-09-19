Require Export PolyAI.TotalMap.
Require Export Coq.Sets.Ensembles.
Require Import PolyAI.SSA.

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
        Some inst = List.nth_error prog l ->
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
