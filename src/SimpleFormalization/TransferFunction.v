From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export AbstractDomain.
From PolyAI.SimpleFormalization Require Export SSA.
Require Export Coq.Lists.List.

(* Transfer functions for our language *)
Class transfer_function {ab: Type} (A: adom RegisterMap ab) :=
  {
    transfer : Instruction -> ab -> label -> list (ab * label);
    transfer_sound :
      forall prog R l R' l',
        step prog (R, l) (R', l') ->
        forall inst, Some inst = List.nth_error prog l ->
                forall a, Ensembles.In RegisterMap (gamma a) R ->
                     exists a', In (a', l') (transfer inst a l) /\
                           Ensembles.In RegisterMap (gamma a') R'
  }.
