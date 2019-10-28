From Coq Require Export ssrbool.
From PolyAI Require Export AbstractDomain.
From PolyAI.LoopFormalization Require Export LSSA.
Require Export Coq.Lists.List.

(* Transfer functions for our language, using relational abstract domain *)
Class transfer_function_relational {ab: Type} (A: adom (RegisterMap * RegisterMap) ab) :=
  {
    transfer_inst : Inst -> ab -> ab;
    transfer_inst_sound :
      forall inst R R', inst_step inst R R' ->
                   forall a R_begin, Ensembles.In _ (gamma a) (R_begin, R) ->
                        Ensembles.In _ (gamma (transfer_inst inst a)) (R_begin, R');

    transfer_term : Term -> ab -> list (ab * bbid);
    transfer_term_sound :
      forall prog term R bb R',
        term_step prog term R (bb, R') ->
        forall a R_begin, Ensembles.In _ (gamma a) (R_begin, R) ->
             exists a', In (a', bb) (transfer_term term a) /\
                   Ensembles.In _ (gamma a') (R_begin, R');
    transfer_term_only_successors :
      forall term bb a,
        (exists a', In (a', bb) (transfer_term term a)) ->
        list_string_in (term_successors term) bb;
  }.
