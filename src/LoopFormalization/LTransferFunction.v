From PolyAI Require Export LAbstractDomain LSSA.
Require Export Coq.Lists.List.

(* Transfer functions for our language *)
Class transfer_function {ab: Type} (A: adom ab) :=
  {
    transfer_inst : Inst -> ab -> ab;
    transfer_inst_sound :
      forall inst R R', inst_step inst R R' ->
                   forall a, Ensembles.In RegisterMap (gamma a) R ->
                        Ensembles.In RegisterMap (gamma (transfer_inst inst a)) R';

    transfer_term : Term -> ab -> list (ab * bbid);
    transfer_term_sound :
      forall prog term R bb R',
        term_step prog term R (bb, R') ->
        forall a, Ensembles.In RegisterMap (gamma a) R ->
             exists a', In (a', bb) (transfer_term term a) /\
                   Ensembles.In RegisterMap (gamma a') R';

  }.
