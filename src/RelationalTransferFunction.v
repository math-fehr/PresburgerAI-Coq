From Coq Require Export ssrbool.
From PolyAI Require Export RelationalAbstractDomain LSSA.
Require Export Coq.Lists.List.

Local Open Scope type_scope.

(* Transfer functions for our language, using relational abstract domain *)
Class transfer_function_relational {abstract_state: eqType}
      {A: adom (prod_eqType RegisterMap RegisterMap) abstract_state}
      (AR: adom_relational A) :=
  {
    transfer_inst : Inst -> abstract_state -> abstract_state;
    transfer_inst_sound :
      forall inst R R', inst_step inst R R' ->
                   forall a R_begin, Ensembles.In _ (gamma a) (R_begin, R) ->
                                Ensembles.In _ (gamma (transfer_inst inst a)) (R_begin, R');

    transfer_inst_compose :
      forall inst a comp_a,
        le (transfer_inst inst (compose_relation comp_a a))
           (compose_relation comp_a (transfer_inst inst a));

    transfer_term : Term -> abstract_state -> list (abstract_state * bbid);
    transfer_term_sound :
      forall prog term R bb R',
        term_step prog term R (bb, R') ->
        forall a R_begin, Ensembles.In _ (gamma a) (R_begin, R) ->
             exists a', (a', bb) \in (transfer_term term a) /\
                   Ensembles.In _ (gamma a') (R_begin, R');
    transfer_term_only_successors :
      forall term bb,
        (exists a a', (a', bb) \in (transfer_term term a)) ->
        bb \in (term_successors term);

    transfer_term_compose :
      forall term a a' comp_a bb,
        (a', bb) \in (transfer_term term (compose_relation comp_a a)) ->
        exists a'', (a'', bb) \in transfer_term term a /\ le a' (compose_relation comp_a a'');
  }.
