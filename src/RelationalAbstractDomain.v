From Coq Require Import ssreflect ssrfun ssrbool.
Require Export Coq.Sets.Ensembles.
From Coq Require Import ssrbool.
From PolyAI Require Export AbstractDomain.

(* The abstract domain over relations of concrete states *)
Class adom_relational {concrete_state abstract_state: eqType} {p: Program}
      (A: adom (prod_eqType concrete_state concrete_state) abstract_state p) :=
  {
    (* The identity relation *)
    id_relation : abstract_state;
    id_relation_spec : forall x, In _ (gamma id_relation) (x, x);

    (* Composing two abstract domains by their relation representation *)
    compose_relation : abstract_state -> abstract_state -> abstract_state;
    compose_relation_spec : forall x1 x0 x2 a1 a2, In _ (gamma a1) (x0, x1) ->
                                              In _ (gamma a2) (x1, x2) ->
                                              In _ (gamma (compose_relation a1 a2)) (x0,x2);
    compose_bot : forall a, compose_relation a bot = bot;
    compose_relation_le: forall a a1 a2, le a1 a2 -> le (compose_relation a a1) (compose_relation a a2);
    compose_relation_quotient_right : forall a1 a2 a3,
        le a2 a3 -> le (compose_relation a1 a2) (compose_relation a1 a3);
    compose_relation_quotient_left : forall a1 a2 a3,
      le a1 a2 -> le (compose_relation a1 a3) (compose_relation a2 a3);

    (* Compute an overapproximation of a reflexive-transitive closure *)
    transitive_closure : abstract_state -> abstract_state;
    transitive_closure_ge_step : forall a, le a (transitive_closure a);
    transitive_closure_ge_id : forall a, le id_relation (transitive_closure a);
    transitive_closure_eq_compose : forall a, le (compose_relation (transitive_closure a) a) (transitive_closure a);
  }.

Hint Rewrite @compose_bot : airw.
Hint Resolve @compose_bot @transitive_closure_ge_step transitive_closure_ge_id transitive_closure_eq_compose @id_relation_spec : core.

Section RelationalAbstractDomainTheorems.

  Context {concrete_state abstract_state: eqType}
          {p: Program}
          {A: adom (prod_eqType concrete_state concrete_state) abstract_state p}
          (AR: adom_relational A)
          (a a1 a2 a3: abstract_state).

  Theorem compose_relation_id :
    le a (compose_relation a id_relation).
  Proof.
    move => [x0 x1] Hin.
    by apply (compose_relation_spec x1); auto.
  Qed.

End RelationalAbstractDomainTheorems.

Hint Resolve @compose_relation_le @compose_relation_id
     @compose_relation_quotient_right @compose_relation_quotient_left : core.
