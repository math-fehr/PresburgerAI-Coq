From Coq Require Import ssreflect ssrfun ssrbool.
Require Export Coq.Sets.Ensembles.
From Coq Require Import ssrbool.
From PolyAI Require Export AbstractDomain.

(* The abstract domain over relations of concrete states *)
Class adom_relational {concrete_state abstract_state: eqType}
      (A: adom (prod_eqType concrete_state concrete_state) abstract_state) :=
  {
    (* The identity relation *)
    id_relation : abstract_state;
    id_relation_spec : forall x0 x1, In _ (gamma id_relation) (x0, x1) <-> x0 = x1;

    (* Composing two abstract domains by their relation representation *)
    compose_relation : abstract_state -> abstract_state -> abstract_state;
    compose_relation_spec :
      forall a1 a2 x0 x2, In _ (gamma (compose_relation a1 a2)) (x0,x2) <->
                     exists x1, In _ (gamma a1) (x0, x1) /\ In _ (gamma a2) (x1, x2);

    (* Compute an overapproximation of a reflexive-transitive closure *)
    transitive_closure : abstract_state -> abstract_state;
    transitive_closure_ge_step : forall a, le a (transitive_closure a);
    transitive_closure_ge_id : forall a, le id_relation (transitive_closure a);
    transitive_closure_eq_compose : forall a, le (compose_relation a (transitive_closure a)) (transitive_closure a);
  }.

Theorem compose_relation_le {concrete_state abstract_state: eqType}
        {A: adom (prod_eqType concrete_state concrete_state) abstract_state} (AR: adom_relational A)
  (a1 a2 comp_a: abstract_state):
  le a1 a2 -> le (compose_relation comp_a a1) (compose_relation comp_a a2).
Proof.
  move => /gamma_monotone Hle.
  apply gamma_monotone => [[x0 x2]] Hin1.
  apply compose_relation_spec in Hin1.
  move: Hin1 => [x1 [Hin1 Hin2]].
  apply compose_relation_spec.
  eauto.
Qed.
