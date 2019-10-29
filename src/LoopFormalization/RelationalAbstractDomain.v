Require Export Coq.Sets.Ensembles.
From Coq Require Import ssrbool.
From PolyAI Require Export AbstractDomain.

(* The abstract domain over relations of concrete states *)
Class adom_relational {concrete_state abstract_state: Type}
      (A: adom (concrete_state * concrete_state) abstract_state) :=
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
