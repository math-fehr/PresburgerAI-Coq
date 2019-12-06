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
    id_relation_spec : forall x, In _ (gamma id_relation) (x, x);

    (* Composing two abstract domains by their relation representation *)
    compose_relation : abstract_state -> abstract_state -> abstract_state;
    compose_relation_spec :
      forall a1 a2 x0 x2, In _ (gamma (compose_relation a1 a2)) (x0,x2) <->
                     exists x1, In _ (gamma a1) (x0, x1) /\ In _ (gamma a2) (x1, x2);
    compose_bot : forall a, compose_relation a bot = bot;

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
          {A: adom (prod_eqType concrete_state concrete_state) abstract_state}
          (AR: adom_relational A)
          (a a1 a2 a3: abstract_state).

  Theorem compose_relation_le:
    le a1 a2 -> le (compose_relation a a1) (compose_relation a a2).
  Proof.
    move => /gamma_monotone Hle.
    apply gamma_monotone => [[x0 x2]] /compose_relation_spec => [[x1 [Hin1 Hin2]]].
    apply compose_relation_spec.
    eauto.
  Qed.

  Theorem compose_relation_id :
    le a (compose_relation a id_relation).
  Proof.
    apply gamma_monotone => [[x0 x1] Hin].
    apply compose_relation_spec.
    by eauto.
  Qed.

  Theorem compose_assoc_l :
    le (compose_relation a1 (compose_relation a2 a3)) (compose_relation (compose_relation a1 a2) a3).
  Proof.
    apply gamma_monotone => [[x0 x1]] /compose_relation_spec[x2 [H1 /compose_relation_spec[x3 [H2 H3]]]].
    apply compose_relation_spec. exists x3. split; auto. apply compose_relation_spec. eauto.
  Qed.

  Theorem compose_assoc_r :
    le (compose_relation (compose_relation a1 a2) a3) (compose_relation a1 (compose_relation a2 a3)).
  Proof.
    apply gamma_monotone => [[x0 x1]] /compose_relation_spec[x2 [/compose_relation_spec[x3 [H2 H3]] H1]].
    apply compose_relation_spec. exists x3. split; auto. apply compose_relation_spec. eauto.
  Qed.

  Theorem compose_relation_quotient_right :
    le a2 a3 -> le (compose_relation a1 a2) (compose_relation a1 a3).
  Proof.
    move => /gamma_monotone Hle. apply gamma_monotone => [[x1 x2]] /compose_relation_spec[x3 [Hin1 Hin2]].
    apply compose_relation_spec; eauto.
  Qed.

  Theorem compose_relation_quotient_left :
    le a1 a2 -> le (compose_relation a1 a3) (compose_relation a2 a3).
  Proof.
    move => /gamma_monotone Hle. apply gamma_monotone => [[x1 x2]] /compose_relation_spec[x3 [Hin1 Hin2]].
    apply compose_relation_spec; eauto.
  Qed.

End RelationalAbstractDomainTheorems.

Hint Resolve @compose_relation_le @compose_relation_id @compose_assoc_l @compose_assoc_r
     @compose_relation_quotient_right @compose_relation_quotient_left : core.
