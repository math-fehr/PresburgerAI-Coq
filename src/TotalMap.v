From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.ssrnat eqtype seq.
From Coq Require Export Arith.Arith Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From PolyAI Require Import Tactic.

(* This code is inspired from the programming language fundations book *)

Local Open Scope list_scope.

(*  ____            _   _       _ __  __              *)
(* |  _ \ __ _ _ __| |_(_) __ _| |  \/  | __ _ _ __   *)
(* | |_) / _` | '__| __| |/ _` | | |\/| |/ _` | '_ \  *)
(* |  __/ (_| | |  | |_| | (_| | | |  | | (_| | |_) | *)
(* |_|   \__,_|_|   \__|_|\__,_|_|_|  |_|\__,_| .__/  *)
(*                                            |_|     *)


Section PartialMapDefinition.

  Context {Key: eqType}
          {Value: Type}.

  (* Representation of a total map with finite non-default values *)

  Inductive partial_map :=
  | PEmpty
  | PUpdate (m: partial_map) (k: Key) (v: Value).

  (* Evaluate a map on a point*)
  Fixpoint eval_partial_map (m: partial_map) (k: Key) :=
    match m with
    | PEmpty => None
    | PUpdate m' k' v => if k' == k then Some v else eval_partial_map m' k
    end.

  (* Coercion for evaluation *)
  Coercion eval_partial_map : partial_map >-> Funclass.

End PartialMapDefinition.

(* Notation for a map update *)
Notation "k '!!->' v ';' m" := (PUpdate m k v)
                                 (at level 100, v at next level, right associativity).

(* Notation for an empty map *)
Notation "k '!!->' v" := (PUpdate PEmpty k v)
                           (at level 100).


Section PartialMapRewriteRules.

  Context {Key: eqType}
          {Value: Type}
          (k k1 k2: Key)
          (v v1 v2: Value)
          (m: @partial_map Key Value).

  (* Useful lemmas and theorems *)

  Lemma p_apply_empty :
    @PEmpty Key Value k = None.
  Proof.
      by [].
  Qed.

  Lemma p_update_eq :
    (k !!-> v ; m) k = Some v.
  Proof.
    by autossr.
  Qed.

  Theorem p_update_neq :
    k1 != k2 ->
    (k1 !!-> v ; m) k2 = m k2.
  Proof.
    by autossr.
  Qed.

  Lemma p_update_shadow :
    eval_partial_map (k !!-> v2 ; k !!-> v1 ; m) = eval_partial_map (k !!-> v2 ; m).
  Proof.
    extensionality k' => /=.
      by case (k =P k').
  Qed.

  Theorem p_update_permute :
    k2 != k1 ->
    eval_partial_map (k1 !!-> v1 ; k2 !!-> v2 ; m) =
    eval_partial_map (k2 !!-> v2 ; k1 !!-> v1 ; m).
  Proof.
    move => Hne /=.
    extensionality k'.
    case (k1 =P k'); by autossr.
  Qed.

End PartialMapRewriteRules.

Hint Rewrite @p_apply_empty @p_update_eq @p_update_neq @p_update_shadow using by simplssr : maprw.

  (* Pointwise operations on one or multiple maps *)

Section PartialMapPointwiseUn.

  Context {Key: eqType} {Value Value': Type}.

  Fixpoint p_pointwise_un_op (m: @partial_map Key Value) (f: Value -> Value') :=
    match m with
    | PEmpty => PEmpty
    | PUpdate m1' k v => (k !!-> f v; p_pointwise_un_op m1' f)
    end.

  Theorem p_pointwise_un_op_spec (m: @partial_map Key Value) (f: Value -> Value') (k: Key) :
    (p_pointwise_un_op m f) k = option_map f (m k).
  Proof.
    elim: m f k => [// | m Hind k v f k' /=].
      by case (k =P k').
  Qed.

End PartialMapPointwiseUn.

Section PartialMapKeysList.

  Context {Key: eqType} {Value Value': Type}.

  Fixpoint keys_list (m: @partial_map Key Value) :=
    match m with
    | PEmpty => [::]
    | PUpdate m' k _ => k::(keys_list m')
    end.

  Theorem keys_list_spec (m: @partial_map Key Value) :
    forall k, m k <> None <-> k \in keys_list m.
  Proof.
    elim m => [ // | m' Hind k v k0].
    case (k =P k0) => [ -> /= | /eqP Hne ]; autossr.
  Qed.

End PartialMapKeysList.

(* Equality definition *)

Fixpoint eq_partial_map {Key Value: eqType} (m1 m2: @partial_map Key Value) :=
  match (m1, m2) with
  | (PEmpty, PEmpty) => true
  | (PUpdate m1' k1 v1, PUpdate m2' k2 v2) => (eq_partial_map m1' m2') && (k1 == k2) && (v1 == v2)
  | _ => false
  end.

Theorem eq_partial_mapP (Key Value: eqType) :
  Equality.axiom (@eq_partial_map Key Value).
Proof.
  elim => [ m2 /= | m1' Hind1 k1 v1 m2 /= ].
  - apply (iffP idP); by case m2.
  - apply (iffP idP) => [ | <- ].
    + case m2 => [ // | m2' k2 v2 /andP[/andP[/Hind1 -> /eqP ->] /eqP ->] //].
    + simplssr. by apply /Hind1.
Qed.

Hint Rewrite @p_pointwise_un_op_spec using by reflect_ne ; simplssr : maprw.

Canonical partial_map_eqMixin {Key Value: eqType} := EqMixin (@eq_partial_mapP Key Value).
Canonical partial_map_eqType {Key Value: eqType} := Eval hnf in EqType (@partial_map Key Value) partial_map_eqMixin.

(* Useful tactic which apply known lemmas *)


Global Opaque eval_partial_map.

(*  _____     _        _ __  __            ____   *)
(* |_   _|__ | |_ __ _| |  \/  | __ _ _ __|___ \  *)
(*   | |/ _ \| __/ _` | | |\/| |/ _` | '_ \ __) | *)
(*   | | (_) | || (_| | | |  | | (_| | |_) / __/  *)
(*   |_|\___/ \__\__,_|_|_|  |_|\__,_| .__/_____| *)
(*                                   |_|          *)

(* Representation of a total map with finite non-default values *)

Section TotalMapDefinition.

  Context (Key: eqType) (Value: Type).

  Structure total_map := TotalMap
    {
      t_map: @partial_map Key Value;
      t_default: Value;
    }.

End TotalMapDefinition.

Section TotalMapCoreDefinitions.

  Context {Key: eqType} {Value: Type}.

  (* Update the total map *)
  Definition t_update (m: total_map Key Value) (k: Key) (v: Value) :=
    TotalMap _ _ (k !!-> v; t_map _ _ m) (t_default _ _ m).

End TotalMapCoreDefinitions.

(* Notation for a map update *)
Notation "k '!->' v ';' m" := (t_update m k v)
                                 (at level 100, v at next level, right associativity).

(* Notation for a default map *)
Notation "'_' '!->' v" := (TotalMap _ _ (PEmpty) v)
                             (at level 100).


Section TotalMapEqType.

  Context {Key Value: eqType}.

  Definition eq_total_map (m1 m2: total_map Key Value) :=
    ((t_map _ _ m1) == t_map _ _ m2) && (t_default _ _ m1 == t_default _ _ m2).

  Theorem eq_total_mapP :
    Equality.axiom (eq_total_map).
  Proof.
    move => [map1 default1] [map default2].
    apply (iffP idP) => [ /andP /= [/eqP -> /eqP ->] // | -> ].
    rewrite /eq_total_map. by rewrite !eq_refl.
  Qed.

  Canonical total_map_eqMixin := EqMixin (eq_total_mapP).
  Canonical total_map_eqType := Eval hnf in EqType (@total_map Key Value) total_map_eqMixin.

End TotalMapEqType.

Section TotalMapEval.

  (* Evaluate a map on a point*)
  Definition eval_total_map {Key: eqType} {Value: Type} (m: @total_map Key Value) (k: Key) :=
    if (t_map _ _ m) k is Some v then
      v
    else
      t_default _ _ m.

  (* Coercion for evaluation *)
  Coercion eval_total_map : total_map >-> Funclass.

End TotalMapEval.

(* Important rewrite rules *)
Section TotalMapRewriteRules.

  Context {Key: eqType} {Value: Type} (k k1 k2: Key) (v v1 v2: Value) (m: total_map Key Value).

  Lemma t_update_out (pm: partial_map):
    eval_total_map (TotalMap _ _ (k !!-> v1 ; pm) v) = eval_total_map (t_update (TotalMap _ _ pm v) k v1).
  Proof.
      by [].
  Qed.

  Lemma t_apply_empty :
    (_ !-> v) k = v.
  Proof.
      by [].
  Qed.

  Lemma t_update_eq :
    (k !-> v ; m) k = v.
  Proof.
    rewrite /eval_total_map /=.
    by autorewrite with maprw.
  Qed.

  Theorem t_update_neq :
    k1 != k2 ->
    (k1 !-> v ; m) k2 = m k2.
  Proof.
    move => Hne. rewrite /eval_total_map /=.
    by autorewrite with maprw.
  Qed.

  Lemma t_update_shadow :
    eval_total_map (k !-> v2 ; k !-> v1 ; m) = eval_total_map (k !-> v2 ; m).
  Proof.
    rewrite /eval_total_map.
    extensionality k' => /=.
    by autorewrite with maprw.
  Qed.

  Theorem t_update_same :
    eval_total_map (k !-> m k ; m) = eval_total_map m.
  Proof.
    rewrite /eval_total_map.
    extensionality k' => /=.
    case (k =P k') => [ -> | /eqP Hne ]; by autorewrite with maprw.
  Qed.

  Theorem t_update_permute :
    k2 != k1 ->
    eval_total_map (k1 !-> v1 ; k2 !-> v2 ; m) =
    eval_total_map (k2 !-> v2 ; k1 !-> v1 ; m).
  Proof.
    rewrite /eval_total_map => Hne.
    extensionality k' => /=.
      by rewrite p_update_permute.
  Qed.

End TotalMapRewriteRules.

Hint Rewrite @t_update_out @t_apply_empty @t_update_eq @t_update_neq @t_update_shadow @t_update_same using by simplssr : maprw.

(* Pointwise operations on one or multiple maps *)

Section TotalMapPointwiseUn.

  Context {Key: eqType}
          {Value Value': Type}.

  Definition t_pointwise_un_op (m: total_map Key Value) (f: Value -> Value') :=
    TotalMap _ _ (p_pointwise_un_op (t_map _ _ m) f) (f (t_default _ _ m)).

  Theorem t_pointwise_un_op_spec (m: total_map Key Value) (f: Value -> Value') (k: Key) :
    t_pointwise_un_op m f k = f (m k).
  Proof.
    rewrite /t_pointwise_un_op /eval_total_map /=.
    autorewrite with maprw.
    by case (t_map _ _ m k).
  Qed.

  Fixpoint t_pointwise_un_op_in_seq (m: total_map Key Value) (f: Value -> Value) (l: seq Key) :=
    match l with
    | [::] => m
    | a::l' => (a !-> f (m a); t_pointwise_un_op_in_seq m f l')
    end.

  Theorem t_pointwise_un_op_in_seq_spec (m: total_map Key Value) (f: Value -> Value) (l: seq Key) :
    forall x, (t_pointwise_un_op_in_seq m f l) x = if x \in l then f (m x) else (m x).
  Proof.
    move => x. elim l => [ // | k l' ].
    rewrite in_cons. case: (x \in l') => Hind /=; case: (x =P k) => [ -> | /eqP Hne ]; by autorewrite with maprw.
  Qed.

End TotalMapPointwiseUn.

Hint Rewrite @t_pointwise_un_op_spec @t_pointwise_un_op_in_seq_spec using by autossr : maprw.

Global Opaque eval_total_map.

Section TotalMapD.

  Context (Key: eqType)
          (Value: Type)
          (default: Value).

  Definition total_map_d := { map: total_map Key Value | t_default _ _ map = default}.

End TotalMapD.

Section TotalMapDCoreDefinitions.

  Context {Key: eqType}
          {Value: Type}.

  (* Create an empty map *)
  Program Definition td_new (default: Value) : total_map_d Key Value default :=
    exist _ (_ !-> default) _.

  (* Update the total map *)
  Program Definition td_update {default: Value} (m: total_map_d Key Value default) (k: Key) (v: Value) : total_map_d Key Value default :=
    exist _ (k !-> v; proj1_sig m) _.
  Obligation 1.
    by destruct m.
  Qed.

End TotalMapDCoreDefinitions.

(* Notation for a map update *)
Notation "k '|->' v ';' m" := (td_update m k v)
                                 (at level 99, v at next level, right associativity).

(* Notation for a default map *)
Notation "'_' '|->' v" := (td_new v)
                             (at level 99).

Section TotalMapDEqType.

  Context {Key Value: eqType}
          (default: Value).

  Definition eq_total_map_d (m1 m2: total_map_d Key Value default) :=
    sval m1 == sval m2.

  Theorem eq_total_map_dP :
    Equality.axiom (eq_total_map_d).
  Proof.
    move => [map1 default1] [map default2].
    apply: (iffP idP) => [ /eqP /= Heq | ].
    - move: default1 default2. rewrite Heq => default1 default2. move: eq_irrelevance.
        by move => /(_ _ _ _ default1 default2) ->.
    - case. rewrite /eq_total_map_d /= => -> //.
  Qed.

  Canonical total_map_d_eqMixin := EqMixin (eq_total_map_dP).
  Canonical total_map_d_eqType := Eval hnf in EqType (@total_map_d Key Value default) total_map_d_eqMixin.

End TotalMapDEqType.

Section TotalMapDEval.

  (* Evaluate a map on a point*)
  Definition eval_total_map_d {Key: eqType} {Value: Type} {default: Value} (m: total_map_d Key Value default) (k: Key) :=
    eval_total_map (sval m) k.

  (* Coercion for evaluation *)
  Coercion eval_total_map_d : total_map_d >-> Funclass.

End TotalMapDEval.

(* Important rewrite rules *)
Section TotalMapDRewriteRules.

  Context {Key: eqType}
          {Value: Type}
          {default: Value}
          (k k1 k2: Key)
          (v v1 v2: Value)
          (m: total_map_d Key Value default).

  Lemma td_apply_empty :
    (_ |-> v) k = v.
  Proof.
      by [].
  Qed.

  Lemma td_update_eq :
    (k |-> v ; m) k = v.
  Proof.
    rewrite /eval_total_map_d /=.
    by autorewrite with maprw.
  Qed.

  Theorem td_update_neq :
    k1 != k2 ->
    (k1 |-> v ; m) k2 = m k2.
  Proof.
    move => Hne. rewrite /eval_total_map_d /=.
    by autorewrite with maprw.
  Qed.

  Lemma td_update_shadow :
    eval_total_map_d (k |-> v2 ; k |-> v1 ; m) = eval_total_map_d (k |-> v2 ; m).
  Proof.
    rewrite /eval_total_map_d.
    extensionality k' => /=.
    by autorewrite with maprw.
  Qed.

  Theorem td_update_same :
    eval_total_map_d (k |-> m k ; m) = eval_total_map_d m.
  Proof.
    rewrite /eval_total_map_d.
    extensionality k' => /=.
    case (k =P k') => [ -> | /eqP Hne ]; by autorewrite with maprw.
  Qed.

  Theorem td_update_permute :
    k2 != k1 ->
    eval_total_map_d (k1 |-> v1 ; k2 |-> v2 ; m) =
    eval_total_map_d (k2 |-> v2 ; k1 |-> v1 ; m).
  Proof.
    rewrite /eval_total_map_d => Hne.
    extensionality k' => /=.
      by rewrite t_update_permute.
  Qed.

End TotalMapDRewriteRules.

Hint Rewrite @td_apply_empty @td_update_eq @td_update_neq @td_update_shadow @td_update_same using by autossr : maprw.

(* Pointwise operations on one or multiple maps *)

Section TotalMapDPointwiseUn.

  Context {Key: eqType}
          {Value Value': Type}
          {default: Value}
          (m: total_map_d Key Value default).

  Program Definition td_pointwise_un_op (f: Value -> Value') : total_map_d Key Value' (f default) :=
    exist _ (t_pointwise_un_op (sval m) f) _.
  Obligation 1.
    by move: m => [m' ->].
  Qed.

  Theorem td_pointwise_un_op_spec (f: Value -> Value') (k: Key) :
    td_pointwise_un_op f k = f (m k).
  Proof.
    rewrite /td_pointwise_un_op /eval_total_map_d /=.
    apply t_pointwise_un_op_spec.
  Qed.

  Program Definition td_pointwise_un_op_in_seq (f: Value -> Value) (l: seq Key) : total_map_d Key Value default :=
    exist _ (t_pointwise_un_op_in_seq (sval m) f l) _.
  Obligation 1.
    by elim: l m => [ [m' Hdefault] // | //].
  Qed.

  Theorem td_pointwise_un_op_in_seq_spec (f: Value -> Value) (l: seq Key) :
    forall x, (td_pointwise_un_op_in_seq f l) x = if x \in l then f (m x) else (m x).
  Proof.
    rewrite /eval_total_map_d /= => k.
    by rewrite t_pointwise_un_op_in_seq_spec.
  Qed.

End TotalMapDPointwiseUn.

Hint Rewrite @td_pointwise_un_op_spec @td_pointwise_un_op_in_seq_spec using by autossr : maprw.

Ltac simpl_map_ := repeat (autorewrite with maprw; simplssr).
Ltac simpl_map := reflect_ne_in simpl_map_.

Ltac auto_map := intros ; simpl_map ; autossr.
