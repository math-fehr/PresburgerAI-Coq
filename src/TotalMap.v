From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.ssrnat eqtype seq.
From Coq Require Export Arith.Arith Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From PolyAI Require Import Tactic ssrstring.

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

  Lemma p_update_eq_hyp :
    k1 == k2 ->
    (k1 !!-> v ; m) k2 = Some v.
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

Hint Rewrite @p_apply_empty @p_update_eq @p_update_eq_hyp @p_update_neq @p_update_shadow using by first [liassr | autossr ] : maprw.

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

Hint Rewrite @p_pointwise_un_op_spec : maprw.

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

Canonical partial_map_eqMixin {Key Value: eqType} := EqMixin (@eq_partial_mapP Key Value).
Canonical partial_map_eqType {Key Value: eqType} := Eval hnf in EqType (@partial_map Key Value) partial_map_eqMixin.

(* Useful tactic which apply known lemmas *)


Global Opaque eval_partial_map.

(*  _____     _        _ __  __              *)
(* |_   _|__ | |_ __ _| |  \/  | __ _ _ __   *)
(*   | |/ _ \| __/ _` | | |\/| |/ _` | '_ \  *)
(*   | | (_) | || (_| | | |  | | (_| | |_) | *)
(*   |_|\___/ \__\__,_|_|_|  |_|\__,_| .__/  *)
(*                                   |_|     *)

(* Representation of a total map with finite non-default values *)

Section TotalMapDefinition.

  Context {Key: eqType}
          {Value: Type}.

  (* Representation of a total map with finite non-default values *)
  Inductive total_map :=
  | TDefault (v: Value)
  | TUpdate (m': total_map) (k: Key) (v: Value).

  Fixpoint eval_total_map (m: total_map) (k: Key) :=
    match m with
    | TDefault v => v
    | TUpdate m' k' v => if k' == k then v else eval_total_map m' k
    end.

  Coercion eval_total_map : total_map >-> Funclass.

End TotalMapDefinition.


(* Notation for a map update *)
Notation "k '!->' v ';' m" := (TUpdate m k v)
                                (at level 100, v at next level, right associativity).

(* Notation for a default map *)
Notation "'_' '!->' v" := (TDefault v)
                            (at level 100).

Section TotalMapEqType.

  Context {Key Value: eqType}.

  Fixpoint eq_total_map (m1 m2: @total_map Key Value) :=
    match (m1, m2) with
    | (TDefault d1, TDefault d2) => d1 == d2
    | (TUpdate m1' k1 v1, TUpdate m2' k2 v2) => (k1 == k2) && (v1 == v2) && (eq_total_map m1' m2')
    | _ => false
    end.

  Theorem eq_total_mapP :
    Equality.axiom (eq_total_map).
  Proof.
    elim => [ v1 m2 /= | m1' Hind1 k1 v1 m2 /= ].
    - apply (iffP idP); case m2; autossr.
      move => v2. case. autossr.
    - apply (iffP idP) => [ | <- ].
      + case m2 => [ // | m2' k2 v2 /andP[/andP[/eqP -> /eqP ->] /Hind1 ->] //].
      + simplssr. by apply /Hind1.
  Qed.

  Canonical total_map_eqMixin := EqMixin (eq_total_mapP).
  Canonical total_map_eqType := Eval hnf in EqType (@total_map Key Value) total_map_eqMixin.

End TotalMapEqType.

(* Important rewrite rules *)
Section TotalMapRewriteRules.

  Context {Key: eqType}
          {Value: Type}
          (k k1 k2: Key)
          (v v1 v2: Value)
          (m: @total_map Key Value).

  Lemma t_apply_empty :
    (_ !-> v) k = v.
  Proof.
      by [].
  Qed.

  Lemma t_update_eq :
    (k !-> v ; m) k = v.
  Proof.
      by autossr.
  Qed.

  Lemma t_update_eq_hyp :
    k1 == k2 -> (k1 !-> v ; m) k2 = v.
  Proof.
      by autossr.
  Qed.


  Theorem t_update_neq :
    k1 != k2 ->
    (k1 !-> v ; m) k2 = m k2.
  Proof.
      by autossr.
  Qed.

  Lemma t_update_shadow :
    eval_total_map (k !-> v2 ; k !-> v1 ; m) = eval_total_map (k !-> v2 ; m).
  Proof.
    extensionality k' => /=.
    case (k =P k'); autossr.
  Qed.

  Theorem t_update_same :
    eval_total_map (k !-> m k ; m) = eval_total_map m.
  Proof.
    extensionality k' => /=.
    case (k =P k'); autossr.
  Qed.

  Theorem t_update_permute :
    k2 != k1 ->
    eval_total_map (k1 !-> v1 ; k2 !-> v2 ; m) =
    eval_total_map (k2 !-> v2 ; k1 !-> v1 ; m).
  Proof.
    move => Hne.
    extensionality k' => /=.
    case (k1 =P k'); by autossr.
  Qed.

End TotalMapRewriteRules.

Hint Rewrite @t_apply_empty @t_update_eq @t_update_eq_hyp @t_update_neq @t_update_shadow @t_update_same using by first [liassr | autossr ] : maprw.

(* Pointwise operations on one or multiple maps *)

Section TotalMapPointwise.

  Context {Key: eqType}
          {Value Value' Value'': Type}.

  Fixpoint t_pointwise_un_op (m: @total_map Key Value) (f: Value -> Value') :=
    match m with
    | TDefault v => TDefault (f v)
    | TUpdate m' k v => TUpdate (t_pointwise_un_op m' f) k (f v)
    end.

  Theorem t_pointwise_un_op_spec (m: @total_map Key Value) (f: Value -> Value') (k: Key) :
    t_pointwise_un_op m f k = f (m k).
  Proof.
    elim: m => [ v // | m' Hind k' v'].
    case (k =P k'); rewrite /= Hind; autossr.
  Qed.

  Fixpoint t_pointwise_un_op_in_seq (m: @total_map Key Value) (f: Value -> Value) (l: seq Key) :=
    match l with
    | [::] => m
    | a::l' => (a !-> f (m a); t_pointwise_un_op_in_seq m f l')
    end.

  Theorem t_pointwise_un_op_in_seq_spec (m: @total_map Key Value) (f: Value -> Value) (l: seq Key) :
    forall x, (t_pointwise_un_op_in_seq m f l) x = if x \in l then f (m x) else (m x).
  Proof.
    elim: l => [ // | k l' Hind x /=]. rewrite Hind.
      by case (k =P x); autossr.
  Qed.

  Fixpoint t_pointwise_bin_op_aux (m1: @total_map Key Value) (k2: Value') (f: Value -> Value' -> Value'') :=
    match m1 with
    | TDefault k1 => (_ !-> f k1 k2)
    | TUpdate m1' v k1 => let new_m := t_pointwise_bin_op_aux m1' k2 f in
                         (v !-> f k1 k2; new_m)
    end.

  Lemma t_pointwise_bin_op_aux_spec (m1: @total_map Key Value) (v2: Value') (f: Value -> Value' -> Value'') (k: Key):
    (t_pointwise_bin_op_aux m1 v2 f) k = f (m1 k) v2.
  Proof.
    elim: m1 => [// | m1 Hind k1 v1 /=].
    rewrite Hind.
      by case (k1 == k).
  Qed.

  Fixpoint t_pointwise_bin_op (m1: @total_map Key Value) (m2: @total_map Key Value') (f: Value -> Value' -> Value'') :=
    match m2 with
    | TDefault v2 => t_pointwise_bin_op_aux m1 v2 f
    | TUpdate m2' k v2 => let new_m := t_pointwise_bin_op m1 m2' f in
                         (k !-> (f (m1 k) v2); new_m)
    end.

  Theorem t_pointwise_bin_op_spec (m1: @total_map Key Value) (m2: @total_map Key Value') (f: Value -> Value' -> Value'') (k: Key):
    (t_pointwise_bin_op m1 m2 f) k = f (m1 k) (m2 k).
  Proof.
    elim: m2 m1 => [v m1 | m2 Hind k2 v2 m1 /=].
    - by apply t_pointwise_bin_op_aux_spec.
    - rewrite Hind.
        by case (k2 =P k) => [-> // | //].
  Qed.

End TotalMapPointwise.

Hint Rewrite @t_pointwise_un_op_spec @t_pointwise_un_op_in_seq_spec @t_pointwise_bin_op_spec : maprw.

Section TotalMapForallBin.

  Context {Value Value': Type}.

  Fixpoint t_forall_bin_op_aux (m1: total_map) (v2: Value')
           (f: Value -> Value' -> bool) (seen: list string) :=
    match m1 with
    | TDefault v1 => f v1 v2
    | TUpdate m1' k v1 =>
      if k \in seen then
        t_forall_bin_op_aux m1' v2 f seen
      else
        f v1 v2 && t_forall_bin_op_aux m1' v2 f (k::seen)
    end.

  Lemma t_forall_bin_op_aux_spec (m1: total_map) (v2: Value')
        (f: Value -> Value' -> bool) (seen: list string) :
    t_forall_bin_op_aux m1 v2 f seen <->
    (forall k, k \notin seen -> f (m1 k) v2).
  Proof.
    elim: m1 seen => [v seen /= | m Hind k v1 seen /=].
      by split => [// | H]; by apply (H (construct_not_in_list seen)), construct_not_in_list_spec.
      case Hseen: (k \in seen).
    - rewrite Hind.
      split => [Hin k0 HnotIn | Hin k0 /negP Hf]; move: Hseen.
      + case (k =P k0) => [-> Hin2 | //]; autossr.
        move => /negb_true_iff in HnotIn. by rewrite Hin2 in HnotIn.
      + case (k =P k0) => [-> // | /eqP /negb_true_iff Hkk0].
        move => /negP /Hin in Hf.
          by rewrite Hkk0 in Hf.
    - split => [/andP[Hf /Hind Hforall] k0 Hk0notin | H ].
      + case (k =P k0) => [// | Hkk0 ].
        apply Hforall.
          by autossr.
      + move => /negb_true_iff in Hseen.
        apply /andP. split.
        * apply H in Hseen.
            by rewrite eq_refl in Hseen.
        * apply Hind => k0 /=. rewrite in_cons => /norP [/negb_true_iff Hkk0 /H Hnotin].
            by rewrite eq_sym Hkk0 in Hnotin.
  Qed.

  Fixpoint t_forall_bin_op_fix (m1 m2: total_map) (f: Value -> Value' -> bool) (seen: list string):=
    match m2 with
    | TDefault v2 => t_forall_bin_op_aux m1 v2 f seen
    | TUpdate m2' k v2 =>
      if k \in seen then
        t_forall_bin_op_fix m1 m2' f seen
      else
        f (m1 k) v2 && t_forall_bin_op_fix m1 m2' f (k::seen)
    end.

  Lemma t_forall_bin_op_fix_spec (m1 m2: total_map) (f: Value -> Value' -> bool) (seen: list string) :
    t_forall_bin_op_fix m1 m2 f seen <-> forall k, k \notin seen -> f (m1 k) (m2 k).
  Proof.
    elim: m2 m1 seen => [v1 m2 seen /= | m2 Hind k v1 m1 seen /=].
      by split => /t_forall_bin_op_aux_spec.
      case_eq (k \in seen) => Hseen. rewrite Hseen.
    - rewrite Hind.
      split => [Hin k0 HnotIn| HIn k0 Hf]; move: Hseen.
      + case (k =P k0) => [-> | //]; auto.
        move => /negb_true_iff in HnotIn. by rewrite HnotIn.
      + case (k =P k0) => [-> // | Hkk0].
        * move => /negb_true_iff in Hf. by rewrite Hf.
        * move: Hf => /HIn.
            by move: Hkk0 => /eqP /negb_true_iff ->.
    - rewrite Hseen. split => [/andP[Hf /Hind Hforall] k0 Hk0notin | H ].
      + case (k =P k0) => [<- // | Hkk0].
        apply Hforall. rewrite in_cons. apply /norP. split; auto. apply /eqP. auto.
      + apply /andP. split.
        * move => /negb_true_iff in Hseen. apply H in Hseen.
            by rewrite eq_refl in Hseen.
        * apply Hind => v0 /=. rewrite in_cons => /norP [/negb_true_iff Hvv0 /H Hnotin].
            by rewrite eq_sym Hvv0 in Hnotin.
  Qed.

  Definition t_forall_bin_op (m1 m2: total_map) (f: Value -> Value' -> bool) :=
    t_forall_bin_op_fix m1 m2 f nil.

  Theorem t_forall_bin_op_spec (m1 m2: total_map) (f: Value -> Value' -> bool) :
    t_forall_bin_op m1 m2 f <-> forall k, f (m1 k) (m2 k).
  Proof.
    rewrite t_forall_bin_op_fix_spec /=.
    split; auto.
  Qed.

End TotalMapForallBin.

Hint Rewrite @t_forall_bin_op_spec : maprw.

Global Opaque eval_total_map.

(*  _____     _        _ __  __             ____   *)
(* |_   _|__ | |_ __ _| |  \/  | __ _ _ __ |  _ \  *)
(*   | |/ _ \| __/ _` | | |\/| |/ _` | '_ \| | | | *)
(*   | | (_) | || (_| | | |  | | (_| | |_) | |_| | *)
(*   |_|\___/ \__\__,_|_|_|  |_|\__,_| .__/|____/  *)
(*                                   |_|           *)

Section TotalMapD.

  Context {Key: eqType}
          {Value: Type}.

  Inductive total_map_d {default: Value} :=
  | TDDefault
  | TDUpdate (m': total_map_d) (k: Key) (v: Value).

  Fixpoint eval_total_map_d {default: Value} (m: @total_map_d default) (k: Key) :=
    match m with
    | TDDefault => default
    | TDUpdate m' k' v => if k' == k then v else eval_total_map_d m' k
    end.

  Coercion eval_total_map_d : total_map_d >-> Funclass.

End TotalMapD.

(* Notation for a map update *)
Notation "k '|->' v ';' m" := (TDUpdate m k v)
                                (at level 99, v at next level, right associativity).

(* Notation for a default map *)
Notation "'_' '|->' v" := (@TDDefault _ _ v)
                            (at level 99).

Section TotalMapDEqType.

  Context {Key Value: eqType}
          (default: Value).

  Fixpoint eq_total_map_d (m1 m2: @total_map_d Key Value default) :=
    match (m1, m2) with
    | (TDDefault, TDDefault) => true
    | (TDUpdate m1' k1 v1, TDUpdate m2' k2 v2) => (k1 == k2) && (v1 == v2) && (eq_total_map_d m1' m2')
    | _ => false
    end.


  Theorem eq_total_map_dP :
    Equality.axiom (eq_total_map_d).
  Proof.
    elim => [ m2 /= | m1' Hind1 k1 v1 m2 /= ].
    - apply (iffP idP); case m2; autossr.
    - apply (iffP idP) => [ | <- ].
      + case m2 => [ // | m2' k2 v2 /andP[/andP[/eqP -> /eqP ->] /Hind1 ->] //].
      + simplssr. by apply /Hind1.
  Qed.

  Canonical total_map_d_eqMixin := EqMixin (eq_total_map_dP).
  Canonical total_map_d_eqType := Eval hnf in EqType (@total_map_d Key Value default) total_map_d_eqMixin.

End TotalMapDEqType.

(* Important rewrite rules *)
Section TotalMapDRewriteRules.

  Context {Key: eqType}
          {Value: Type}
          {default: Value}
          (k k1 k2: Key)
          (v v1 v2: Value)
          (m: @total_map_d Key Value default).

  Lemma td_apply_empty :
    (_ |-> v) k = v.
  Proof.
      by [].
  Qed.

  Lemma td_update_eq :
    (k |-> v ; m) k = v.
  Proof.
      by autossr.
  Qed.

  Lemma td_update_eq_hyp :
    k1 == k2 -> (k1 |-> v ; m) k2 = v.
  Proof.
      by autossr.
  Qed.

  Theorem td_update_neq :
    k1 != k2 ->
    (k1 |-> v ; m) k2 = m k2.
  Proof.
      by autossr.
  Qed.

  Lemma td_update_shadow :
    eval_total_map_d (k |-> v2 ; k |-> v1 ; m) = eval_total_map_d (k |-> v2 ; m).
  Proof.
    extensionality k' => /=.
      by case (k =P k'); autossr.
  Qed.

  Theorem td_update_same :
    eval_total_map_d (k |-> m k ; m) = eval_total_map_d m.
  Proof.
    extensionality k' => /=.
      by case (k =P k'); autossr.
  Qed.

  Theorem td_update_permute :
    k2 != k1 ->
    eval_total_map_d (k1 |-> v1 ; k2 |-> v2 ; m) =
    eval_total_map_d (k2 |-> v2 ; k1 |-> v1 ; m).
  Proof.
    move => Hne.
    extensionality k' => /=.
      by case (k1 =P k'); autossr.
  Qed.

End TotalMapDRewriteRules.

Hint Rewrite @td_apply_empty @td_update_eq @td_update_eq_hyp @td_update_neq @td_update_shadow @td_update_same using by first [liassr | autossr ] : maprw.

(* Pointwise operations on one or multiple maps *)

Section TotalMapDPointwiseUn.

  Context {Key: eqType}
          {Value Value': Type}
          {default: Value}.

  Fixpoint td_pointwise_un_op (m: @total_map_d Key Value default) (f: Value -> Value') : @total_map_d Key Value' (f default) :=
    match m with
    | TDDefault => TDDefault
    | TDUpdate m' k v => (k |-> f v; td_pointwise_un_op m' f)
    end.

  Theorem td_pointwise_un_op_spec (m: @total_map_d Key Value default) (f: Value -> Value') (k: Key) :
    td_pointwise_un_op m f k = f (m k).
  Proof.
    elim: m => [ // | m' Hind k' v' /= ]. rewrite Hind.
      by case (k' =P k); autossr.
  Qed.

  Fixpoint td_pointwise_un_op_in_seq (m: @total_map_d Key Value default) (f: Value -> Value) (l: seq Key) :=
    match l with
    | [::] => m
    | a::l' => (a |-> f (m a); td_pointwise_un_op_in_seq m f l')
    end.

  Theorem td_pointwise_un_op_in_seq_spec (m: @total_map_d Key Value default) (f: Value -> Value) (l: seq Key) :
    forall x, (td_pointwise_un_op_in_seq m f l) x = if x \in l then f (m x) else (m x).
  Proof.
    elim: l => [ // | k l Hind x /=]. rewrite Hind.
      by case (k =P x); autossr.
  Qed.

End TotalMapDPointwiseUn.

Hint Rewrite @td_pointwise_un_op_spec @td_pointwise_un_op_in_seq_spec : maprw.

Global Opaque eval_total_map_d.

Ltac simpl_map_ := repeat (autorewrite with maprw; simplssr).
Ltac simpl_map := reflect_ne_in simpl_map_.

Ltac auto_map := intros ; simpl_map ; autossr.
