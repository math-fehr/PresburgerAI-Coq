From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.ssrnat eqtype seq.
From Coq Require Export Arith.Arith Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From PolyAI Require Export ssrstring.

(* This code is inspired from the programming language fundations book *)

Local Open Scope string_scope.
Local Open Scope list_scope.


(*  _____     _        _ __  __              *)
(* |_   _|__ | |_ __ _| |  \/  | __ _ _ __   *)
(*   | |/ _ \| __/ _` | | |\/| |/ _` | '_ \  *)
(*   | | (_) | || (_| | | |  | | (_| | |_) | *)
(*   |_|\___/ \__\__,_|_|_|  |_|\__,_| .__/  *)
(*                                   |_|     *)


(* Representation of a total map with finite non-default values *)

Inductive total_map {Key: eqType} {Value} :=
| TEmpty (v: Value)
| TUpdate (m: total_map) (k: Key) (v: Value)
.

(* Notation for a default map *)
Notation "'_' '!->' v" := (TEmpty v)
  (at level 100, right associativity).

(* Notation for a map update *)
Notation "k '!->' v ';' m" := (TUpdate m k v)
                                (at level 100, v at next level, right associativity).

Fixpoint eqmap {Key: eqType} {Value: eqType} (m1 m2: @total_map Key Value) :=
  match (m1, m2) with
  | (TEmpty v1, TEmpty v2) => v1 == v2
  | (TUpdate m1' k1 v1, TUpdate m2' k2 v2) => (eqmap m1' m2') && (k1 == k2) && (v1 == v2)
  | _ => false
  end.

Theorem eqmapP {Key: eqType} {Value: eqType} :
  Equality.axiom (@eqmap Key Value).
Proof.
  elim => [ v1 m2 /= | m1' Hind1 k1 v1 m2 /= ].
  - apply (iffP idP).
    + by case m2 => [ v2 /eqP -> // | // ].
    + case m2 => [ v2 Heq | // ].
        by injection Heq => ->.
  - apply (iffP idP) => [ | <- ].
    + by case m2 => [ // | m2' k2 v2 /andP[/andP[/Hind1 -> /eqP ->] /eqP ->]].
    + rewrite !eq_refl.
        by have -> : (eqmap m1' m1') by apply /Hind1.
Qed.

Canonical total_map_eqMixin {Key Value: eqType} := EqMixin (@eqmapP Key Value).
Canonical total_map_eqType {Key Value: eqType} := Eval hnf in EqType (@total_map Key Value) total_map_eqMixin.

(* Evaluate a map on a point*)
Fixpoint eval_map {Key: eqType} {Value: Type} (m: @total_map Key Value) (k: Key) :=
  match m with
  | TEmpty v => v
  | TUpdate m' k' v => if k' == k then v else eval_map m' k
  end.

(* Coercion for evaluation *)
Coercion eval_map : total_map >-> Funclass.

(* Useful lemmas and theorems *)

Lemma t_apply_empty {Key: eqType} {Value: Type} (k: Key) (v: Value) :
    (_ !-> v) k = v.
Proof.
  by [].
Qed.

Lemma t_update_eq {Key : eqType} {Value: Type} (m : total_map) (k: Key) (v: Value) :
    (k !-> v ; m) k = v.
Proof.
  by rewrite /= eq_refl.
Qed.

Theorem t_update_neq {Key: eqType} {Value : Type} (m : total_map) (k1 k2: Key) (v: Value) :
    k1 != k2 ->
    (k1 !-> v ; m) k2 = m k2.
Proof.
  by move => /negb_true_iff /= ->.
Qed.

Lemma t_update_shadow {Key: eqType} {Value: Type} (m : total_map) (k: Key) (v1 v2: Value) :
    eval_map (k !-> v2 ; k !-> v1 ; m) = eval_map (k !-> v2 ; m).
Proof.
  extensionality k' => /=.
  by case (k == k').
Qed.

Theorem t_update_same {Key : eqType} {Value: Type} (m : @total_map Key Value) (k: Key) :
    eval_map (k !-> m k ; m) = eval_map m.
Proof.
  extensionality k' => /=.
  by case (k =P k') => [-> | ].
Qed.

Theorem t_update_permute {Key : eqType} {Value: Type} (m : total_map) (k1 k2: Key) (v1 v2: Value) :
    k2 != k1 ->
    eval_map (k1 !-> v1 ; k2 !-> v2 ; m) =
    eval_map (k2 !-> v2 ; k1 !-> v1 ; m).
Proof.
  move => /negb_true_iff Hne /=.
  extensionality k'.
  case (k1 =P k') => [ <- /= | _ //].
  - by rewrite Hne.
Qed.

Require Import Coq.ZArith.BinInt.

(* Pointwise operations on one or multiple maps *)

Fixpoint pointwise_un_op {Key: eqType} {Value Value': Type} (m: @total_map Key Value) (f: Value -> Value') :=
  match m with
  | TEmpty v => (_ !-> f v)
  | TUpdate m1' k v => let new_m := pointwise_un_op m1' f in
                      (k !-> f v; new_m)
  end.

Theorem pointwise_un_op_spec {Key: eqType} {Value Value': Type} (m: @total_map Key Value) (f: Value -> Value') (k: Key) :
  (pointwise_un_op m f) k = f (m k).
Proof.
  elim: m f k => [// | m Hind k v f k' /=].
  rewrite Hind.
  by case (k == k').
Qed.

Fixpoint pointwise_un_op_in_seq {Key: eqType} {Value: Type} (m: @total_map Key Value) (f: Value -> Value) (l: seq Key) :=
  match l with
  | [::] => m
  | a::l' => (a !-> f (m a); pointwise_un_op_in_seq m f l')
  end.

Theorem pointwise_un_op_in_seq_spec {Key: eqType} {Value: Type} (m: @total_map Key Value) (f: Value -> Value) (l: seq Key) :
  forall x, (pointwise_un_op_in_seq m f l) x = if x \in l then f (m x) else (m x).
Proof.
  move => x. elim: l => [// | k l'].
  rewrite in_cons. case: (x \in l') => Hind /=; case: (x =P k) => [-> | /eqP /negb_true_iff].
  - by rewrite eq_refl.
  - by rewrite eq_sym => ->.
  - by rewrite eq_refl.
  - by rewrite eq_sym => ->.
Qed.

Fixpoint pointwise_bin_op_aux {Key: eqType} {Value1 Value2 Value3: Type} (m1: @total_map Key Value1)
         (k2: Value2) (f: Value1 -> Value2 -> Value3) :=
  match m1 with
  | TEmpty k1 => (_ !-> f k1 k2)
  | TUpdate m1' v k1 => let new_m := pointwise_bin_op_aux m1' k2 f in
                       (v !-> f k1 k2; new_m)
  end.

Lemma pointwise_bin_op_aux_spec {Key: eqType} {Value1 Value2 Value3: Type} (m1: @total_map Key Value1)
      (v2: Value2) (f: Value1 -> Value2 -> Value3) (k: Key):
  (pointwise_bin_op_aux m1 v2 f) k = f (m1 k) v2.
Proof.
  elim: m1 => [// | m1 Hind k1 v1 /=].
  rewrite Hind.
  by case (k1 == k).
Qed.

Fixpoint pointwise_bin_op {Key: eqType} {Value1 Value2 Value3: Type} (m1: @total_map Key Value1)
         (m2: @total_map Key Value2) (f: Value1 -> Value2 -> Value3) :=
  match m2 with
  | TEmpty v2 => pointwise_bin_op_aux m1 v2 f
  | TUpdate m2' k v2 => let new_m := pointwise_bin_op m1 m2' f in
                       (k !-> (f (m1 k) v2); new_m)
  end.

Theorem pointwise_bin_op_spec {Key: eqType} {Value1 Value2 Value3: Type} (m1: @total_map Key Value1)
         (m2: @total_map Key Value2) (f: Value1 -> Value2 -> Value3) (k: Key):
  (pointwise_bin_op m1 m2 f) k = f (m1 k) (m2 k).
Proof.
  elim: m2 m1 => [v m1 | m2 Hind k2 v2 m1 /=].
  - by apply pointwise_bin_op_aux_spec.
  - rewrite Hind.
    by case (k2 =P k) => [-> // | //].
Qed.

Local Open Scope string_scope.

Lemma ne_length_impl_ne :
  forall s1 s2, length s1 <> length s2 -> s1 <> s2.
Proof.
  move => s1 s2 HLength Heq.
  rewrite Heq in HLength.
    by case HLength.
Qed.

Lemma string_append_length :
  forall s1 s2, length (s1 ++ s2) = length s1 + length s2.
Proof.
  elim => [s2 // | a s1 Hind s2 /=].
    by rewrite Hind.
Qed.

Fixpoint repeat_string (n: nat) :=
  match n with
  | O => ""
  | S n' => "X" ++ (repeat_string n')
  end.

Lemma repeat_string_length :
  forall n, length (repeat_string n) = n.
Proof.
  elim => [// | n Hind /=].
  by auto.
Qed.

Fixpoint construct_not_in_list (l: list string) :=
  match l with
  | nil => "X"
  | a::l' => (repeat_string (length a)) ++ (construct_not_in_list l')
  end.

Lemma construct_not_in_list_length :
  forall l, 0 < length (construct_not_in_list l).
Proof.
  elim => [// | a l Hind /=].
  rewrite string_append_length.
    by apply ltn_addl.
Qed.

Theorem construct_not_in_list_length_forall :
  forall l x, x \in l -> length (construct_not_in_list l) > length x.
Proof.
  elim => [x Hin /= // | a l Hind x /=].
  rewrite in_cons => /orP [/eqP -> | Hinl].
  - rewrite string_append_length repeat_string_length.
    rewrite {1}(plus_n_O (length a)).
    by rewrite ltn_add2l construct_not_in_list_length.
  - rewrite string_append_length ltn_addl => //.
    by auto.
Qed.

Theorem construct_not_in_list_spec:
  forall l, (construct_not_in_list l) \notin l.
Proof.
  move => l. apply /negP => HIn.
  apply construct_not_in_list_length_forall in HIn.
    by rewrite ltnn in HIn.
Qed.

Fixpoint forall_bin_op_aux {Value: Type} (m1: total_map) (v2: Value)
         (f: Value -> Value -> bool) (seen: list string) :=
  match m1 with
  | TEmpty v1 => f v1 v2
  | TUpdate m1' k v1 =>
    if k \in seen then
      forall_bin_op_aux m1' v2 f seen
    else
      f v1 v2 && forall_bin_op_aux m1' v2 f (k::seen)
  end.

Lemma forall_bin_op_aux_spec {Value: Type} {m1: total_map} (v2: Value)
      (f: Value -> Value -> bool) (seen: list string) :
  forall_bin_op_aux m1 v2 f seen <->
                       (forall k, k \notin seen -> f (m1 k) v2).
Proof.
  elim: m1 seen => [v seen /= | m Hind k v1 seen /=].
    by split => [// | H]; apply (H (construct_not_in_list seen)), construct_not_in_list_spec.
    case_eq (k \in seen) => Hseen.
  - rewrite Hseen Hind.
    split => [Hin k0 HnotIn | Hin k0 /negP Hf]; move: Hseen.
    + case (k =P k0) => [-> Hin2 | //]; auto.
      move => /negb_true_iff in HnotIn. by rewrite Hin2 in HnotIn.
    + case (k =P k0) => [-> // | /eqP /negb_true_iff Hkk0].
      move => /negP in Hf. apply Hin in Hf.
        by rewrite Hkk0 in Hf.
  - rewrite Hseen. split => [/andP[Hf /Hind Hforall] k0 Hk0notin | H ].
    + case (k =P k0) => [// | Hkk0 ].
      apply Hforall. rewrite in_cons. apply /norP. split; auto.
      apply /eqP. auto.
    + move => /negb_true_iff in Hseen.
      apply /andP. split.
      * apply H in Hseen.
          by rewrite eq_refl in Hseen.
      * apply Hind => k0 /=. rewrite in_cons => /norP [/negb_true_iff Hkk0 /H Hnotin].
          by rewrite eq_sym Hkk0 in Hnotin.
Qed.

Fixpoint forall_bin_op_fix {Value: Type} (m1 m2: total_map) (f: Value -> Value -> bool) (seen: list string):=
  match m2 with
  | TEmpty v2 => forall_bin_op_aux m1 v2 f seen
  | TUpdate m2' k v2 =>
    if k \in seen then
      forall_bin_op_fix m1 m2' f seen
    else
      f (m1 k) v2 && forall_bin_op_fix m1 m2' f (k::seen)
  end.

Lemma forall_bin_op_fix_spec {Value: Type} (m1 m2: total_map) (f: Value -> Value -> bool) (seen: list string) :
  forall_bin_op_fix m1 m2 f seen <-> forall k, k \notin seen -> f (m1 k) (m2 k).
Proof.
  elim: m2 m1 seen => [v1 m2 seen /= | m2 Hind k v1 m1 seen /=].
    by split => /forall_bin_op_aux_spec.
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

Definition forall_bin_op {Value: Type} (m1 m2: total_map) (f: Value -> Value -> bool) :=
  forall_bin_op_fix m1 m2 f nil.

Theorem forall_bin_op_spec {Value: Type} (m1 m2: total_map) (f: Value -> Value -> bool) :
  forall_bin_op m1 m2 f <-> forall k, f (m1 k) (m2 k).
Proof.
  rewrite forall_bin_op_fix_spec /=.
  split; auto.
Qed.

(* Useful tactic which apply known lemmas *)

Ltac simpl_totalmap :=
repeat match goal with
       | [ |- context[eval_map (_ !-> _) _] ] => rewrite t_apply_empty
       | [ |- context[eval_map (?k !-> _ ; _) ?k]] => rewrite t_update_eq
       | [ H : ?k1 <> ?k2 |- _ ] => move: H => /eqP H

       | [ H : is_true (?k1 != ?k2) |- context[eval_map (?k1 !-> _ ; _) ?k2] ] => rewrite (t_update_neq _ _ _ _ H)
       | [ H : is_true (?k2 != ?k1) |- context[eval_map (?k1 !-> _ ; _) ?k2] ] =>
         rewrite eq_sym in H; rewrite (t_update_neq _ _ _ _ H); rewrite eq_sym in H
       | [ |- context[eval_map (?k1 !-> _ ; ?m) ?k2]] => rewrite (t_update_neq m k1 k2 _); last first; [ by [] | idtac ]
       | [ |- context[eval_map (?k !-> _ ; ?k !-> _ ; _)]] => rewrite t_update_shadow
       | [ |- context[eval_map (?k !-> eval_map ?m ?k ; ?m)]] => rewrite t_update_same
       | [ |- context[(?k == ?k)]] => rewrite eq_refl
       | [ |- context[eval_map (pointwise_un_op _ _) _]] => rewrite pointwise_un_op_spec
       | [ |- context[eval_map (pointwise_bin_op _ _ _) _]] => rewrite pointwise_bin_op_spec
       | [ |- is_true (forall_bin_op _ _ _)] => apply forall_bin_op_spec
       | [ H : is_true ?x |- context[?x]] => rewrite H
       | [ H : is_true (?x != ?y) |- context[?x == ?y]] => rewrite ?(ifN_eq _ _ H) ?(ifN_eqC _ _ H)
       | _ => rewrite //=; auto
       end.

Global Opaque eval_map.

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


Section PartialMapTheorems.

  Context {Key: eqType}
          {Value Value' Value'': Type}.

  (* Useful lemmas and theorems *)

  Lemma p_apply_empty (k: Key) :
    @PEmpty Key Value k = None.
  Proof.
      by [].
  Qed.

  Lemma p_update_eq (m : partial_map) (k: Key) (v: Value) :
    (k !!-> v ; m) k = Some v.
  Proof.
      by rewrite /= eq_refl.
  Qed.

  Theorem p_update_neq (m : partial_map) (k1 k2: Key) (v: Value) :
    k1 != k2 ->
    (k1 !!-> v ; m) k2 = m k2.
  Proof.
      by move => /negb_true_iff /= ->.
  Qed.

  Lemma p_update_shadow (m : partial_map) (k: Key) (v1 v2: Value) :
    eval_partial_map (k !!-> v2 ; k !!-> v1 ; m) = eval_partial_map (k !!-> v2 ; m).
  Proof.
    extensionality k' => /=.
      by case (k =P k').
  Qed.

  Theorem p_update_permute (m : partial_map) (k1 k2: Key) (v1 v2: Value) :
    k2 != k1 ->
    eval_partial_map (k1 !!-> v1 ; k2 !!-> v2 ; m) =
    eval_partial_map (k2 !!-> v2 ; k1 !!-> v1 ; m).
  Proof.
    move => /negb_true_iff Hne /=.
    extensionality k'.
    case (k1 =P k') => [ <- /= | _ //].
      by rewrite Hne.
  Qed.

  (* Pointwise operations on one or multiple maps *)

  Fixpoint p_pointwise_un_op (m: @partial_map Key Value) (f: Value -> Value') :=
    match m with
    | PEmpty => PEmpty
    | PUpdate m1' k v => (k !!-> f v; p_pointwise_un_op m1' f)
    end.

  Theorem p_pointwise_un_op_spec (m: @partial_map Key Value) (f: Value -> Value') (k: Key) :
    (p_pointwise_un_op m f) k = option_map f (m k).
  Proof.
    elim: m f k => [// | m Hind k v f k' /=].
    rewrite Hind.
      by case (k == k').
  Qed.

End PartialMapTheorems.


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
    + by case m2 => [ // | m2' k2 v2 /andP[/andP[/Hind1 -> /eqP ->] /eqP ->]].
    + rewrite !eq_refl.
        by have -> : (eq_partial_map m1' m1') by apply /Hind1.
Qed.

Canonical partial_map_eqMixin {Key Value: eqType} := EqMixin (@eq_partial_mapP Key Value).
Canonical partial_map_eqType {Key Value: eqType} := Eval hnf in EqType (@partial_map Key Value) partial_map_eqMixin.


(* Useful tactic which apply known lemmas *)

Ltac simpl_partialmap :=
repeat match goal with
       | [ |- context[eval_partial_map PEmpty _] ] => rewrite p_apply_empty
       | [ |- context[eval_partial_map (?k !!-> _ ; _) ?k]] => rewrite p_update_eq
       | [ H : ?k1 <> ?k2 |- _ ] => move: H => /eqP H
       | [ H : is_true (?k1 != ?k2) |- context[eval_partial_map (?k1 !!-> _ ; _) ?k2] ] => rewrite (p_update_neq _ _ _ _ H)
       | [ H : is_true (?k2 != ?k1) |- context[eval_partial_map (?k1 !!-> _ ; _) ?k2] ] =>
         rewrite eq_sym in H; rewrite (p_update_neq _ _ _ _ H); rewrite eq_sym in H
       | [ |- context[eval_partial_map (?k1 !!-> _ ; ?m) ?k2]] => rewrite (p_update_neq m k1 k2 _); last first; [ by [] | idtac ]
       | [ |- context[eval_partial_map (?k !!-> _ ; ?k !!-> _ ; _)]] => rewrite p_update_shadow
       | [ |- context[(?k == ?k)]] => rewrite eq_refl
       | [ |- context[eval_partial_map (p_pointwise_un_op _ _) _]] => rewrite p_pointwise_un_op_spec
       | [ H : is_true ?x |- context[?x]] => rewrite H
       | [ H : is_true (?x != ?y) |- context[?x == ?y]] => rewrite ?(ifN_eq _ _ H) ?(ifN_eqC _ _ H)
       | _ => rewrite //=; auto
       end.

Global Opaque eval_partial_map.
