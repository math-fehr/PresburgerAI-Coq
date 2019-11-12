From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.ssrnat eqtype.
From Coq Require Export Arith.Arith Bool.Bool.
From Coq Require Import Logic.FunctionalExtensionality.
From PolyAI Require Export ssrstring.

(* This code is inspired from the programming language fundations book *)

Local Open Scope string_scope.
Local Open Scope list_scope.

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

Fixpoint list_string_in (l: list string) (s: string) :=
  match l with
  | nil => false
  | s'::l' => (s =? s')%string || list_string_in l' s
  end.

Theorem list_string_in_spec:
  forall l s, reflect (List.In s l) (list_string_in l s).
Proof.
  elim => [s // | a l Hind s /=].
  - apply: (iffP idP) => [// | Hne // ].
  - apply: (iffP idP) => [ /orP[/eqb_spec Heq | HIn] | [-> | HIn]]; auto.
    + right. by apply /Hind.
    + apply /orP. left. by apply eqb_refl.
    + apply /orP. right. by apply /Hind.
Qed.

Theorem list_string_in_append:
  forall l1 l2 s, list_string_in (l1++l2) s = list_string_in l1 s || list_string_in l2 s.
Proof.
  elim => [ s l // | s l Hind l2 s' /=].
    by case (s' =? s) => //=.
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
  forall l x, List.In x l -> length (construct_not_in_list l) > length x.
Proof.
  elim => [x Hin /= // | a l Hind x /= [Heqxa | Hinl]].
  - rewrite Heqxa string_append_length repeat_string_length.
    rewrite {1}(plus_n_O (length x)).
    by rewrite ltn_add2l construct_not_in_list_length.
  - rewrite string_append_length ltn_addl => //.
    by auto.
Qed.

Theorem construct_not_in_list_spec:
  forall l, not (List.In (construct_not_in_list l) l).
Proof.
  move => l HIn.
  apply construct_not_in_list_length_forall in HIn.
    by rewrite ltnn in HIn.
Qed.

Fixpoint forall_bin_op_aux {Value: Type} (m1: total_map) (v2: Value)
         (f: Value -> Value -> bool) (seen: list string) :=
  match m1 with
  | TEmpty v1 => f v1 v2
  | TUpdate m1' k v1 =>
    if list_string_in seen k then
      forall_bin_op_aux m1' v2 f seen
    else
      f v1 v2 && forall_bin_op_aux m1' v2 f (k::seen)
  end.

Lemma forall_bin_op_aux_spec {Value: Type} {m1: total_map} (v2: Value)
      (f: Value -> Value -> bool) (seen: list string) :
  forall_bin_op_aux m1 v2 f seen <->
                       (forall k, not (List.In k seen) -> f (m1 k) v2).
Proof.
  elim: m1 seen => [v seen /= | m Hind k v1 seen /=].
    by split => [// | H]; apply (H (construct_not_in_list seen)), construct_not_in_list_spec.
  case (list_string_in_spec seen k) => Hseen.
  - rewrite Hind.
    split => [Hin k0 HnotIn | Hin k0 Hf]; move: Hseen.
    + case (k =P k0) => [-> | //]; by auto.
    + case (k =P k0) => [-> // | /eqP /negb_true_iff Hkk0].
      apply Hin in Hf.
        by rewrite Hkk0 in Hf.
  - split => [/andP[Hf /Hind Hforall] k0 Hk0notin | H ].
    + case (k =P k0) => [// | Hkk0 ].
      apply Hforall.
      by case.
    + apply /andP. split.
      * apply H in Hseen.
          by rewrite eq_refl in Hseen.
      * apply Hind => k0 /= /Decidable.not_or [/eqP /negb_true_iff Hkk0 /H Hnotin].
          by rewrite Hkk0 in Hnotin.
Qed.

Fixpoint forall_bin_op_fix {Value: Type} (m1 m2: total_map) (f: Value -> Value -> bool) (seen: list string):=
  match m2 with
  | TEmpty v2 => forall_bin_op_aux m1 v2 f seen
  | TUpdate m2' k v2 =>
    if list_string_in seen k then
      forall_bin_op_fix m1 m2' f seen
    else
      f (m1 k) v2 && forall_bin_op_fix m1 m2' f (k::seen)
  end.

Lemma forall_bin_op_fix_spec {Value: Type} (m1 m2: total_map) (f: Value -> Value -> bool) (seen: list string) :
  forall_bin_op_fix m1 m2 f seen <-> forall k, not (List.In k seen) -> f (m1 k) (m2 k).
Proof.
  elim: m2 m1 seen => [v1 m2 seen /= | m2 Hind k v1 m1 seen /=].
    by split => /forall_bin_op_aux_spec.
  case (list_string_in_spec seen k) => Hseen.
  - rewrite Hind.
    split => [Hin k0 HnotIn| HIn k0 Hf]; move: Hseen.
    + case (k =P k0) => [-> | //]; by auto.
    + case (k =P k0) => [-> // | Hkk0].
      move: Hf => /HIn.
      by move: Hkk0 => /eqP /negb_true_iff ->.
  - split => [/andP[Hf /Hind Hforall] k0 Hk0notin | H ].
    + case (k =P k0) => [<- // | Hkk0].
      apply Hforall.
      by case.
    + apply /andP. split.
      * apply H in Hseen.
          by rewrite eq_refl in Hseen.
      * apply Hind => v0 /= /Decidable.not_or [/eqP /negb_true_iff Hvv0 /H Hnotin].
          by rewrite Hvv0 in Hnotin.
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
       | _ => rewrite //=
       end.

Global Opaque eval_map.
