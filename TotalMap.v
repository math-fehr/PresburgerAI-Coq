From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect.ssrnat.
From Coq Require Export Arith.Arith Bool.Bool Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.

(* This code is inspired from the programming language fundations book *)

Local Open Scope string_scope.
Local Open Scope list_scope.

(* Representation of a total map with finite non-default values *)

Inductive total_map (A: Type) :=
| TEmpty (v: A)
| TUpdate (m: total_map A) (x: string) (v: A)
.

(* Notation for a default map *)
Notation "'_' '!->' v" := (TEmpty _ v)
  (at level 100, right associativity).

(* Notation for a map update *)
Notation "x '!->' v ';' m" := (TUpdate _ m x v)
                              (at level 100, v at next level, right associativity).


(* Evaluate a map on a point*)
Fixpoint eval_map {A: Type} (m: @total_map A) (x: string) :=
  match m with
  | TEmpty v => v
  | TUpdate m' x' v => if x' =? x then v else eval_map m' x
  end.

(* Notation for evaluation *)
Notation "m [| x |] " := (eval_map m x) (at level 65).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v)[|x|] = v.
Proof.
  by [].
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) (x: string) (v: A),
    (x !-> v ; m)[|x|] = v.
Proof.
  move => A m x v /=.
  by rewrite eqb_refl.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) (x1 x2: string) (v: A),
    x1 <> x2 ->
    (x1 !-> v ; m)[|x2|] = m[|x2|].
Proof.
  by move => A m x1 x2 v /eqb_neq /= ->.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) (x: string) (v1 v2: A),
    eval_map (x !-> v2 ; x !-> v1 ; m) = eval_map (x !-> v2 ; m).
Proof.
  move => A m x v1 v2 /=.
  extensionality x'.
  by case (x =? x').
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) (x: string),
    eval_map (x !-> eval_map m x ; m) = eval_map m.
Proof.
  move => A m x /=.
  extensionality x'.
  by case (eqb_spec x x') => [<- | _].
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  (v1 v2: A) (x1 x2: string),
    x2 <> x1 ->
    eval_map (x1 !-> v1 ; x2 !-> v2 ; m) =
    eval_map (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  move => A m v1 v2 x1 x2 /eqb_neq Hne.
  extensionality x'.
  case (eqb_spec x1 x') => [ <- /= | /eqb_neq Hne' /= ].
  - by rewrite eqb_refl Hne.
  - by rewrite Hne'.
Qed.

Require Import Coq.ZArith.BinInt.

Fixpoint pointwise_un_op {A B: Type} (m: total_map A) (f: A -> B) :=
  match m with
  | TEmpty x => (_ !-> f x)
  | TUpdate m1' v x => let new_m := pointwise_un_op m1' f in
                      (v !-> f x; new_m)
  end.

Theorem pointwise_un_op_spec {A B: Type} :
  forall m (f: A -> B) v, (pointwise_un_op m f)[|v|] = f (m[|v|]).
Proof.
  elim => [// | m Hind v x f v' /=].
  rewrite Hind.
    by case (v =? v').
Qed.

Fixpoint pointwise_bin_op_aux {A B C: Type} (m1: total_map A) (x2: B) (f: A -> B -> C) :=
  match m1 with
  | TEmpty x1 => (_ !-> f x1 x2)
  | TUpdate m1' v x1 => let new_m := pointwise_bin_op_aux m1' x2 f in
                       (v !-> f x1 x2; new_m)
  end.

Lemma pointwise_bin_op_aux_spec {A B C: Type} :
  forall m1 x2 (f: A -> B -> C) s, (pointwise_bin_op_aux m1 x2 f)[|s|] = f (m1[|s|]) x2.
Proof.
  elim => [// | m H s x1 x2 f s' /=].
  rewrite H.
    by case (eqb_spec s s').
Qed.

Fixpoint pointwise_bin_op {A B C: Type} (m1: total_map A) (m2: total_map B) (f: A -> B -> C) :=
  match m2 with
  | TEmpty x2 => pointwise_bin_op_aux m1 x2 f
  | TUpdate m2' v x2 => let new_m := pointwise_bin_op m1 m2' f in
                       (v !-> (f (m1[|v|]) x2); new_m)
  end.

Theorem pointwise_bin_op_spec {A B C: Type} :
  forall m1 m2 (f: A -> B -> C) x, (pointwise_bin_op m1 m2 f)[|x|] = f (m1[|x|]) (m2[|x|]).
Proof.
  move => m1 m2.
  elim: m2 m1 => [v m1 f x | m Hind x v m1 f x0 /=].
  - by apply pointwise_bin_op_aux_spec.
  - rewrite Hind.
    case (eqb_spec x x0) => [ -> // | //].
Qed.

Ltac simpl_totalmap :=
  repeat (
      rewrite ?t_apply_empty ?t_update_eq ?t_update_shadow ?t_update_same ?eqb_refl%string
              ?pointwise_un_op_spec ?pointwise_bin_op_spec /=
    ).

Ltac simpl_totalmap_Z :=
  repeat ( simpl_totalmap; rewrite ?Z.eqb_refl ).


Fixpoint list_string_in (l: list string) (s: string) :=
  match l with
  | nil => false
  | s'::l' => (s =? s')%string || list_string_in l' s
  end.

Theorem list_string_in_spec : forall l s, reflect (List.In s l) (list_string_in l s).
Proof.
  elim => [s // | a l Hind s /=].
  - apply: (iffP idP) => [// | Hne // ].
  - apply: (iffP idP) => [ /orP[/eqb_spec Heq | HIn] | [-> | HIn]].
    + by left.
    + right. by apply /Hind.
    + apply /orP. left. by apply eqb_refl.
    + apply /orP. right. by apply /Hind.
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
    by rewrite Hind.
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
  elim => [x Hin /= | a l Hind x /= [Heqxa | Hinl]].
  - by apply List.in_nil in Hin.
  - rewrite Heqxa string_append_length repeat_string_length.
    rewrite {1}(plus_n_O (length x)).
    by rewrite ltn_add2l construct_not_in_list_length.
  - rewrite string_append_length ltn_addl => [// | ].
      by apply Hind.
Qed.

Theorem construct_not_in_list_spec:
  forall l, not (List.In (construct_not_in_list l) l).
Proof.
  move => l HIn.
  apply construct_not_in_list_length_forall in HIn.
    by rewrite ltnn in HIn.
Qed.

Fixpoint forall_bin_op_aux {A: Type} (m1: total_map A) (x2: A) (f: A -> A -> bool) (seen: list string):=
  match m1 with
  | TEmpty x1 => f x1 x2
  | TUpdate m1' v x1 =>
    if list_string_in seen v then
      forall_bin_op_aux m1' x2 f seen
    else
      f x1 x2 && forall_bin_op_aux m1' x2 f (v::seen)
  end.

Lemma forall_bin_op_aux_spec {A: Type} :
  forall m1 (x2: A) f seen, forall_bin_op_aux m1 x2 f seen <->
                       (forall v, not (List.In v seen) -> f (m1[|v|]) x2).
Proof.
  elim => [v x2 f seen /= | m Hind v x1 x2 f seen /=].
    by split => [// | H]; apply (H (construct_not_in_list seen)), construct_not_in_list_spec.
  case (list_string_in seen v) eqn:Hseen.
  - rewrite Hind.
    split => [Hin v0 HnotIn| Hin v0 Hf].
    + case (v =? v0) eqn: Hvv0; last first. by apply Hin.
        by move: Hvv0 Hseen => /eqb_spec -> /list_string_in_spec Hseen.
    + case (v =? v0) eqn: Hvv0; last first. apply Hin in Hf. by rewrite Hvv0 in Hf.
        by move: Hvv0 Hseen => /eqb_spec -> /list_string_in_spec Hseen.
  - split => [/andP[Hf /Hind Hforall] v0 Hv0notin | H ].
    + case (v =? v0) eqn:Hvv0 => [// | ].
      move: Hvv0 => /eqb_spec Hvv0.
      apply Hforall.
      by case.
    + apply /andP. split.
      * move: Hseen => /list_string_in_spec Hseen.
        apply H in Hseen.
          by rewrite eqb_refl in Hseen.
      * apply Hind => v0 /= /Decidable.not_or [/eqb_spec Hvv0 Hnotin].
        apply H in Hnotin.
        rewrite /is_true in Hvv0.
        apply negb_true_iff in Hvv0.
          by rewrite Hvv0 in Hnotin.
Qed.

Fixpoint forall_bin_op_fix {A: Type} (m1 m2: total_map A) (f: A -> A -> bool) (seen: list string):=
  match m2 with
  | TEmpty x2 => forall_bin_op_aux m1 x2 f seen
  | TUpdate m2' v x2 =>
    if list_string_in seen v then
      forall_bin_op_fix m1 m2' f seen
    else
      f (m1[|v|]) x2 && forall_bin_op_fix m1 m2' f (v::seen)
  end.

Lemma forall_bin_op_fix_spec {A: Type} :
  forall (m1 m2: @total_map A) f seen, forall_bin_op_fix m1 m2 f seen <->
                                  forall v, not (List.In v seen) -> f (m1[|v|]) (m2[|v|]).
Proof.
  move => m1 m2; move: m2 m1.
  elim => [m1 m2 f seen /= | m2 Hind v x1 m1 f seen /=].
    by split => /forall_bin_op_aux_spec //.
  case (list_string_in seen v) eqn:Hseen; move: Hseen => /list_string_in_spec Hseen.
  - rewrite Hind.
    split => [Hin v0 HnotIn| Hin v0 Hf].
    + case (v =? v0) eqn: Hvv0; last first. by apply Hin.
        by move: Hvv0 Hseen => /eqb_spec ->.
    + case (v =? v0) eqn: Hvv0; last first. apply Hin in Hf. by rewrite Hvv0 in Hf.
        by move: Hvv0 Hseen => /eqb_spec ->.
  - split => [/andP[Hf /Hind Hforall] v0 Hv0notin | H ].
    + case (v =? v0) eqn:Hvv0 => [ | ].
      * by move: Hvv0 => /eqb_spec <-.
      * apply Hforall.
        move: Hvv0 => /eqb_spec Hvv0.
        by case.
    + apply /andP. split.
      * apply H in Hseen.
          by rewrite eqb_refl in Hseen.
      * apply Hind => v0 /= /Decidable.not_or [/eqb_spec Hvv0 Hnotin].
        apply H in Hnotin.
        rewrite /is_true in Hvv0.
        apply negb_true_iff in Hvv0.
          by rewrite Hvv0 in Hnotin.
Qed.

Definition forall_bin_op {A: Type} (m1 m2: total_map A) (f: A -> A -> bool) :=
  forall_bin_op_fix m1 m2 f nil.

Theorem forall_bin_op_spec {A: Type} :
  forall (m1 m2: @total_map A) f, forall_bin_op m1 m2 f <-> forall v, f (m1[|v|]) (m2[|v|]).
Proof.
  move => m1 m2 f.
  unfold forall_bin_op.
  rewrite forall_bin_op_fix_spec /=.
  split => [H | H v _].
  - auto.
  - by apply H.
Qed.
