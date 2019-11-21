From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export TotalMap ssrZ ssrstring.
Require Export Coq.Sets.Ensembles.
Require Export Coq.ZArith.BinInt.

Require Import String.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* An affine function *)

Inductive Aff :=
| AConst (c: Z)
| AVar (v: string)
| APlus (a1 a2: Aff)
| AMinus (a1 a2: Aff)
| AMul (c: Z) (a: Aff).

(* Check if a variable is used in an affine function *)

Fixpoint used_in_aff (a: Aff) (v: string) :=
  match a with
  | AConst _ => true
  | AVar v' => (v == v')
  | APlus a1 a2 => used_in_aff a1 v || used_in_aff a2 v
  | AMinus a1 a2 => used_in_aff a1 v || used_in_aff a2 v
  | AMul c a' => used_in_aff a' v
  end.

(* Evaluate an affine function given values for each variable *)

Fixpoint eval_aff (a: Aff) (m: string -> Z) :=
  match a with
  | AConst c => c
  | AVar v => m v
  | APlus a1 a2 => (eval_aff a1 m) + (eval_aff a2 m)
  | AMinus a1 a2 => (eval_aff a1 m) - (eval_aff a2 m)
  | AMul c a => c * (eval_aff a m)
  end.

(* Implementation of a Presburger set / pw_aff library *)

Class PresburgerImpl (PSet PwAff: Type) :=
  {
    eval_set : PSet -> (string -> Z) -> bool;
    eval_set_same : forall m1 m2,
        (forall x, m1 x = m2 x) -> forall s, eval_set s m1 = eval_set s m2;

    empty_set : PSet;
    empty_set_spec : forall x, ~~(eval_set empty_set x);

    universe_set : PSet;
    universe_set_spec : forall x, eval_set universe_set x;

    union_set : PSet -> PSet -> PSet;
    union_set_spec : forall p1 p2 x,
        eval_set (union_set p1 p2) x = eval_set p1 x || eval_set p2 x;

    intersect_set : PSet -> PSet -> PSet;
    intersect_set_spec : forall p1 p2 x,
        eval_set (intersect_set p1 p2) x = eval_set p1 x && eval_set p2 x;

    is_subset : PSet -> PSet -> bool;
    is_subset_spec : forall p1 p2, is_subset p1 p2 <->
                              forall x, eval_set p1 x -> eval_set p2 x;

    set_project_out : PSet -> string -> PSet;
    set_project_out_spec : forall p d (m: total_map _ _), eval_set (set_project_out p d) m <->
                                    exists v, eval_set p (d !-> v; m);


    eval_pw_aff : PwAff -> (string -> Z) -> option Z;

    pw_aff_from_aff : Aff -> PwAff;
    pw_aff_from_aff_spec : forall a x, eval_pw_aff (pw_aff_from_aff a) x = Some (eval_aff a x);

    intersect_domain : PwAff -> PSet -> PwAff;
    intersect_domain_spec : forall p s x, eval_pw_aff (intersect_domain p s) x =
                                     if eval_set s x then
                                       eval_pw_aff p x
                                     else
                                       None;

    union_pw_aff : PwAff -> PwAff -> PwAff;
    union_pw_aff_spec : forall p1 p2 x, eval_pw_aff (union_pw_aff p1 p2) x =
                                   match eval_pw_aff p1 x with
                                   | None => eval_pw_aff p2 x
                                   | r => r
                                   end;

    eq_set : PwAff -> PwAff -> PSet;
    eq_set_spec : forall p1 p2 x, eval_set (eq_set p1 p2) x =
                             match (eval_pw_aff p1 x, eval_pw_aff p2 x) with
                             | (Some v1, Some v2) => v1 == v2
                             | _ => false
                             end;

    ne_set : PwAff -> PwAff -> PSet;
    ne_set_spec : forall p1 p2 x, eval_set (ne_set p1 p2) x =
                             match (eval_pw_aff p1 x, eval_pw_aff p2 x) with
                             | (Some v1, Some v2) => (v1 != v2)
                             | _ => false
                             end;

    le_set : PwAff -> PwAff -> PSet;
    le_set_spec : forall p1 p2 x, eval_set (le_set p1 p2) x =
                             match (eval_pw_aff p1 x, eval_pw_aff p2 x) with
                             | (Some v1, Some v2) => v1 <=? v2
                             | _ => false
                             end;

    indicator_function : PSet -> PwAff;
    indicator_function_spec : forall s x, eval_pw_aff (indicator_function s) x =
                                     if eval_set s x then
                                       Some 1
                                     else
                                       Some 0;
  }.

Generalizable All Variables.

Theorem is_subset_refl `{PI: PresburgerImpl PSet PwAff}:
  forall p, is_subset p p.
Proof.
  move => p.
    by apply is_subset_spec.
Qed.

Theorem is_subset_trans `{PI: PresburgerImpl PSet PwAff}:
  forall p1 p2 p3, is_subset p1 p2 ->
              is_subset p2 p3 ->
              is_subset p1 p3.
Proof.
  move => p1 p2 p3.
  rewrite !is_subset_spec.
    by auto.
Qed.

Theorem is_subset_union_l `{PI: PresburgerImpl PSet PwAff} :
  forall p1 p2, is_subset p1 (union_set p1 p2).
Proof.
  move => p1 p2.
  rewrite is_subset_spec => x Hp1.
    by rewrite union_set_spec Hp1.
Qed.

Theorem is_subset_union_r `{PI: PresburgerImpl PSet PwAff} :
  forall p1 p2, is_subset p2 (union_set p1 p2).
Proof.
  move => p1 p2.
  rewrite is_subset_spec => x Hp2.
    by rewrite union_set_spec Hp2 orbT.
Qed.

(* Tactic to simplify proofs that use presburger sets or pw_aff *)

Ltac simpl_presburger :=
  repeat match goal with
         | [ |- context[eval_set empty_set _]] => rewrite (negbTE (empty_set_spec _))
         | [ |- context[eval_set universe_set _]] => rewrite universe_set_spec
         | [ |- context[eval_set (union_set _ _) _]] => rewrite union_set_spec
         | [ |- context[eval_set (intersect_set _ _) _]] => rewrite intersect_set_spec
         | [ |- context[eval_set (set_project_out _ _) _]] => rewrite set_project_out_spec
         | [ |- context[eval_pw_aff (pw_aff_from_aff _) _]] => rewrite pw_aff_from_aff_spec
         | [ |- context[eval_pw_aff (intersect_domain _ _) _]] => rewrite intersect_domain_spec
         | [ |- context[eval_pw_aff (union_pw_aff _ _) _]] => rewrite union_pw_aff_spec
         | [ |- context[eval_set (eq_set _ _) _]] => rewrite eq_set_spec
         | [ |- context[eval_set (ne_set _ _) _]] => rewrite ne_set_spec
         | [ |- context[eval_set (le_set _ _) _]] => rewrite le_set_spec
         | [ |- context[eval_pw_aff (indicator_function _) _]] => rewrite indicator_function_spec
         | [ |- context[is_subset ?s ?s]] => rewrite is_subset_refl
         | [ |- context[is_subset ?s (union_set ?s _)]] => rewrite is_subset_union_l
         | [ |- context[is_subset ?s (union_set _ ?s)]] => rewrite is_subset_union_r
         | _ => by autorewrite with totalrw
         end.
