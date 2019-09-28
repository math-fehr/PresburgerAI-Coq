From Coq Require Import ssreflect ssrfun ssrbool.
Require Export PolyAI.TotalMap.
Require Export Coq.Sets.Ensembles.
Require Export Coq.ZArith.BinInt.

Require Import String.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Inductive Aff :=
| AConst (c: Z)
| AVar (v: string)
| APlus (a1 a2: Aff)
| AMinus (a1 a2: Aff)
| AMul (c: Z) (a: Aff).

Definition indicator (b: bool) :=
  match b with
  | true => 1
  | false => 0
  end.

Fixpoint eval_aff (a: Aff) (m: total_map Z) :=
  match a with
  | AConst c => c
  | AVar v => m v
  | APlus a1 a2 => (eval_aff a1 m) + (eval_aff a2 m)
  | AMinus a1 a2 => (eval_aff a1 m) - (eval_aff a2 m)
  | AMul c a => c * (eval_aff a m)
  end.

Class PresburgerImpl (PSet PwAff: Type) :=
  {
    eval_set : PSet -> total_map Z -> bool;

    empty_set : PSet;
    empty_set_spec : forall x, eval_set empty_set x = false;

    universe_set : PSet;
    universe_set_spec : forall x, eval_set universe_set x = true;

    union_set : PSet -> PSet -> PSet;
    union_set_spec : forall p1 p2 x,
        eval_set (union_set p1 p2) x = eval_set p1 x || eval_set p2 x;

    intersect_set : PSet -> PSet -> PSet;
    intersect_set_spec : forall p1 p2 x,
        eval_set (intersect_set p1 p2) x = eval_set p1 x && eval_set p2 x;

    is_subset : PSet -> PSet -> bool;
    is_subset_spec : forall p1 p2, is_subset p1 p2 = true <->
                              forall x, eval_set p1 x = true -> eval_set p2 x = true;

    set_project_out : PSet -> string -> PSet;
    set_project_out_spec : forall p d x, eval_set (set_project_out p d) x = true <->
                                    exists v, eval_set p (d !-> v; x) = true;


    eval_pw_aff : PwAff -> total_map Z -> option Z;

    pw_aff_from_aff : Aff -> PwAff;
    pw_aff_from_aff_spec : forall a x, eval_pw_aff (pw_aff_from_aff a) x = Some (eval_aff a x);

    intersect_domain : PwAff -> PSet -> PwAff;
    intersect_domain_spec_in : forall p s x, eval_set s x = true -> eval_pw_aff (intersect_domain p s) x = eval_pw_aff p x;
    intersect_domain_spec_out : forall p s x, eval_set s x = false -> eval_pw_aff (intersect_domain p s) x = None;

    union_pw_aff : PwAff -> PwAff -> PwAff;
    union_pw_aff_spec : forall p1 p2 x, eval_pw_aff (union_pw_aff p1 p2) x = match eval_pw_aff p1 x with
                                                                        | None => eval_pw_aff p2 x
                                                                        | r => r
                                                                        end;

    eq_set : PwAff -> PwAff -> PSet;
    eq_set_spec : forall p1 p2 x, eval_set (eq_set p1 p2) x = match (eval_pw_aff p1 x, eval_pw_aff p2 x) with
                                                         | (Some v1, Some v2) => v1 =? v2
                                                         | _ => false
                                                         end;

    ne_set : PwAff -> PwAff -> PSet;
    ne_set_spec : forall p1 p2 x, eval_set (ne_set p1 p2) x = match (eval_pw_aff p1 x, eval_pw_aff p2 x) with
                                                         | (Some v1, Some v2) => negb (v1 =? v2)
                                                         | _ => false
                                                         end;

    le_set : PwAff -> PwAff -> PSet;
    le_set_spec : forall p1 p2 x, eval_set (le_set p1 p2) x = match (eval_pw_aff p1 x, eval_pw_aff p2 x) with
                                                         | (Some v1, Some v2) => v1 <=? v2
                                                         | _ => false
                                                         end;

    indicator_function : PSet -> PwAff;
    indicator_function_spec : forall s x, eval_pw_aff (indicator_function s) x = if eval_set s x then
                                                                             Some 1
                                                                         else
                                                                           Some 0;
  }.


Theorem is_subset_refl {PSet PwAff : Type} {P : PresburgerImpl PSet PwAff} :
  forall p, is_subset p p = true.
Proof.
  move => p.
  apply is_subset_spec => //.
Qed.

Theorem is_subset_trans {PSet PwAff: Type} {P : PresburgerImpl PSet PwAff} :
  forall p1 p2 p3, is_subset p1 p2 = true ->
              is_subset p2 p3 = true ->
              is_subset p1 p3 = true.
Proof.
  move => p1 p2 p3 /is_subset_spec H12 /is_subset_spec H23.
  apply is_subset_spec.
  by auto.
Qed.

Theorem is_subset_union_l {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} :
  forall p1 p2, is_subset p1 (union_set p1 p2).
Proof.
  move => p1 p2.
  apply is_subset_spec => x Hp1.
  rewrite union_set_spec Hp1.
  reflexivity.
Qed.

Theorem is_subset_union_r {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} :
  forall p1 p2, is_subset p2 (union_set p1 p2).
Proof.
  move => p1 p2.
  apply is_subset_spec => x Hp2.
  rewrite union_set_spec Hp2.
  by apply orbT.
Qed.

Theorem constraint_eq_one_variable_correct {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} :
  forall m p x, eval_set p m = eval_set (intersect_set (eq_set (pw_aff_from_aff (AVar x)) (pw_aff_from_aff (AConst (m x)))) p) m.
Proof.
  move => m p x.
  by rewrite intersect_set_spec eq_set_spec !pw_aff_from_aff_spec /= Z.eqb_refl.
Qed.

Theorem constraint_neq_one_variable_correct {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} :
  forall m x v, m x <> v ->
           forall p, eval_set p m = eval_set (intersect_set (ne_set (pw_aff_from_aff (AVar x)) (pw_aff_from_aff (AConst v))) p) m.
Proof.
  move => m x v /Z.eqb_neq Hne p.
  by rewrite intersect_set_spec ne_set_spec !pw_aff_from_aff_spec Hne.
Qed.
