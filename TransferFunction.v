From Coq Require Import ssreflect ssrfun ssrbool.
Require Export PolyAI.Presburger.
Require Export PolyAI.AbstractDomain.
Require Import PolyAI.SSA.
Require Import Coq.Lists.List.
Require Import String.
Open Scope string_scope.

(* Transfer functions for our language *)
Class transfer_function {ab: Type} (A: adom ab) :=
  {
    transfer : SSA -> ab -> label -> list (ab * label);
    transfer_sound :
      forall prog R l R' l',
        step prog (R, l) (R', l') ->
        forall inst, Some inst = List.nth_error prog l ->
                forall a, Ensembles.In RegisterMap (gamma a) R ->
                     exists a', In (a', l') (transfer inst a l) /\
                           Ensembles.In RegisterMap (gamma a') R'
  }.

(* We define in the rest of the file the transfer functions for the presburger abstract domain *)


(* Transfer function for constant instruction *)
Definition transfer_presburger_set_const {S: Type} {P: PresburgerSet S} (s: S) (l: label) (v: string) (c: Z) :=
  let constraint := CEq (AVar v) (AConst c) in
  let s := set_project_out s v in
  let c_set := set_from_constraint constraint in
  let new_set := intersect_set c_set s in
  (new_set, l+1).

Lemma transfer_presburger_set_const_sound_aux {S: Type} (P: PresburgerSet S) :
  forall v c R l R' l', (R', l') = ssa_step (Const v c) R l ->
                   forall a, Ensembles.In RegisterMap (@gamma S (PresburgerSetAD P) a) R ->
                        let (a', l') := (transfer_presburger_set_const a l v c) in
                              Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move=> v c R l R' l' [HR' Hl'] a Hingamma.
  rewrite /Ensembles.In /transfer_presburger_set_const /gamma /= in Hingamma *.
  rewrite intersect_set_spec Bool.andb_true_iff.
  split.
    - by rewrite set_from_constraint_spec /= HR' t_update_eq Z.eqb_refl //.
    - rewrite set_project_out_spec.
      exists (R v).
      rewrite HR' t_update_shadow t_update_same.
        by exact Hingamma.
Qed.

Theorem transfer_presburger_set_const_sound {S: Type} (P: PresburgerSet S) :
  forall v c prog R l R' l',
    step prog (R, l) (R', l') ->
    Some (Const v c) = List.nth_error prog l ->
    forall a, Ensembles.In RegisterMap (gamma a) R ->
         exists a', In (a', l') ((transfer_presburger_set_const a l v c)::nil) /\
               Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => v c prog R l R' l' Hstep Hinst a HIn.
  exists (fst (transfer_presburger_set_const a l v c)).
  inversion Hstep. subst.
  rewrite -Hinst in H6.
  case: H6 => H6.
  rewrite H6 /= in H7.
  split.
  - left.
    move: H7 => [HR' Hl'].
    rewrite Hl'.
    by reflexivity.
  - move: (transfer_presburger_set_const_sound_aux P v c R l R' l' H7 a HIn) => Hgoal.
    by apply Hgoal.
Qed.

(* Transfer function for binary arithmetic operation *)
Definition binop_to_pwaff (v: variable) (opc: BinArithOpCode) (op1 op2: variable) :=
  match opc with
  | OpAdd => APlus (AVar op1) (AVar op2)
  | OpMul => AVar v
  | OpLe => ALe (AVar op1) (AVar op2)
  end.

Definition transfer_presburger_set_binop {S: Type} {P: PresburgerSet S} (s: S) (l: label) (v: variable) (opc: BinArithOpCode) (op1 op2: variable) :=
  let pwaff := binop_to_pwaff v opc op1 op2 in
  let constraint := CEq (AVar v) pwaff in
  let s := set_project_out s v in
  let c_set := set_from_constraint constraint in
  let new_set := intersect_set c_set s in
  (new_set, l+1).


Lemma transfer_presburger_set_binop_sound_aux {S: Type} (P: PresburgerSet S) :
  forall v opc op1 op2 Hop1 Hop2 R l R' l',
    (R', l') = ssa_step (BinOp v opc op1 op2 Hop1 Hop2) R l ->
    forall a, Ensembles.In RegisterMap (@gamma S (PresburgerSetAD P) a) R ->
         let (a', l') := (transfer_presburger_set_binop a l v opc op1 op2) in
         Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move=> v opc op1 op2 Hop1 Hop2 R l R' l' [HR' Hl'] a Hingamma.
  rewrite /Ensembles.In /transfer_presburger_set_const /gamma /= in Hingamma *.
  rewrite intersect_set_spec Bool.andb_true_iff.
  split.
  - rewrite set_from_constraint_spec /= HR' t_update_eq.
    case opc;
      try ((repeat (rewrite /= t_update_neq => [// |]);
            rewrite Z.eqb_refl //)).
    + rewrite /= t_update_eq Z.eqb_refl //.
  - rewrite set_project_out_spec.
    exists (R v).
    rewrite HR' t_update_shadow t_update_same.
      by exact Hingamma.
Qed.

Theorem transfer_presburger_set_binop_sound {S: Type} (P: PresburgerSet S) :
  forall v opc op1 op2 Hop1 Hop2 prog R l R' l',
    step prog (R, l) (R', l') ->
    Some (BinOp v opc op1 op2 Hop1 Hop2) = List.nth_error prog l ->
    forall a, Ensembles.In RegisterMap (gamma a) R ->
         exists a', In (a', l') ((transfer_presburger_set_binop a l v opc op1 op2)::nil) /\
               Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => v opc op1 op2 Hop1 Hop2 prog R l R' l' Hstep Hinst a HIn.
  exists (fst (transfer_presburger_set_binop a l v opc op1 op2)).
  inversion Hstep. subst.
  rewrite -Hinst in H6.
  case: H6 => H6.
  rewrite H6 /= in H7.
  split.
  - left.
    move: H7 => [HR' Hl'].
    rewrite Hl'.
    by reflexivity.
  - move: (transfer_presburger_set_binop_sound_aux P v opc op1 op2 Hop1 Hop2 R l R' l' H7 a HIn) => Hgoal.
    by apply Hgoal.
Qed.

(* Transfer function for unconditional branch instruction *)
Fixpoint presburger_affect_variables {S: Type} {P: PresburgerSet S} (s: S) (params: list (variable * variable)) :=
  match params with
  | nil => s
  | (param, value)::params' =>
    if string_dec param value then
      presburger_affect_variables s params'
    else
      let constraint := CEq (AVar param) (AVar value) in
      let s := set_project_out s param in
      let c_set := set_from_constraint constraint in
      let new_s := intersect_set c_set s in
      presburger_affect_variables new_s params'
  end.

Definition transfer_presburger_set_branch {S: Type} {P: PresburgerSet S} (s: S) (l: label) (params: list (variable * variable)) :=
  (presburger_affect_variables s params, l).

Lemma presburger_affect_variables_sound {S: Type} (P: PresburgerSet S) :
  forall R s,
    Ensembles.In RegisterMap (@gamma S (PresburgerSetAD P) s) R ->
    forall params, Ensembles.In RegisterMap (gamma (presburger_affect_variables s params)) (affect_variables R params).
Proof.
  move => R s HR params.
  elim: params R s HR.
  - by [].
  - move => [param value] l Hind R s HR /=.
    case (string_dec param value) => [Heq /= | Hne /=].
    + rewrite Heq t_update_same.
      by apply Hind, HR.
    + apply Hind.
      rewrite /= /Ensembles.In intersect_set_spec Bool.andb_true_iff.
      split.
      * rewrite set_from_constraint_spec /= t_update_eq t_update_neq
        => [/Hne // |].
          by rewrite Z.eqb_refl //.
      * rewrite set_project_out_spec.
        exists (R param).
        by rewrite t_update_shadow t_update_same //.
Qed.

Lemma transfer_presburger_set_branch_sound_aux {S: Type} (P: PresburgerSet S) :
  forall l_ params R l R' l',
    (R', l') = ssa_step (Br l_ params) R l ->
    forall a, Ensembles.In RegisterMap (@gamma S (PresburgerSetAD P) a) R ->
         let (a', l') := (transfer_presburger_set_branch a l_ params) in
         Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => l_ params R l R' l' Hstep a HR /=.
  inversion Hstep. subst.
  by apply presburger_affect_variables_sound, HR.
Qed.

Theorem transfer_presburger_set_branch_sound {S: Type} (P: PresburgerSet S) :
  forall l_ params prog R l R' l',
    step prog (R, l) (R', l') ->
    Some (Br l_ params) = List.nth_error prog l ->
    forall a, Ensembles.In RegisterMap (gamma a) R ->
         exists a', In (a', l') ((transfer_presburger_set_branch a l_ params)::nil) /\
               Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => l_ params prog R l R' l' Hstep Hinst a HIn.
  exists (fst (transfer_presburger_set_branch a l_ params)).
  inversion Hstep. subst.
  rewrite -Hinst in H6.
  case: H6 => H6.
  rewrite H6 /= in H7.
  split.
  - left.
    move: H7 => [HR' Hl'].
    rewrite Hl'.
    by reflexivity.
  - move: (transfer_presburger_set_branch_sound_aux P l_ params R l R' l' H7 a HIn) => Hgoal.
    by apply Hgoal.
Qed.

(* Transfer function for conditional branch instruction *)
Definition transfer_presburger_set_branch_cond {S: Type} {P: PresburgerSet S} (s: S) (c: variable) (l1 : label) (params1: list (variable * variable)) (l2: label) (params2: list (variable * variable)) :=
  let constraint_true := CNeq (AVar c) (AConst 0) in
  let set_true := set_from_constraint constraint_true in
  let set_true' := intersect_set s set_true in
  let new_set_true := presburger_affect_variables set_true' params1 in
  let constraint_false := CEq (AVar c) (AConst 0) in
  let set_false := set_from_constraint constraint_false in
  let set_false' := intersect_set s set_false in
  let new_set_false := presburger_affect_variables set_false' params2 in
  (new_set_true, l1)::(new_set_false, l2)::nil.


Theorem transfer_presburger_set_branch_cond_sound {S: Type} (P: PresburgerSet S) :
  forall c l1 params1 l2 params2 prog R l R' l',
    step prog (R, l) (R', l') ->
    Some (BrC c l1 params1 l2 params2) = List.nth_error prog l ->
    forall a, Ensembles.In RegisterMap (gamma a) R ->
         exists a', In (a', l') (transfer_presburger_set_branch_cond a c l1 params1 l2 params2) /\
               Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => c l1 params1 l2 params2 prog R l R' l' Hstep Hinst a HIn.
  inversion Hstep. subst.
  rewrite -Hinst in H6.
  move: H6 => [H6].
  rewrite H6 /= in H7.
  case (R c =? 0)%Z eqn:HRC in H7.
  - eexists. simpl. split.
    + right. left. move: H7 => [HR' Hl'].
      by rewrite Hl' //.
    + move: H7 => [HR' Hl'].
      rewrite HR' /= /Ensembles.In (constraint_eq_one_variable_correct R a c) in HIn *.
      rewrite presburger_affect_variables_sound => [ | //].
      rewrite /Ensembles.In /gamma /= !intersect_set_spec !Bool.andb_true_iff in HIn *.
      move => [HIn1 HIn2].
      split => [// | ].
      rewrite Z.eqb_eq in HRC * => HRC.
      by rewrite -HRC //.
  - eexists. simpl. split.
    + left. move: H7 => [HR' Hl'].
      rewrite Hl' //.
    + move: H7 => [HR' Hl'].
      rewrite Z.eqb_neq in HRC * => HRC.
      rewrite HR' /= /Ensembles.In (constraint_neq_one_variable_correct R c 0) in HIn * => [// | ].
      rewrite presburger_affect_variables_sound => [ | //].
      rewrite /Ensembles.In /gamma /= !intersect_set_spec !Bool.andb_true_iff in HIn *.
      move => [HIn1 HIn2].
      by [].
Qed.


(* The final transfer function *)
Definition transfer_presburger_set {S: Type} {P: PresburgerSet S} (inst: SSA) (s: S) (l: label) :=
  match inst with
  | Const v c => (transfer_presburger_set_const s l v c)::nil
  | BinOp v opc op1 op2 op1_ne_v op2_ne_v => (transfer_presburger_set_binop s l v opc op1 op2)::nil
  | Br l' params => (transfer_presburger_set_branch s l' params)::nil
  | BrC c l1 params1 l2 params2 => transfer_presburger_set_branch_cond s c l1 params1 l2 params2
  end.

Theorem transfer_presburger_set_sound {S: Type} (P: PresburgerSet S) :
  forall prog R l R' l',
    step prog (R, l) (R', l') ->
    forall inst, Some inst = List.nth_error prog l ->
            forall a, Ensembles.In (total_map Z) (@gamma S (PresburgerSetAD P) a) R ->
                 exists a', In (a', l') (transfer_presburger_set inst a l) /\
                       Ensembles.In (total_map Z) (gamma a') R'.
Proof.
  move => prog R l R' l' Hstep inst.
  move: prog R l R' l' Hstep.
  case inst.
  - by apply transfer_presburger_set_const_sound.
  - by apply transfer_presburger_set_binop_sound.
  - by apply transfer_presburger_set_branch_sound.
  - by apply transfer_presburger_set_branch_cond_sound.
Qed.
