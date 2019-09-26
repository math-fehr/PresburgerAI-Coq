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


(* The final transfer function *)
Definition transfer_presburger_set {S: Type} {P: PresburgerSet S} (inst: SSA) (s: S) (l: label) :=
  match inst with
  | Const v c => (transfer_presburger_set_const s l v c)::nil
  | BinOp v opc op1 op2 op1_ne_v op2_ne_v => (transfer_presburger_set_binop s l v opc op1 op2)::nil
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
Qed.
