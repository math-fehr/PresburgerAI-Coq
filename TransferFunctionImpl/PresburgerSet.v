From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export TransferFunction AbstractDomainImpl.PresburgerSet.
Require Import Coq.Lists.List.
Open Scope string_scope.

(* Transfer function for constant instruction *)
Definition transfer_presburger_set_const {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} (s: PSet) (l: label) (v: string) (c: Z) :=
  let c_set := eq_set (pw_aff_from_aff (AVar v)) (pw_aff_from_aff (AConst c)) in
  let s := set_project_out s v in
  let new_set := intersect_set c_set s in
  (new_set, l+1).

Lemma transfer_presburger_set_const_sound_aux {PSet PwAff: Type} (P: PresburgerImpl PSet PwAff) :
  forall v c R l R' l', (R', l') = ssa_step (Const v c) R l ->
                   forall a, Ensembles.In RegisterMap (gamma a) R ->
                        let (a', l') := (transfer_presburger_set_const a l v c) in
                              Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move=> v c R l R' l' [HR' Hl'] a Hingamma.
  rewrite /Ensembles.In /transfer_presburger_set_const /gamma /= in Hingamma *.
  simpl_eval_presburger.
  rewrite Bool.andb_true_iff HR'.
  split.
  - by simpl_totalmap_Z.
  - simpl_eval_presburger.
    exists (eval_map R v).
    rewrite -Hingamma.
    by simpl_eval_presburger.
Qed.


Theorem transfer_presburger_set_const_sound {PSet PwAff: Type} (P: PresburgerImpl PSet PwAff) :
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
Definition binop_to_pwaff {PSet PwAff: Type } {P: PresburgerImpl PSet PwAff} (v: variable) (opc: BinArithOpCode) (op1 op2: variable) :=
  match opc with
  | OpAdd => pw_aff_from_aff (APlus (AVar op1) (AVar op2))
  | OpMul => pw_aff_from_aff (AVar v)
  | OpLe => indicator_function (le_set (pw_aff_from_aff (AVar op1)) (pw_aff_from_aff (AVar op2)))
  end.

Definition transfer_presburger_set_binop {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} (s: PSet) (l: label) (v: variable) (opc: BinArithOpCode) (op1 op2: variable) :=
  let pwaff := binop_to_pwaff v opc op1 op2 in
  let c_set := eq_set (pw_aff_from_aff (AVar v)) pwaff in
  let s := set_project_out s v in
  let new_set := intersect_set c_set s in
  (new_set, l+1).


Lemma transfer_presburger_set_binop_sound_aux {PSet PwAff: Type} (P: PresburgerImpl PSet PwAff) :
  forall v opc op1 op2 Hop1 Hop2 R l R' l',
    (R', l') = ssa_step (BinOp v opc op1 op2 Hop1 Hop2) R l ->
    forall a, Ensembles.In RegisterMap (gamma a) R ->
         let (a', l') := (transfer_presburger_set_binop a l v opc op1 op2) in
         Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move=> v opc op1 op2 /eqb_neq Hop1 /eqb_neq Hop2 R l R' l' [HR' Hl'] a Hingamma.
  rewrite /Ensembles.In /transfer_presburger_set_const /gamma /= in Hingamma *.
  simpl_eval_presburger.
  rewrite Bool.andb_true_iff HR'.
  split.
  - simpl_totalmap_Z.
    case opc.
    + simpl_eval_presburger.
      by rewrite Hop1 Hop2 Z.eqb_refl.
    + by simpl_eval_presburger.
    + simpl_eval_presburger.
      rewrite Hop1 Hop2.
      by case (eval_map R op1 <=? eval_map R op2)%Z.
  - simpl_eval_presburger.
    exists (eval_map R v).
    rewrite -Hingamma.
    by simpl_eval_presburger.
Qed.

Theorem transfer_presburger_set_binop_sound {PSet PwAff: Type} (P: PresburgerImpl PSet PwAff) :
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
Fixpoint presburger_affect_variables {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} (s: PSet) (params: list (variable * variable)) :=
  match params with
  | nil => s
  | (param, value)::params' =>
    if string_dec param value then
      presburger_affect_variables s params'
    else
      let c_set := eq_set (pw_aff_from_aff (AVar param)) (pw_aff_from_aff (AVar value)) in
      let s := set_project_out s param in
      let new_s := intersect_set c_set s in
      presburger_affect_variables new_s params'
  end.

Definition transfer_presburger_set_branch {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} (s: PSet) (l: label) (params: list (variable * variable)) :=
  (presburger_affect_variables s params, l).

Lemma presburger_affect_variables_sound {PSet PwAff: Type} (P: PresburgerImpl PSet PwAff) :
  forall R s,
    Ensembles.In RegisterMap (gamma s) R ->
    forall params, Ensembles.In RegisterMap (gamma (presburger_affect_variables s params)) (affect_variables R params).
Proof.
  move => R s HR params.
  elim: params R s HR.
  - by [].
  - move => [param value] l Hind R s HR /=.
    case (string_dec param value) => [Heq /= | /eqb_neq Hne /=].
    + rewrite Heq.
      apply Hind.
      rewrite /Ensembles.In /gamma /=.
      by simpl_eval_presburger.
    + apply Hind.
      rewrite /= /Ensembles.In.
      simpl_eval_presburger.
      rewrite Bool.andb_true_iff.
      split.
      * rewrite Hne.
        by simpl_totalmap_Z.
      * simpl_eval_presburger.
        exists (eval_map R param).
        by simpl_eval_presburger.
Qed.

Lemma transfer_presburger_set_branch_sound_aux {PSet PwAff: Type} (P: PresburgerImpl PSet PwAff) :
  forall l_ params R l R' l',
    (R', l') = ssa_step (Br l_ params) R l ->
    forall a, Ensembles.In RegisterMap (gamma a) R ->
         let (a', l') := (transfer_presburger_set_branch a l_ params) in
         Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => l_ params R l R' l' Hstep a HR /=.
  inversion Hstep. subst.
  by apply presburger_affect_variables_sound, HR.
Qed.

Theorem transfer_presburger_set_branch_sound {PSet PwAff: Type} (P: PresburgerImpl PSet PwAff) :
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
Definition transfer_presburger_set_branch_cond {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} (s: PSet) (c: variable) (l1 : label) (params1: list (variable * variable)) (l2: label) (params2: list (variable * variable)) :=
  let set_true := ne_set (pw_aff_from_aff (AVar c)) (pw_aff_from_aff (AConst 0))in
  let set_true' := intersect_set set_true s in
  let new_set_true := presburger_affect_variables set_true' params1 in
  let set_false := eq_set (pw_aff_from_aff (AVar c)) (pw_aff_from_aff (AConst 0)) in
  let set_false' := intersect_set set_false s in
  let new_set_false := presburger_affect_variables set_false' params2 in
  (new_set_true, l1)::(new_set_false, l2)::nil.


Theorem transfer_presburger_set_branch_cond_sound {PSet PwAff: Type} (P: PresburgerImpl PSet PwAff) :
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
  case (eval_map R c =? 0)%Z eqn:HRC in H7.
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
      by rewrite -HRC /Ensembles.In.
  - eexists. simpl. split.
    + left. move: H7 => [HR' Hl'].
      rewrite Hl' //.
    + move: H7 => [HR' Hl'].
      rewrite Z.eqb_neq in HRC * => HRC.
      rewrite HR' /= /Ensembles.In (constraint_neq_one_variable_correct R c 0) in HIn * => [ | //].
      rewrite presburger_affect_variables_sound => [ | //].
      rewrite /Ensembles.In /gamma /= !intersect_set_spec !Bool.andb_true_iff in HIn *.
      move => [HIn1 HIn2].
      by [].
Qed.


(* The final transfer function *)
Definition transfer_presburger_set {PSet PwAff: Type} {P: PresburgerImpl PSet PwAff} (inst: Instruction) (s: PSet) (l: label) :=
  match inst with
  | Const v c => (transfer_presburger_set_const s l v c)::nil
  | BinOp v opc op1 op2 op1_ne_v op2_ne_v => (transfer_presburger_set_binop s l v opc op1 op2)::nil
  | Br l' params => (transfer_presburger_set_branch s l' params)::nil
  | BrC c l1 params1 l2 params2 => transfer_presburger_set_branch_cond s c l1 params1 l2 params2
  end.

Theorem transfer_presburger_set_sound {PSet PwAff: Type} (P: PresburgerImpl PSet PwAff) :
  forall prog R l R' l',
    step prog (R, l) (R', l') ->
    forall inst, Some inst = List.nth_error prog l ->
            forall a, Ensembles.In (total_map Z) (gamma a) R ->
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
