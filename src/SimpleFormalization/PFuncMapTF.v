From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export PFunc TotalMap PFuncMapAD.
From PolyAI.SimpleFormalization Require Export SSA.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Export Coq.Sets.Ensembles.

Definition constant_or_set_to_top_pfunc {PFunc: Type} {PI: PFuncImpl PFunc} (p: PFunc) (s: string) :=
  if is_constant_on_var p s then
    p
  else
    constant_pfunc VTop.

Theorem constant_or_set_to_top_pfunc_is_constant {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall p s, is_constant_on_var (constant_or_set_to_top_pfunc p s) s.
Proof.
  move => p s.
  rewrite /constant_or_set_to_top_pfunc.
  case (is_constant_on_var p s) eqn:H => [// | ].
  apply is_constant_on_var_spec => m m' H1.
    by simpl_pfunc.
Qed.

Definition pfunc_map_assign_pfunc {PFunc: Type} {PI: PFuncImpl PFunc} (a: total_map) (v: string) (p: PFunc) :=
  let projected_a := pointwise_un_op a (fun a' => constant_or_set_to_top_pfunc a' v) in
  let new_a := (v !-> p ; projected_a) in
  new_a.

Theorem pfunc_map_assign_pfunc_spec {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a R, Ensembles.In RegisterMap (gamma a) R ->
         forall p z v, in_V z (eval_pfunc p (pointwise_un_op (v !-> z; R) VVal))
                -> Ensembles.In RegisterMap (gamma (pfunc_map_assign_pfunc a v p)) (v !-> z; R).
Proof.
  move => a R HInR p z v HinR' /=.
  rewrite /In /gamma_pfunc_map /pfunc_map_assign_pfunc => v'.
  case (eqb_spec v v') => [<- | /eqP Hne ]. by simpl_totalmap.
  simpl_totalmap.
  rewrite /constant_or_set_to_top_pfunc.
  case (is_constant_on_var (eval_map a v') v) eqn:Hconstant; last first.
    by simpl_pfunc.
  have Hconstant': (is_true (is_constant_on_var (a v') v)).
    by [].
    simpl_pfunc.
  apply HInR.
Qed.


Definition pfunc_assign_const {PFunc: Type} {PI: PFuncImpl PFunc} (a: total_map) (v: string) (c: Z) :=
  pfunc_map_assign_pfunc a v (constant_pfunc (VVal c)).

Theorem pfunc_assign_const_spec {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a R, In RegisterMap (gamma a) R ->
         forall v c, In RegisterMap (gamma (pfunc_assign_const a v c)) (v !-> c; R).
Proof.
  move => a R HIn v c.
  apply pfunc_map_assign_pfunc_spec => [// | ].
    by simpl_pfunc.
Qed.

Theorem transfer_pfunc_map_const_sound {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall v c prog R l R' l',
    step prog (R, l) (R', l') ->
    Some (Const v c) = List.nth_error prog l ->
    forall a, Ensembles.In RegisterMap (gamma a) R ->
         exists a', List.In (a', l') ((pfunc_assign_const a v c, l+1)::nil) /\
               Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => v c prog R l R' l' Hstep Hinst a HIn.
  exists (pfunc_assign_const a v c).
  inversion Hstep. subst.
  rewrite -Hinst in H6.
  inversion H6. subst.
  move: H7 => /= [-> ->].
  split => [// | ].
  - auto.
  - by apply pfunc_assign_const_spec.
Qed.

Definition binop_pfunc_map {PFunc: Type} {PI: PFuncImpl PFunc} (res: string) (op1 op2: PFunc) (bin_op: BinArithOpCode) :=
  match bin_op with
  | OpAdd => add_pfunc op1 op2
  | OpMul => constant_pfunc VTop
  | OpLe => le_binop_pfunc op1 op2
  end.

Theorem binop_pfunc_map_spec {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall res op1, is_constant_on_var op1 res ->
             forall op2, is_constant_on_var op2 res ->
                    forall (R: total_map) x1, in_V x1 (eval_pfunc op1 R) ->
                                         forall x2, in_V x2 (eval_pfunc op2 R) ->
                                               forall opc, in_V (bin_op_eval opc x1 x2)
                                                           (eval_pfunc
                                                              (binop_pfunc_map res op1 op2 opc)
                                                              (res !-> VVal (bin_op_eval opc x1 x2); R)).
Proof.
  move => res op1 Hconst1 op2 Hconst2 R x1 Hin1 x2 Hin2 [ | | ]; by simpl_pfunc.
Qed.

Definition pfunc_assign_arith {PFunc: Type} {PI: PFuncImpl PFunc} (a: total_map) (opr op1 op2: string) (opc: BinArithOpCode):=
  let op1_ := constant_or_set_to_top_pfunc (eval_map a op1) opr in
  let op2_ := constant_or_set_to_top_pfunc (eval_map a op2) opr in
  pfunc_map_assign_pfunc a opr (binop_pfunc_map opr op1_ op2_ opc).

Theorem pfunc_assign_arith_spec {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a R, In RegisterMap (gamma a) R ->
         forall opr op1 op2 opc, In RegisterMap (gamma (pfunc_assign_arith a opr op1 op2 opc))
                               (opr !-> bin_op_eval opc (R op1) (R op2); R).
Proof.
  move => a R HInR opr op1 op2 opc.
  apply pfunc_map_assign_pfunc_spec => [// | ].
  rewrite [pointwise_un_op _ _]/=.
  apply binop_pfunc_map_spec.
  - by apply constant_or_set_to_top_pfunc_is_constant.
  - by apply constant_or_set_to_top_pfunc_is_constant.
  - rewrite /constant_or_set_to_top_pfunc.
    case (is_constant_on_var (eval_map a op1) opr) => [// | ].
      by simpl_pfunc.
  - rewrite /constant_or_set_to_top_pfunc.
    case (is_constant_on_var (eval_map a op2) opr) => [// | ].
      by simpl_pfunc.
Qed.

Theorem transfer_pfunc_map_arith_sound {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall v opc op1 op2 Hop1 Hop2 prog R l R' l',
    step prog (R, l) (R', l') ->
    Some (BinOp v opc op1 op2 Hop1 Hop2) = List.nth_error prog l ->
    forall a, Ensembles.In RegisterMap (gamma a) R ->
         exists a', List.In (a', l') ((pfunc_assign_arith a v op1 op2 opc, l+1)::nil) /\
               Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => v opc op1 op2 Hop1 Hop2 prog R l R' l' Hstep Hinst a HIn.
  exists (pfunc_assign_arith a v op1 op2 opc).
  inversion Hstep. subst.
  rewrite -Hinst in H6.
  inversion H6. subst.
  move: H7 => /= [-> ->].
  split => [// | ].
  - auto.
  - by apply pfunc_assign_arith_spec.
Qed.

Fixpoint pfunc_map_affect_variables {PFunc: Type} {PI: PFuncImpl PFunc} (a: total_map) (params: list (variable * variable)) :=
  match params with
  | nil => a
  | (param, value)::params' =>
    if string_dec param value then
      pfunc_map_affect_variables a params'
    else
      let p_value := constant_or_set_to_top_pfunc (eval_map a value) param in
      let new_a := pfunc_map_assign_pfunc a param p_value in
      pfunc_map_affect_variables new_a params'
  end.

Lemma pfunc_map_affect_variables_sound {PFunc: Type} (P: PFuncImpl PFunc) :
  forall R a,
    Ensembles.In RegisterMap (gamma a) R ->
    forall params, Ensembles.In RegisterMap (gamma (pfunc_map_affect_variables a params)) (affect_variables R params).
Proof.
  move => R a HR params.
  elim: params R a HR. by [].
  move => [param value] l Hind R a HR /=.
  case (string_dec param value) => [Heq /= | /eqb_neq Hne /=].
  - rewrite Heq.
    apply Hind => s0.
    simpl_pfunc.
    rewrite -[VVal (R value)](pointwise_un_op_spec).
    by simpl_pfunc.
  - apply Hind => s.
    rewrite pfunc_map_assign_pfunc_spec => [// | // | ].
    rewrite /constant_or_set_to_top_pfunc.
    case (is_constant_on_var (a value) param) eqn:HConst; last first. by simpl_pfunc.
    have: (is_constant_on_var (a value) param) by [] => HConstCoerc.
    by simpl_pfunc.
Qed.

Definition transfer_pfunc_map_branch {PFunc: Type} {P: PFuncImpl PFunc} (a: total_map) (l: label) (params: list (variable * variable)) :=
  (pfunc_map_affect_variables a params, l).

Lemma transfer_pfunc_map_branch_sound {PFunc: Type} (P: PFuncImpl PFunc) :
    forall l_ params prog R l R' l',
      step prog (R, l) (R', l') ->
      Some (Br l_ params) = List.nth_error prog l ->
      forall a, Ensembles.In RegisterMap (gamma a) R ->
           exists a', List.In (a', l') ((transfer_pfunc_map_branch a l_ params)::nil) /\
                 Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => l_ params prog R l R' l' Hstep Hinst a HIn.
  exists (fst (transfer_pfunc_map_branch a l_ params)).
  inversion Hstep. subst.
  rewrite -Hinst in H6.
  case: H6 => -> /= in H7.
  move: H7 => [-> ->].
  split.
  - by left.
  - by apply pfunc_map_affect_variables_sound.
Qed.

(* Transfer function for conditional branch instruction *)
Definition transfer_pfunc_map_branch_cond {PFunc: Type} {P: PFuncImpl PFunc} (a: total_map) (c: variable) (l1 : label) (params1: list (variable * variable)) (l2: label) (params2: list (variable * variable)) :=
  let pfunc_true_ := constant_or_set_to_top_pfunc (eval_map a c) c in
  let pfunc_true := pfunc_restrict_ne_set pfunc_true_ 0 in
  let new_true_ := pfunc_map_assign_pfunc a c pfunc_true in
  let new_true := pfunc_map_affect_variables new_true_ params1 in
  let pfunc_false_ := constant_or_set_to_top_pfunc (eval_map a c) c in
  let pfunc_false := pfunc_restrict_eq_set pfunc_false_ 0 in
  let new_false_ := pfunc_map_assign_pfunc a c pfunc_false in
  let new_false := pfunc_map_affect_variables new_false_ params2 in
  (new_true, l1)::(new_false, l2)::nil.

Theorem transfer_pfunc_map_branch_cond_sound {PFunc: Type} (P: PFuncImpl PFunc) :
  forall c l1 params1 l2 params2 prog R l R' l',
    step prog (R, l) (R', l') ->
    Some (BrC c l1 params1 l2 params2) = List.nth_error prog l ->
    forall a, Ensembles.In RegisterMap (gamma a) R ->
         exists a', List.In (a', l') (transfer_pfunc_map_branch_cond a c l1 params1 l2 params2) /\
               Ensembles.In RegisterMap (gamma a') R'.
Proof.
  move => c l1 params1 l2 params2 prog R l R' l' Hstep Hinst a Hin.
  inversion Hstep. subst.
  rewrite -Hinst in H6.
  case: H6 => -> /= in H7.
  case (eval_map R c == 0)%Z eqn:HRC in H7.
  - eexists. split. by right; left; move: H7 => [HR' -> //].
    apply Z.eqb_eq in HRC.
    move: H7 => [-> _] s0.
    rewrite pfunc_map_affect_variables_sound => [// | s1].
    rewrite /pfunc_map_assign_pfunc.
    case (eqb_spec c s1) => [ <- | Hne ].
    + rewrite /constant_or_set_to_top_pfunc.
      simpl_pfunc.
      case (is_constant_on_var (eval_map a c) c); last first;
        rewrite !HRC. by simpl_pfunc.
      move: Hin => /(_ c).
      move: HRC => -> Hin.
        by rewrite Hin.
    + simpl_totalmap.
      rewrite /constant_or_set_to_top_pfunc.
      case (is_constant_on_var (eval_map a s1) c) eqn:Hconst; last first. by simpl_pfunc.
        by apply Hin.
  - eexists. split. by left; move: H7 => [-> -> //].
    move: H7 => [-> _] s0.
    rewrite pfunc_map_affect_variables_sound => [// | s1].
    case (eqb_spec c s1) => [ <- | Hne ].
    + rewrite /constant_or_set_to_top_pfunc.
      rewrite /pfunc_map_assign_pfunc.
      simpl_pfunc.
      case (is_constant_on_var (eval_map a c) c); last first.
        by simpl_pfunc.
      move: Hin => /(_ c) Hin.
      case (eq_V (eval_pfunc (a c) (pointwise_un_op R VVal)) (VVal 0)) eqn:HeqV => [ | //].
      rewrite /eq_V in HeqV.
      move: HeqV.
      case (eval_pfunc (a c) ((pointwise_un_op R VVal))) eqn:HV0 => [//| /Z.eqb_eq Himpossible|//].
      rewrite Himpossible in Hin.
      by case (eval_map R c) eqn:HeRc0.
    + rewrite /pfunc_map_assign_pfunc.
      simpl_pfunc.
      rewrite /constant_or_set_to_top_pfunc.
      case (is_constant_on_var (a s1) c) => [ | ].
      * by apply Hin.
      * by simpl_pfunc.
Qed.


Definition transfer_pfunc_map {PFunc: Type} {PI: PFuncImpl PFunc} {A: adom (@total_map string_eqType PFunc)} (inst: Instruction) (a: total_map) (l: label):=
  match inst with
  | Const v c => (pfunc_assign_const a v c, l + 1)::nil
  | BinOp v opc op1 op2 op1_ne_v op2_ne_v => (pfunc_assign_arith a v op1 op2 opc, l+1)::nil
  | Br l' params => (transfer_pfunc_map_branch a l' params)::nil
  | BrC c l1 params1 l2 params2 => transfer_pfunc_map_branch_cond a c l1 params1 l2 params2
  end.

Theorem transfer_presburger_set_sound {PFunc: Type} (PI: PFuncImpl PFunc) :
  forall prog R l R' l',
    step prog (R, l) (R', l') ->
    forall inst, Some inst = List.nth_error prog l ->
            forall a, Ensembles.In (total_map) (gamma a) R ->
                 exists a', List.In (a', l') (transfer_pfunc_map inst a l) /\
                       Ensembles.In (total_map) (gamma a') R'.
Proof.
  move => prog R l R' l' Hstep inst.
  move: prog R l R' l' Hstep.
  case inst.
  - by apply transfer_pfunc_map_const_sound.
  - by apply transfer_pfunc_map_arith_sound.
  - by apply transfer_pfunc_map_branch_sound.
  - by apply transfer_pfunc_map_branch_cond_sound.
Qed.