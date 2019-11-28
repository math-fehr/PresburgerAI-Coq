From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export Presburger AbstractDomain RelationalAbstractDomain LSSA RelationalTransferFunction.
From mathcomp.ssreflect Require Export seq.

Section PMapAbstractDomain.

  Context {PMap PSet PwAff: eqType}
          {PI: PresburgerImpl PMap PSet PwAff}
          (prog: Program).

  Definition concrete_state := prod_eqType RegisterMap RegisterMap.

  Definition gamma_pmap (m: PMap) : Ensemble concrete_state:=
    fun R => eval_pmap m R.1 R.2.

  Theorem gamma_pmap_monotone :
    forall a1 a2, is_subset_map a1 a2 <-> Included concrete_state (gamma_pmap a1) (gamma_pmap a2).
  Proof.
    move => a1 a2.
    rewrite is_subset_map_spec /Included.
    split.
    - move => Hle [x1 x2] HIn.
      by apply (Hle x1 x2).
    - move => Hle x1 x2 Heval.
      set x := (x1, x2).
      have -> : x1 = x.1 by [].
      have -> : x2 = x.2 by [].
      by apply Hle.
  Qed.

  Theorem gamma_pmap_top :
    forall x, Ensembles.In concrete_state (gamma_pmap universe_map) x.
  Proof.
    move => x.
    rewrite /gamma_pmap /Ensembles.In.
      by auto_presburger.
  Qed.

  Theorem gamma_pmap_bot :
    forall x, ~ Ensembles.In concrete_state (gamma_pmap empty_map) x.
  Proof.
    move => x.
    rewrite /gamma_pmap /Ensembles.In.
      by auto_presburger.
  Qed.

  Theorem join_pmap_sound_l :
    forall a1 a2, is_subset_map a1 (union_map a1 a2).
  Proof.
    move => a1 a2.
    apply is_subset_map_spec => x1 x2.
      by simpl_presburger => ->.
  Qed.

  Theorem join_pmap_sound_r :
    forall a1 a2, is_subset_map a2 (union_map a1 a2).
  Proof.
    move => a1 a2.
    apply is_subset_map_spec => x1 x2.
    simpl_presburger => ->.
    by autossr.
  Qed.

  Instance adom_pmap : adom concrete_state PMap :=
    {
      le := is_subset_map;
      bot := empty_map;
      top := universe_map;
      join := union_map;

      gamma := gamma_pmap;

      le_refl := is_subset_map_refl;
      le_trans := is_subset_map_trans;
      gamma_monotone := gamma_pmap_monotone;
      gamma_top := gamma_pmap_top;
      gamma_bot := gamma_pmap_bot;
      join_sound_l := join_pmap_sound_l;
      join_sound_r := join_pmap_sound_r;
    }.

  Theorem pmap_id_relation_spec :
    forall x0 x1, Ensembles.In _ (gamma id_map) (x0, x1) <-> x0 = x1.
  Proof.
    move => x0 x1.
    rewrite /Ensembles.In /gamma /= /gamma_pmap /= id_map_spec.
      by split; autossr.
  Qed.

  Theorem pmap_compose_relation_spec :
    forall a1 a2 x0 x2, Ensembles.In _ (gamma (map_apply_range a1 a2)) (x0, x2) <->
                   exists x1, Ensembles.In _ (gamma a1) (x0, x1) /\ Ensembles.In _ (gamma a2) (x1, x2).
  Proof.
    move => a1 a2 x0 x2.
    rewrite /Ensembles.In /gamma /= /gamma_pmap /=.
      by apply map_apply_range_spec.
  Qed.

  Instance adom_relational_pmap : adom_relational adom_pmap :=
    {
      id_relation := id_map;
      id_relation_spec := pmap_id_relation_spec;

      compose_relation := map_apply_range;
      compose_relation_spec := pmap_compose_relation_spec;

      compose_bot := map_apply_range_bot;

      transitive_closure := transitive_closure_map;
      transitive_closure_ge_id := transitive_closure_map_ge_id;
      transitive_closure_ge_step := transitive_closure_map_ge_step;
      transitive_closure_eq_compose := transitive_closure_map_eq_compose;
    }.

  Definition pmap_set_out_var_const (m: PMap) (v: string) (c: Z) :=
  let c_map := Presburger.eq_map (pw_aff_from_aff (AConst 0)) (pw_aff_from_aff (AVar v)) (pw_aff_from_aff (AConst 0)) (pw_aff_from_aff (AConst c)) in
  let m := map_project_out_out m v in
  intersect_map c_map m.

  Theorem pmap_set_out_var_const_spec (m: PMap) :
    forall x0 x1, Ensembles.In _ (gamma m) (x0, x1) ->
             forall v c, Ensembles.In _ (gamma (pmap_set_out_var_const m v c)) (x0, (v !-> c ; x1)).
  Proof.
    move => x0 x1 Heval v c.
    rewrite /gamma /= /gamma_pmap /Ensembles.In /= /pmap_set_out_var_const.
    simpl_presburger.
    apply map_project_out_out_spec.
    exists (x1 v). by simpl_map.
  Qed.

  Theorem pmap_set_out_var_const_tf_sound :
    forall v c R R', inst_step (Const v c) R R' ->
                 forall m R_begin, Ensembles.In _ (gamma m) (R_begin, R) ->
                              Ensembles.In _ (gamma (pmap_set_out_var_const m v c)) (R_begin, R').
  Proof.
    move => v c R R' Hstep m R_begin HIn.
    inversion Hstep. subst.
      by apply pmap_set_out_var_const_spec.
  Qed.

  (* Transfer function for binary arithmetic operation *)
  Definition binop_to_pwaff (res: vid) (opc: BinArithOpCode) (op1 op2: vid) :=
    match opc with
    | OpAdd => pw_aff_from_aff (APlus (AVar op1) (AVar op2))
    | OpMul => pw_aff_from_aff (AVar res)
    | OpLe => indicator_function (le_set (pw_aff_from_aff (AVar op1)) (pw_aff_from_aff (AVar op2)))
    end.

  Definition pmap_set_out_var_binop (m: PMap) (res: vid) (opc: BinArithOpCode) (op1 op2: vid) :=
    let p2' := binop_to_pwaff res opc op1 op2 in
    let c_map := Presburger.eq_map (pw_aff_from_aff (AConst 0)) (pw_aff_from_aff (AVar res)) (pw_aff_from_aff (AConst 0)) p2' in
    let m_projected := map_project_out_out m res in
    let new_map := intersect_map c_map m_projected in
    new_map.

  Theorem pmap_set_out_var_binop_spec (m: PMap) :
    forall x0 x1, Ensembles.In _ (gamma m) (x0, x1) ->
      forall res op1, res != op1 ->
        forall op2, res != op2 ->
          forall opc, Ensembles.In _ (gamma (pmap_set_out_var_binop m res opc op1 op2)) (x0, (res !-> bin_op_eval opc (x1 op1) (x1 op2); x1)).
  Proof.
    move => x0 x1 HIn res op1 Hop1 op2 Hop2 opc.
    rewrite /gamma /= /gamma_pmap /Ensembles.In /pmap_set_out_var_binop /= /binop_to_pwaff.
    case opc; simpl_presburger.
    - apply map_project_out_out_spec.
      exists (x1 res).
        by auto_presburger.
    - apply map_project_out_out_spec.
      exists (x1 res).
        by auto_presburger.
    - case (_ <=? _)%Z; simplssr; apply map_project_out_out_spec; exists (x1 res); by auto_presburger.
  Qed.

  Theorem pmap_set_out_var_binop_tf_sound :
    forall res opc op1 op2 Hop1 Hop2 R R',
      inst_step (BinOp res opc op1 op2 Hop1 Hop2) R R' ->
      forall m R_begin, Ensembles.In _ (gamma m) (R_begin, R) ->
                   Ensembles.In _ (gamma (pmap_set_out_var_binop m res opc op1 op2)) (R_begin, R').
  Proof.
    move => res opc op1 op2 Hop1 Hop2 R R' Hinst m R_begin Hin.
    by case: opc Hinst => Hinst; inversion Hinst; subst; apply pmap_set_out_var_binop_spec; autossr.
  Qed.

  Definition pmap_tf_inst (inst: Inst) (m: PMap) :=
    match inst with
    | Const res c => pmap_set_out_var_const m res c
    | BinOp res opc op1 op2 op1_ne_res op2_ne_res => pmap_set_out_var_binop m res opc op1 op2
    end.

  Theorem pmap_tf_inst_sound :
    forall inst R R',
      inst_step inst R R' ->
      forall m R_begin, Ensembles.In _ (gamma m) (R_begin, R) ->
                   Ensembles.In _ (gamma (pmap_tf_inst inst m)) (R_begin, R').
  Proof.
    move => inst R R' Hinst m R_begin Hin.
    case: inst Hinst => [ res v | res opc op1 op2 Hop1 Hop2 ] Hinst.
    - eapply pmap_set_out_var_const_tf_sound; eauto.
    - eapply pmap_set_out_var_binop_tf_sound; eauto.
  Qed.

  (* Transfer function for unconditional branch instruction *)
  Fixpoint pmap_affect_variables (m: PMap) (vars inputs: list vid) :=
    match (vars, inputs) with
    | (nil, _) => m
    | (_, nil) => m
    | (var::vars', input::inputs') =>
      if var == input then
        pmap_affect_variables m vars' inputs'
      else
        let c_map := Presburger.eq_map (pw_aff_from_aff (AConst 0)) (pw_aff_from_aff (AVar var)) (pw_aff_from_aff (AConst 0)) (pw_aff_from_aff (AVar input)) in
        let m_projected := map_project_out_out m var in
        let new_m := intersect_map c_map m_projected in
        pmap_affect_variables new_m vars' inputs'
    end.

  Theorem pmap_affect_variables_sound :
    forall R_begin R m,
      Ensembles.In _ (gamma m) (R_begin, R) ->
      forall vars inputs, Ensembles.In _ (gamma (pmap_affect_variables m vars inputs)) (R_begin, affect_variables R vars inputs).
  Proof.
    move => R_begin R m Hin vars.
    elim: vars R_begin R m Hin => [// | var vars Hind R_begin R m Hin inputs].
    case: inputs => [ // | input inputs /=].
    case (var =P input) => [ -> /= | ].
    - apply Hind. rewrite /gamma /= /Ensembles.In /gamma_pmap /=. by auto_map.
    - move => Hne. apply Hind. rewrite /gamma /= /Ensembles.In /gamma_pmap /=.
      simpl_presburger. apply map_project_out_out_spec.
      exists (R var). by auto_map.
  Qed.

  Definition pmap_tf_branch (out_id: bbid) (inputs: seq vid) (m: PMap) :=
    [::(pmap_affect_variables m (get_inputs prog out_id) inputs, out_id)].

  Theorem pmap_tf_branch_sound :
    forall out_id inputs out_id' R R',
      term_step prog (Br out_id inputs) R (out_id', R') ->
      forall m R_begin, Ensembles.In _ (gamma m) (R_begin, R) ->
                   exists m', ((m', out_id') \in (pmap_tf_branch out_id inputs m)) /\
                         Ensembles.In  _ (gamma m') (R_begin, R').
  Proof.
    move => out_id inputs out_id' R R' Hterm m R_begin Hin.
    inversion Hterm. subst.
    eexists. split.
    - rewrite mem_seq1. by apply eq_refl.
    - by apply pmap_affect_variables_sound.
  Qed.

  Definition pmap_tf_branch_cond (cond: vid) (out_id_t: bbid) (inputs_t: seq vid) (out_id_f: bbid) (inputs_f: seq vid) (m: PMap) :=
    let map_true := ne_map (pw_aff_from_aff (AConst 0)) (pw_aff_from_aff (AVar cond)) (pw_aff_from_aff (AConst 0)) (pw_aff_from_aff (AConst 0)) in
    let map_true' := intersect_map map_true m in
    let res_map_true := pmap_affect_variables map_true' (get_inputs prog out_id_t) inputs_t in
    let map_false := Presburger.eq_map (pw_aff_from_aff (AConst 0)) (pw_aff_from_aff (AVar cond)) (pw_aff_from_aff (AConst 0)) (pw_aff_from_aff (AConst 0)) in
    let map_false' := intersect_map map_false m in
    let res_map_false := pmap_affect_variables map_false' (get_inputs prog out_id_f) inputs_f in
    [::(res_map_true, out_id_t);(res_map_false, out_id_f)].

  Theorem pmap_tf_branch_cond_sound :
    forall cond out_id_t inputs_t out_id_f inputs_f out_id' R R',
      term_step prog (BrC cond out_id_t inputs_t out_id_f inputs_f) R (out_id', R') ->
      forall m R_begin, Ensembles.In _ (gamma m) (R_begin, R) ->
                   exists m', ((m', out_id') \in (pmap_tf_branch_cond cond out_id_t inputs_t out_id_f inputs_f m)) /\
                         Ensembles.In  _ (gamma m') (R_begin, R').
  Proof.
    move => cond out_id_t inputs_t out_id_f inputs_f out_id' R R' Hterm m R_begin HIn.
    inversion Hterm; subst.
    - eexists. split.
      + rewrite in_cons. apply /orP. left. by apply eq_refl.
      + apply pmap_affect_variables_sound.
        rewrite /= /gamma_pmap /Ensembles.In. by auto_presburger.
    - eexists. split.
      + rewrite in_cons mem_seq1. apply /orP. right. by apply eq_refl.
      + apply pmap_affect_variables_sound.
        rewrite /= /gamma_pmap /Ensembles.In. simpl_presburger.
        rewrite H6. by autossr.
  Qed.

  Definition pmap_tf_term (term: Term) (m: PMap) :=
    match term with
    | Br out_id inputs => pmap_tf_branch out_id inputs m
    | BrC cond out_id_t inputs_t out_id_f inputs_f => pmap_tf_branch_cond cond out_id_t inputs_t out_id_f inputs_f m
    end.

  Theorem pmap_tf_term_sound :
    forall term R bb R',
      term_step prog term R (bb, R') ->
      forall m R_begin, Ensembles.In _ (gamma m) (R_begin, R) ->
                   exists m', ((m', bb) \in (pmap_tf_term term m)) /\
                         Ensembles.In  _ (gamma m') (R_begin, R').
  Proof.
    move => term R bb R'. case term.
    - intros. eapply pmap_tf_branch_sound; eauto.
    - intros. eapply pmap_tf_branch_cond_sound; eauto.
  Qed.

  Instance tf_relational_pmap : transfer_function_relational adom_relational_pmap prog :=
    {
      transfer_inst := pmap_tf_inst;
      transfer_inst_sound := pmap_tf_inst_sound;

      transfer_term := pmap_tf_term;
      transfer_term_sound := pmap_tf_term_sound;
    }.
  Admitted.


End PMapAbstractDomain.
