From PolyAI Require Export Presburger AbstractDomain PFunc.
Require Import PolyAI.SSA.
Require Export Coq.Sets.Ensembles.
From Coq Require Import ssreflect ssrfun ssrbool.

Definition gamma_pfunc_map {PFunc: Type} {PI: PFuncImpl PFunc} :=
  fun p r => forall s, in_V (eval_map r s) (eval_pfunc (eval_map p s) (eval_map (pointwise_un_op r VVal))).

Definition le_pfunc_map {PFunc: Type} {PI: PFuncImpl PFunc} :=
  fun a1 a2 => forall_bin_op a1 a2 le_pfunc.

Definition join_pfunc_map {PFunc: Type} {PI: PFuncImpl PFunc} :=
  fun p1 p2 => pointwise_bin_op p1 p2 join_pfunc.

Theorem le_pfunc_map_refl {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a, le_pfunc_map a a.
Proof.
  move => a.
  apply forall_bin_op_spec => v.
  apply le_pfunc_spec => x.
    by apply le_V_refl.
Qed.

Theorem le_pfunc_map_trans {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a1 a2 a3, le_pfunc_map a1 a2 -> le_pfunc_map a2 a3 -> le_pfunc_map a1 a3.
Proof.
  move => a1 a2 a3.
  rewrite !forall_bin_op_spec => H12 H23 v.
    by apply (le_pfunc_trans _ (eval_map a2 v)).
Qed.

Theorem gamma_pfunc_map_monotone {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a1 a2, le_pfunc_map a1 a2 -> Included RegisterMap (gamma_pfunc_map a1) (gamma_pfunc_map a2).
Proof.
  move => a1 a2 Hle.
  rewrite /le_pfunc_map forall_bin_op_spec /Included /In /gamma_pfunc_map in Hle *.
  move => Hle x Hin s.
  move: (Hle s).
  rewrite le_pfunc_spec => Htemp.
  move: (Htemp (eval_map (pointwise_un_op x VVal))).
  rewrite le_V_spec => Htemp2.
  by apply (Htemp2 (eval_map x s)).
Qed.

Theorem gamma_pfunc_map_top {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall x, Ensembles.In RegisterMap (gamma_pfunc_map (_ !-> constant_pfunc VTop)) x.
Proof.
  move => x.
  rewrite /In /gamma_pfunc_map => s.
    by simpl_pfunc.
Qed.

Theorem join_pfunc_map_sound_l {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a1 a2, le_pfunc_map a1 (join_pfunc_map a1 a2).
Proof.
  move => a1 a2.
  rewrite /join_pfunc_map /le_pfunc_map forall_bin_op_spec => v.
  rewrite pointwise_bin_op_spec.
  apply join_pfunc_spec_l.
Qed.

Theorem join_pfunc_map_sound_r {PFunc: Type} {PI: PFuncImpl PFunc} :
  forall a1 a2, le_pfunc_map a2 (join_pfunc_map a1 a2).
Proof.
  move => a1 a2.
  rewrite /join_pfunc_map /le_pfunc_map forall_bin_op_spec => v.
  rewrite pointwise_bin_op_spec.
  apply join_pfunc_spec_r.
Qed.

Instance PFuncMapAD {PFunc: Type} (PI: PFuncImpl PFunc) : adom (total_map PFunc) :=
  {
    le := le_pfunc_map;
    bot := (_ !-> constant_pfunc VBot);
    top := (_ !-> constant_pfunc VTop);
    join := join_pfunc_map;

    gamma := gamma_pfunc_map;

    le_refl := le_pfunc_map_refl;
    le_trans := le_pfunc_map_trans;
    gamma_monotone := gamma_pfunc_map_monotone;
    gamma_top := gamma_pfunc_map_top;
    join_sound_l := join_pfunc_map_sound_l;
    join_sound_r := join_pfunc_map_sound_r;
  }.