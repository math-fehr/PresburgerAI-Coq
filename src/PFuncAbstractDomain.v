From Coq Require Import ssreflect ssrfun ssrbool.
From Coq Require Import ssrbool Ensembles.
From PolyAI Require Export PFunc LSSA AbstractDomain.
Local Set Warnings "-notation-overridden".
From mathcomp Require Import ssrnat eqtype.

Local Open Scope string_scope.

Module PFuncMap (FPI: FPresburgerImpl).
  Import FPI.
  Module PFI := PFuncImpl FPI.
  Import PFI.

  Definition concrete_state := prod_eqType RegisterMap RegisterMap.

  Definition to_var_values_seq (p: Program) (R: RegisterMap) :=
    List.map (fun v => R v) (vars_in_program p).

  Definition PFuncMap (p: Program) :=
    let n := size (vars_in_program p) in
    { x: seq (PFunc_eqType n) | size x == n}.

  Program Definition bot_PFuncMap (p: Program) : PFuncMap p :=
    let n := size (vars_in_program p) in
    (nseq n (constant_pfunc n VBot)).
  Next Obligation.
      by rewrite size_nseq.
  Qed.

  Program Definition top_PFuncMap (p: Program) : PFuncMap p :=
    let n := size (vars_in_program p) in
    nseq n (constant_pfunc n VTop).
  Next Obligation.
      by rewrite size_nseq.
  Qed.

  Program Definition join_PFuncMap {p: Program} (p1 p2: PFuncMap p) : PFuncMap p :=
    [ seq join_pfunc x.1 x.2 | x <- zip p1 p2].
  Next Obligation.
    rewrite size_map size_zip.
    case: p1. case: p2.
    move => x /eqP -> x0 /eqP ->.
      by rewrite ssrnat.minnn.
  Qed.

  Definition gamma_PFuncMap {p: Program} (pf: PFuncMap p) (x: concrete_state) :=
    let inputs := to_var_values_seq p x.1 in
    forall i, (x.2 (nth "" (vars_in_program p) i)) \inV (eval_pfunc (nth (constant_pfunc _ VTop) (sval pf) i) inputs).

  Theorem gamma_top_PFuncMap :
    forall p x, Ensembles.In _ (gamma_PFuncMap (top_PFuncMap p)) x.
  Proof.
    move => p x var_values i. rewrite /In /gamma_PFuncMap /top_PFuncMap nth_nseq.
    case_if; auto_pfunc.
  Qed.

  Theorem gamma_bot_PFuncMap :
    forall p x, ~ Ensembles.In _ (gamma_PFuncMap (bot_PFuncMap p)) x.
  Proof.
    rewrite /In /gamma_PFuncMap /bot_PFuncMap => p x /(_ 0). rewrite nth_nseq.
    case_if. by simpl_pfunc.
      by rewrite size_vars_in_program in H.
  Qed.

    Theorem join_sound_l_PFuncMap :
      forall p a1 a2, Included _ (@gamma_PFuncMap p a1) (gamma_PFuncMap (join_PFuncMap a1 a2)).
    Proof.
      rewrite /Included /In /gamma_PFuncMap /join_PFuncMap => p [a1 size_a1] [a2 size_a2].
      move: (size_a1) (size_a2).
      move => /eqP in size_a1. move => /eqP in size_a2.
      move => size_a1' size_a2' x Hle i.
      move => /(_ i) in Hle. move: Hle. simpl_pfunc.
      apply le_V_spec.
      case Hs : (i < size a1).
      - erewrite nth_map; last first. by rewrite size_zip size_a1 size_a2 minnn -size_a1.
        erewrite nth_zip; last first. by rewrite size_a1 size_a2.
        rewrite /= join_pfuncP.
          by apply join_V_leftP.
      - rewrite !nth_default.
        + by apply le_V_refl.
        + rewrite size_map size_zip size_a1 size_a2 minnn -size_a1.
            by rewrite leqNgt Hs.
        + by rewrite leqNgt Hs.
    Unshelve.
      eapply constant_pfunc.
      by apply VTop.
    Qed.

    Theorem join_sound_r_PFuncMap :
      forall p a1 a2, Included _ (@gamma_PFuncMap p a2) (gamma_PFuncMap (join_PFuncMap a1 a2)).
    Proof.
      rewrite /Included /In /gamma_PFuncMap /join_PFuncMap => p [a1 size_a1] [a2 size_a2].
      move: (size_a1) (size_a2).
      move => /eqP in size_a1. move => /eqP in size_a2.
      move => size_a1' size_a2' x Hle i.
      move => /(_ i) in Hle. move: Hle. simpl_pfunc.
      apply le_V_spec.
      case Hs : (i < size a2).
      - erewrite nth_map; last first. by rewrite size_zip size_a1 size_a2 minnn -size_a2.
        erewrite nth_zip; last first. by rewrite size_a1 size_a2.
        rewrite /= join_pfuncP.
          by apply join_V_rightP.
      - rewrite !nth_default.
        + by apply le_V_refl.
        + rewrite size_map size_zip size_a1 size_a2 minnn -size_a2.
            by rewrite leqNgt Hs.
        + by rewrite leqNgt Hs.
          Unshelve.
          eapply constant_pfunc.
            by apply VTop.
    Qed.

    Definition PFuncMap_eqMixin (p: Program) :=
      let n := size (vars_in_program p) in
      @sig_eqMixin (seq_eqType (PFunc_eqType n)) (fun x => size x == n).
    Canonical PFuncMap_eqType (p: Program) := Eval hnf in EqType (PFuncMap p) (PFuncMap_eqMixin p).

  Instance adom_pmap (p: Program) : adom concrete_state (PFuncMap_eqType p) p :=
    {
      bot := bot_PFuncMap p;
      top := top_PFuncMap p;
      join := join_PFuncMap;

      gamma := gamma_PFuncMap;

      gamma_top := gamma_top_PFuncMap p;
      gamma_bot := gamma_bot_PFuncMap p;
      join_sound_l := join_sound_l_PFuncMap p;
      join_sound_r := join_sound_r_PFuncMap p;
    }.

End PFuncMap.
