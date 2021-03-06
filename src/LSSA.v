From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export TotalMap ssrstring ssrZ Tactic.
From Coq Require Export Bool.Bool Strings.String Numbers.BinNums ZArith.BinInt.
From mathcomp.ssreflect Require Export seq.
Local Set Warnings "-notation-overridden".
From mathcomp.ssreflect Require Import ssrnat.

Local Open Scope type_scope.

(*
This is the definition of a loop aware SSA language.
 *)

Definition vid := string.
Definition bbid := string.
Definition bbid_eqType := string_eqType.

(* Every variable has a value, even the non defined ones *)
Definition RegisterMap := @total_map_eqType string_eqType Z_eqType.

(* The label is the program counter *)
Definition state := bbid * nat * RegisterMap.

(* Basics binary arithmetic opcodes *)
Inductive BinArithOpCode :=
| OpAdd
| OpMul
| OpLe.

(* An arithmetic instruction *)
Inductive Inst :=
| Const (v: vid) (c: Z)
| BinOp (v: vid) (b: BinArithOpCode) (op1 op2: vid): v <> op1 -> v <> op2 -> Inst.

(* A terminator of a basic block *)
Inductive Term :=
| Br (bb: bbid) (params: seq vid)
| BrC (c: vid) (bbT: bbid) (paramsT: seq vid)
      (bbF: bbid) (paramsF: seq vid).

(* A basic block. Has a list of parameters,
 a list of instructions, and a terminator *)
Definition BasicBlock :=
  (seq vid) * (seq Inst) * Term.

(* A program is a set of basic blocks indexed by their bbid *)
Definition Program := @partial_map string_eqType BasicBlock.

(* A program structure is either a basic block, a loop that contains a header and
 a body, or the concatenation of two program strutures *)
Inductive ProgramStructure :=
| Loop (header: bbid) (body: ProgramStructure)
| DAG (p1 p2: ProgramStructure)
| BB (bb: bbid).

Local Open Scope string_scope.
Local Open Scope seq_scope.

(* [affect_variables R [(o1,i1); ... ; (oN, iN)]] will affect i1 to o1, then i2 to o2... *)
Fixpoint affect_variables (R: RegisterMap) (vars inputs: seq vid) :=
  match (vars, inputs) with
  | (nil, _) => R
  | (_, nil) => R
  | (var::vars', input::inputs') => affect_variables (var !-> R input; R) vars' inputs'
  end.

(* Get inputs of a basic block given its id,
   and return nil if the id is not found *)
Fixpoint get_inputs (p: Program) (id: bbid) :=
  match p id with
  | Some (inputs, _, _) => inputs
  | None => nil
  end.

Definition vars_in_inst (i: Inst) :=
  match i with
  | Const v _ | BinOp v _ _ _ _ _ => [::v]
  end.

Fixpoint vars_in_program_ (p: Program) :=
  match p with
  | PEmpty => [::""]
  | PUpdate m' _ bb => (foldl (fun acc inst => acc ++ (vars_in_inst inst)) [::] bb.1.2) ++ (vars_in_program_ m')
  end.

Definition vars_in_program (p: Program) :=
  undup (vars_in_program_ p).

Theorem size_vars_in_program :
  forall p, 0 < size (vars_in_program p).
Proof.
  move => p.
  have: ("" \in (vars_in_program p)).
  - elim p => [ // | m Hind k v /= ]. rewrite /vars_in_program mem_undup /= mem_cat.
    apply /orP. right. by rewrite /vars_in_program mem_undup in Hind.
  - move => Hlt. rewrite -has_predT. apply /hasP. by exists "".
Qed.

Theorem uniq_vars_in_program :
  forall p, uniq (vars_in_program p).
Proof.
  move => p. by rewrite undup_uniq.
Qed.

Fixpoint bbs_in_program (p: ProgramStructure) :=
  match p with
  | Loop header body => header::(bbs_in_program body)
  | DAG p1 p2 => (bbs_in_program p1) ++ (bbs_in_program p2)
  | BB bb => bb::nil
  end.

(* Return list of basic blocks that are inside a loop body.
   Note that the body does not contain the header. *)
Fixpoint bbs_in_loops (p: ProgramStructure) :=
  match p with
  | Loop header body => bbs_in_program body
  | DAG p1 p2 => (bbs_in_loops p1) ++ (bbs_in_loops p2)
  | BB _ => nil
  end.

Definition term_successors (term: Term) :=
  match term with
  | Br succ _ => succ::nil
  | BrC _ succ1 _ succ2 _ => succ1::succ2::nil
  end.

Fixpoint program_successors (p: Program) (ps: ProgramStructure) :=
  match ps with
  | Loop header body =>
    match (p header) with
    | Some (_, t) => (term_successors t) ++ (program_successors p body)
    | None => program_successors p body
    end
  | DAG ps1 ps2 => (program_successors p ps1) ++ (program_successors p ps2)
  | BB bb =>
    match (p bb) with
    | Some (_, t) => (term_successors t)
    | None => nil
    end
  end.

Theorem program_successors_spec (p: Program) (ps: ProgramStructure) :
  forall bb_id, (exists in_id, (in_id \in bbs_in_program ps) /\
                    match (p in_id) with
                    | Some (_, t) => bb_id \in (term_successors t)
                    | None => false
                    end)
           -> (bb_id \in program_successors p ps).
Proof.
  elim: ps.
  - move => header_id body Hind bb_id [in_id [/= Hin_in Hin]].
    move: Hin_in. rewrite in_cons => /orP [/eqP Hineq | Hin_in].
    + move: Hin. rewrite Hineq. case (p header_id) => [ [[header_inputs header_insts] header_term]| // ].
        by rewrite mem_cat => ->.
    + move: Hin. case_eq (p in_id) => [[[in_inputs in_insts] in_term] Hin_id | //].
      case (p header_id) => [[[header_inputs header_insts] header_term] | ] Hbb_in_term.
      * move => /(_ bb_id) in Hind. rewrite mem_cat.
        have -> : (bb_id \in program_successors p body); last first. by rewrite orb_true_r.
        apply Hind. exists in_id. by rewrite Hin_id.
      * apply (Hind bb_id). exists in_id. by rewrite Hin_id.
  - move => ps1 Hind1 ps2 Hind2 bb_id [in_id [Hin_in ]] Hpin_id.
    move: Hin_in. rewrite /= mem_cat => /orP[Hin1 | Hin2].
    + rewrite mem_cat. apply /orP. left. eauto.
    + rewrite mem_cat. apply /orP. right. eauto.
  - move => bb_id bb /= [in_id [Hin Hin_in]].
    rewrite mem_seq1 in Hin. move => /eqP in Hin. rewrite -Hin.
    move: Hin_in. case (p in_id) => [ [[bb_inputs bb_insts] bb_term] // | //].
Qed.

Definition program_predecessors (p: Program) (bb_id: bbid) :=
  let keys := keys_list p in
  filter (fun k => match p k with
                | Some (_,t) => bb_id \in (term_successors t)
                | None => false
                end ) keys.

Theorem program_predecessors_spec (p: Program) (bb_id: bbid) :
  forall bb_id', bb_id' \in (program_predecessors p bb_id) =
                       match (p bb_id') with
                       | Some (_, t) => bb_id \in (term_successors t)
                       | None => false
                       end.
Proof.
  move => bb_id'.
  rewrite mem_filter.
  apply/idP/idP.
  - by move => /andP[].
  - move => Hbb. apply /andP.
    split; auto. apply keys_list_spec. move: Hbb.
      by case (p bb_id').
Qed.


Fixpoint structure_sound (p: Program) (ps: ProgramStructure) :=
  match ps with
  | Loop header body =>
    (header \notin (bbs_in_program body)) &&
    all (fun bb_id => all (fun bb_id' => bb_id' \in header::(bbs_in_program body)) (program_predecessors p bb_id)) (bbs_in_program body) &&
    (structure_sound p body) &&
    match p header with
    | None => false
    | Some _ => true
    end
  | DAG ps1 ps2 =>
    all (fun s => s \notin (bbs_in_program ps2)) (bbs_in_program ps1) &&
    all (fun s => s \notin (bbs_in_program ps1)) (bbs_in_program ps2) &&
    all (fun s => s \notin (bbs_in_program ps1)) (program_successors p ps2) &&
    structure_sound p ps1 &&
    structure_sound p ps2
  | BB bb =>
    match p bb with
    | None => false
    | Some (_,term) => bb \notin (term_successors term)
    end
  end.

Local Open Scope Z_scope.

(* The evaluation of a binary operation *)
Definition bin_op_eval (op : BinArithOpCode) (v1 v2 : Z) :=
  match op with
  | OpAdd => v1 + v2
  | OpMul => v1 * v2
  | OpLe => if v1 <=? v2 then 1 else 0
  end.

(* The semantics of arithmetic instructions *)
Inductive inst_step: Inst -> RegisterMap -> RegisterMap -> Prop :=
| ConstStep (v: vid) (c: Z) (R: RegisterMap):
    inst_step (Const v c) R (v !-> c; R)
| BinOpStep (v: vid) (opc: BinArithOpCode) (op1 op2: vid) (H1: v <> op1) (H2: v <> op2) (R: RegisterMap):
    inst_step (BinOp v opc op1 op2 H1 H2) R (v !-> bin_op_eval opc (R op1) (R op2); R).

(* The semantics of a terminator *)
Inductive term_step: Program -> Term -> RegisterMap -> (bbid * RegisterMap)
                           -> Prop :=
| BrStep (p: Program) (bb: bbid) (params: list vid) (R: RegisterMap) :
    term_step p (Br bb params) R (bb, (affect_variables R (get_inputs p bb) params))
| BrCTrueStep (p: Program) (c: vid) (bbT bbF: bbid) (paramsT paramsF: list vid) (R: RegisterMap) :
    R c <> 0 ->
    term_step p (BrC c bbT paramsT bbF paramsF) R
                    (bbT, (affect_variables R (get_inputs p bbT) paramsT))
| BrCFalseStep (p: Program) (c: vid) (bbT bbF: bbid) (paramsT paramsF: list vid) (R: RegisterMap) :
    R c = 0 ->
    term_step p (BrC c bbT paramsT bbF paramsF) R
                    (bbF, (affect_variables R (get_inputs p bbF) paramsF))
.

Theorem term_successors_spec (p: Program) (term: Term) :
  forall out_id R R', term_step p term R (out_id, R') ->
                 out_id \in term_successors term.
Proof.
  move => out_id R R' Hterm_step.
  inversion Hterm_step; subst.
  - by rewrite in_cons eq_refl.
  - by rewrite in_cons eq_refl.
  - by rewrite in_cons in_cons eq_refl orb_true_r.
Qed.


(* The small step semantics of a program *)
Inductive step: Program -> state -> state -> Prop :=
| InstStep (p: Program) (bb_id: bbid) (params: list vid) (insts: list Inst) (term: Term) :
    p bb_id = Some (params, insts, term) ->
    forall l inst, List.nth_error insts l = Some inst ->
            forall R R', inst_step inst R R' ->
                    step p (bb_id, l, R) (bb_id, S l, R')
| TermStep (p: Program) (bb_id: bbid) (params: list vid) (insts: list Inst) (term: Term) :
    p bb_id = Some (params, insts, term) ->
    forall l, List.nth_error insts l = None ->
         forall new_bbid R R', term_step p term R (new_bbid, R') ->
                          step p (bb_id, l, R) (new_bbid, O, R').

(* The reflexive and transitive closure of the trans relation *)
Inductive multi_step: Program -> state -> state -> Prop :=
| StepRefl : forall p s, multi_step p s s
| StepTrans : forall p s s' s'', multi_step p s s' -> step p s' s'' -> multi_step p s s''.

Definition reachable_states (p: Program) (R: RegisterMap) (s: state) :=
multi_step p ("entry", O, R) s.

Open Scope nat_scope.

Theorem multi_step_trans :
  forall p s0 s1 s2, multi_step p s0 s1 -> multi_step p s1 s2 -> multi_step p s0 s2.
Proof.
  move => p s0 s1 s2 H01 H12.
  induction H12 => [// | ].
  apply IHmulti_step in H01.
    by eapply StepTrans; eauto.
Qed.

Theorem reachable_states_pos (p: Program) (R: RegisterMap) (s: state) :
  reachable_states p R s ->
  match p s.1.1 with
  | Some (_, insts, _) => s.1.2 <= List.length insts
  | Non => true
  end.
Proof.
  rewrite /reachable_states.
  move s1 : ("entry", O, R) => Hs1 Hmulti_step.
  elim: Hmulti_step s1.
  - move => p0 s0 <- /= .
    case (p0 "entry") => [ [[_ insts] _] | //].
    case insts => [ // | i l /=].
      by apply leq0n.
  - move => p0 s0 s' s'' Hmulti_step Hind Hstep Hs0.
    inversion Hstep; subst.
    + move: Hind => /(_ (erefl _)) /=. case_eq (p0 bb_id) => [ [[inputs' insts'] term'] Hbb'| //].
      rewrite H in Hbb'. inversion Hbb'. subst.
      have Hne_None : (List.nth_error insts' l <> None). move: H0. case (List.nth_error insts' l) => //.
      apply List.nth_error_Some in Hne_None.
      by move => /ltP in Hne_None.
    + rewrite /=. case (p0 new_bbid) => [[[_ insts'] _] | //]. case insts' => [ // | i' l' /=].
      by apply leq0n.
Qed.

Theorem step_entering_loop :
  forall p header_id body,
    let loop := Loop header_id body in
    structure_sound p loop ->
    forall s_in, (s_in.1.1 \notin (bbs_in_program loop)) ->
            forall s_out, (s_out.1.1 \in (bbs_in_program loop)) ->
                     step p s_in s_out ->
                     s_out.1.1 = header_id /\ s_out.1.2 = 0.
Proof.
  move => p header_id body loop Hsound s_in Hs_in_notin s_out Hs_out_in Hstep.
  have H_s_in_out_ne: (s_in <> s_out). move => H_s_in_out_eq. subst. by rewrite Hs_out_in in Hs_in_notin.
  inversion Hstep. bigsubst. by rewrite Hs_out_in in Hs_in_notin.
  bigsubst. rewrite /=. split; auto.
  inversion Hsound. move: H3 => /andP[/andP[/andP[_ /allP Hpred] _] _].
  move => /= in Hs_out_in. rewrite in_cons in Hs_out_in. move => /orP in Hs_out_in.
  case: Hs_out_in; first by autossr.
  move => /Hpred /allP.
  apply term_successors_spec in H1.
  move: (program_predecessors_spec p new_bbid bb_id).
  rewrite H H1 => H_in_predecessors. move => /(_ bb_id H_in_predecessors).
    by autossr.
Qed.

Theorem multi_step_loop :
  forall p header_id body,
    let loop := Loop header_id body in
    structure_sound p loop ->
    forall s_entry, (s_entry.1.1 \notin (bbs_in_program loop)) ->
               forall s_bb, (s_bb.1.1 \in (bbs_in_program loop)) ->
                       multi_step p s_entry s_bb <->
                       exists R_header, multi_step p s_entry (header_id, 0, R_header) /\
                                   multi_step p (header_id, 0, R_header) s_bb.
Proof.
  move => p header_id body loop Hsound s_entry H_entry_notin s_bb H_bb_in.
  split => [ H_multi_step | [R_header [H01 H12]]]; last by eapply multi_step_trans; eauto.
  move Hp : p => p'. rewrite Hp in H_multi_step.
  elim: H_multi_step Hp H_bb_in H_entry_notin; first by move => p0 s _ ->.
  move => p0 s s' s'' Hmulti_step Hind Hstep Hp H_s''_in H_s_notin.
  case Hs'_in : (s'.1.1 \in bbs_in_program loop). by case: (Hind Hp Hs'_in H_s_notin) => R_header [H0 H1]; eexists; split; eauto; econstructor; eauto.
  have H_s'_s''_ne: (s' <> s''). move => H_s'_s''_eq. subst. by rewrite H_s''_in in Hs'_in.
  bigsubst. move => /negb_true_iff in Hs'_in. move: (step_entering_loop _ _ _ Hsound _ Hs'_in _ H_s''_in Hstep) => [H_s''_header H_s''_pos_0].
  exists s''.2. rewrite -H_s''_header -H_s''_pos_0.
  rewrite -!surjective_pairing. split; last by constructor.
  econstructor; eauto.
Qed.

Definition step_cond (p: Program) (s s': state) (avoid: seq bbid) :=
  step p s s' /\ ~~ ((s'.1.1 \in avoid) && (s'.1.2 != 0)).

Inductive multi_step_cond: Program -> state -> state -> seq bbid -> Prop :=
| StepCondRefl : forall p s l, multi_step_cond p s s l
| StepCondTrans : forall p s s' s'' l, multi_step_cond p s s' l -> step_cond p s' s'' l -> multi_step_cond p s s'' l.

Theorem multi_step_cond_trans:
  forall p s' s s'' l, multi_step_cond p s s' l ->
                     multi_step_cond p s' s'' l ->
                     multi_step_cond p s s'' l.
Proof.
  move => p s' s s'' l H01 H12.
  induction H12 => [ // | ].
  apply IHmulti_step_cond in H01.
    by eapply StepCondTrans; eauto.
Qed.

Theorem step_cond_cons:
  forall p s s' bb_id l, step_cond p s s' (bb_id::l) -> step_cond p s s' l.
Proof.
  move => p s s' bb_id l [Hstep /nandP [Hnotin | Hnot0]]; rewrite /step_cond; autossr.
Qed.

Theorem multi_step_cond_cons:
  forall p s s' bb_id l, multi_step_cond p s s' (bb_id::l) ->
                    multi_step_cond p s s' l.
Proof.
  move => p s s' bb_id l Hmulti.
  move Hl_cons : (bb_id :: l) => l_cons. rewrite Hl_cons in Hmulti.
  induction Hmulti; first by constructor.
  eapply StepCondTrans; eauto.
  rewrite -Hl_cons in H. by eapply step_cond_cons; eauto.
Qed.

Section Example.

  Definition y_ne_x : "y" <> "x".
  Proof.
      by apply /eqP.
  Qed.

  Definition y_ne_one : "y" <> "one".
  Proof.
      by apply /eqP.
  Qed.

  Definition c_ne_y : "c" <> "y".
  Proof.
      by apply /eqP.
  Qed.

  Definition c_ne_one : "c" <> "one".
  Proof.
      by apply /eqP.
  Qed.

  Definition entry_bb := (@nil string,
                          (Const "zero" 0)::(Const "one" 1)::nil,
                          (Br "loop" ("zero"::nil))).

  Definition loop_bb := ("x"::nil,
                         (BinOp "y" OpAdd "x" "one" y_ne_x y_ne_one)::
                         (BinOp "c" OpLe "y" "one" c_ne_y c_ne_one)::nil,
                         (BrC "c" "loop" ("y"::nil) "exit" ("y"::nil))).

  Definition dummy_bb := (@nil string, @nil Inst, (Br "loop" ([::"y"]))).

  Definition exit_bb := ("exitvalue"::nil, @nil Inst, (Br "finished" nil)).

  Definition prog := ("entry" !!-> entry_bb; "loop" !!-> loop_bb; "dummy" !!-> dummy_bb; "exit" !!-> exit_bb).

  Definition progstruct := DAG (BB "entry") (DAG (Loop "loop" (BB "dummy")) (BB "exit")).

  Example progstruct_correct :
    structure_sound prog progstruct.
  Proof.
      by [].
  Qed.

End Example.
