From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export TotalMap ssrstring ssrZ.
From Coq Require Export Bool.Bool Strings.String Numbers.BinNums ZArith.BinInt.
From mathcomp.ssreflect Require Export seq.

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
    | Some (_, _, t) => (term_successors t) ++ (program_successors p body)
    | None => program_successors p body
    end
  | DAG ps1 ps2 => (program_successors p ps1) ++ (program_successors p ps2)
  | BB bb =>
    match (p bb) with
    | Some (_, _, t) => (term_successors t)
    | None => nil
    end
  end.

Theorem program_successors_spec (p: Program) (ps: ProgramStructure) :
  forall bb_id, (exists in_id, (in_id \in bbs_in_program ps) /\
                    match (p in_id) with
                    | Some (_, _, t) => bb_id \in (term_successors t)
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
                | Some (_,_,t) => bb_id \in (term_successors t)
                | None => false
                end ) keys.

Theorem program_predecessors_spec (p: Program) (bb_id: bbid) :
  forall bb_id', bb_id' \in (program_predecessors p bb_id) =
                       match (p bb_id') with
                       | Some (_, _, t) => bb_id \in (term_successors t)
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
    (structure_sound p body) &&
    (header \notin (bbs_in_program body)) &&
    all (fun bb_id => all (fun bb_id' => bb_id' \in header::(bbs_in_program body)) (program_predecessors p bb_id)) (bbs_in_program body) &&
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
    | Some (_,_,term) => bb \notin (term_successors term)
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
| StepTrans : forall p s s' s'', step p s s' -> multi_step p s' s'' -> multi_step p s s''.

(* The reflexive and transitive closure of the trans relation,
   where every step should fulfill a proposition *)
Inductive multi_step_cond: Program -> (state -> state -> Prop) -> state -> state -> Prop :=
| StepCondRefl : forall p c s, multi_step_cond p c s s
| StepCondTrans : forall p (c: state -> state -> Prop) s s' s'',
    step p s s' -> c s s' -> multi_step_cond p c s' s'' -> multi_step_cond p c s s''.

(* Interpretation of a single instruction *)
Definition interpret_inst (inst: Inst) (R: RegisterMap) :=
  match inst with
  | Const v c => (v !-> c; R)
  | BinOp v opc op1 op2 _ _ => (v !-> bin_op_eval opc (R op1) (R op2); R)
  end.

Theorem interpret_inst_spec :
  forall inst R, inst_step inst R (interpret_inst inst R).
Proof.
  move => inst R.
  case inst; constructor.
Qed.

(* Interpretation of a single terminator *)
Definition interpret_term (p: Program) (t: Term) (R: RegisterMap) :=
  match t with
  | Br bb params => (bb, affect_variables R (get_inputs p bb) params)
  | BrC c bbT paramsT bbF paramsF =>
    if R c == 0 then
      (bbF, affect_variables R (get_inputs p bbF) paramsF)
    else
      (bbT, affect_variables R (get_inputs p bbT) paramsT)
  end.

Theorem interpret_term_spec :
  forall p t R, term_step p t R (interpret_term p t R).
Proof.
  move => p t R.
  case t => [ bb params | c bbT paramsT bbF paramsF /=].
  - constructor.
  - case ((R c) =P 0) => [ H | /eqP /negb_true_iff H].
    + rewrite H. by constructor.
    + rewrite H. constructor => H1. by rewrite H1 in H.
Qed.

(* Interpretation of a single step *)
Definition interpret_step (p: Program) (bb_id: bbid) (pc: nat) (R: RegisterMap) :=
  if p bb_id is Some (_, insts, term) then
    if List.nth_error insts pc is Some inst then
      Some (bb_id, S pc, interpret_inst inst R)
    else
      let (new_bb_id, R') := interpret_term p term R in
      Some (new_bb_id, O, R')
  else
    None.

Theorem interpret_step_spec :
  forall p bb_id pc R state',
    Some state' = interpret_step p bb_id pc R ->
    step p (bb_id, pc, R) state'.
Proof.
  move => p bb_id pc R [[bb_id' pc'] R'].
  rewrite /interpret_step.
  case Hbb: (p bb_id) => [ [[params insts] term] | //].
  case_eq (List.nth_error insts pc) => [inst Hinst [-> -> ->] | Hinst].
  - eapply InstStep.
    + by apply Hbb.
    + by apply Hinst.
    + by apply interpret_inst_spec.
  - move Hnew: (interpret_term p term R) => [new_bb_id R'0] [-> -> ->].
    eapply TermStep.
    + by apply Hbb.
    + by apply Hinst.
    + rewrite -Hnew.
        by apply interpret_term_spec.
Qed.

(* Interpretation of multiple steps *)
Fixpoint interpret_multi_step (fuel: nat) (p: Program) (bb_id: bbid) (pc: nat) (R: RegisterMap) :=
  if fuel is S fuel' then
    if interpret_step p bb_id pc R is Some (bb_id', pc', R') then
      interpret_multi_step fuel' p bb_id' pc' R'
    else
      (bb_id, pc, R)
  else
    (bb_id, pc, R).

Theorem interpret_multi_step_spec:
  forall fuel p bb_id pc R, multi_step p (bb_id, pc, R) (interpret_multi_step fuel p bb_id pc R).
Proof.
  elim => [p bb_id pc R | fuel' Hind p bb_id pc R /=]; [by apply StepRefl | ].
  case_eq (interpret_step p bb_id pc R) => [[[bb_id' pc'] R'] Hstep | Hnostep ]; [ | by constructor ].
  symmetry in Hstep.
  apply interpret_step_spec in Hstep.
  eapply StepTrans.
  - by apply Hstep.
  - by apply Hind.
Qed.

(* The big_step semantics of a list of instructions *)
Inductive inst_list_big_step: (list Inst) -> RegisterMap -> RegisterMap -> Prop :=
| EmptyInstListStep (R: RegisterMap) : inst_list_big_step nil R R
| ConsInstListStep (i: Inst) (l: list Inst) (R R' R'': RegisterMap) :
    inst_step i R R' -> inst_list_big_step l R' R'' ->
    inst_list_big_step (i::l) R R''.

(* The big_step semantics of a basic block *)
Inductive bb_big_step: Program -> BasicBlock -> RegisterMap -> (bbid * RegisterMap) -> Prop :=
| BBBigStep (p: Program) (out_id: bbid) (params: list vid) (il: list Inst) (t: Term) (R R' R'': RegisterMap) :
    inst_list_big_step il R R' -> term_step p t R' (out_id, R'') -> bb_big_step p (params,il,t) R (out_id, R'').

(* The big_step semantics of a program *)
Inductive program_big_step: Program -> ProgramStructure -> (bbid * RegisterMap) -> (bbid * RegisterMap) -> Prop :=
| BBInBigStep (p: Program) (out_id bb_id: bbid) (params: list vid) (insts: list Inst)
            (term: Term) (R R': RegisterMap):
    Some (params, insts, term) = p bb_id ->
    bb_big_step p (params, insts, term) R (out_id, R') ->
    program_big_step p (BB bb_id) (bb_id, R) (out_id, R')
| BBNotInBigStep (p: Program) (in_id bb_id: bbid) (R: RegisterMap):
    bb_id != in_id ->
    program_big_step p (BB bb_id) (in_id, R) (in_id, R)
| DAGBigStep (p: Program) (ps1 ps2: ProgramStructure) (R R' R'': RegisterMap) (id id' id'': bbid):
    program_big_step p ps1 (id, R) (id', R') ->
    program_big_step p ps2 (id', R') (id'', R'') ->
    program_big_step p (DAG ps1 ps2) (id, R) (id'', R'')
| LoopNotInBigStep (p: Program) (header_id: bbid) (body: ProgramStructure) (id: bbid) (R: RegisterMap):
    header_id != id ->
    program_big_step p (Loop header_id body) (id, R) (id, R)
| LoopInBigStep (p: Program) (body: ProgramStructure) (header_id: bbid) (params: list vid) (insts: list Inst)
              (term: Term) (id1 id2 id3: bbid) (R0 R1 R2 R3: RegisterMap):
    Some (params, insts, term) = p header_id ->
    bb_big_step p (params, insts, term) R0 (id1, R1) ->
    program_big_step p body (id1, R1) (id2, R2) ->
    program_big_step p (Loop header_id body) (id2, R2) (id3, R3) ->
    program_big_step p (Loop header_id body) (header_id, R0) (id3, R3).


Fixpoint interpret_inst_list (l: list Inst) (R: RegisterMap) :=
  match l with
  | nil => R
  | inst::l' => interpret_inst_list l' (interpret_inst inst R)
  end.

Theorem interpret_inst_list_spec :
  forall l R, inst_list_big_step l R (interpret_inst_list l R).
Proof.
  elim => [ | i l0 Hind R /= ].
  - constructor.
  - eapply ConsInstListStep.
    + by apply interpret_inst_spec.
    + by [].
Qed.

Definition interpret_bb (p: Program) (bb: BasicBlock) (R: RegisterMap) :=
  interpret_term p bb.2 (interpret_inst_list bb.1.2 R).

Theorem interpret_bb_spec :
  forall p bb R, bb_big_step p bb R (interpret_bb p bb R).
Proof.
  move => p [[params insts] term] R.
  move H: (interpret_bb p (params, insts, term) R) => bbR'.
  case: bbR' H => a b Hbb.
  eapply BBBigStep.
  - apply interpret_inst_list_spec.
  - rewrite -Hbb.
    rewrite /interpret_bb /=.
      by apply interpret_term_spec.
Qed.

Fixpoint interpret_program (fuel: nat) (p: Program) (ps: ProgramStructure) (id: bbid) (R: RegisterMap) :=
  if fuel is S fuel' then
    match ps with
    | BB bb =>
      if id == bb then
        option_map (fun bb => interpret_bb p bb R) (p bb)
      else
        Some (id, R)
    | DAG p1 p2 =>
      if interpret_program fuel' p p1 id R is Some (id', R') then
        interpret_program fuel' p p2 id' R'
      else
        None
    | Loop h body =>
      if id == h then
        if p h is Some (params, insts, term) then
          let (id', R') := interpret_bb p (params, insts, term) R in
          if interpret_program fuel' p body id' R' is Some (id'', R'') then
            interpret_program fuel' p (Loop h body) id'' R''
          else
            None
        else
          None
      else
        Some (id, R)
    end
  else
    None.

Theorem interpret_program_spec :
  forall fuel p sub_p id R id' R',
    Some (id', R') = interpret_program fuel p sub_p id R ->
    program_big_step p sub_p (id, R) (id', R').
Proof.
  elim => [ p sub_p id R id' R' Hsome // | n Hind p sub_p id R id' R'].
  case sub_p => [ header_id body /= | p1 p2 /= HDAG | bb_id].
  - case (id =P header_id); last first.
    + move => /eqP Hne [-> ->].
      apply LoopNotInBigStep.
      by rewrite eq_sym.
    + move => ->.
      case_eq (p header_id) => [[[params insts] term] Hpheader_id | //].
      move Hbb_interpret: (interpret_bb p (params, insts, term) R) => bb_interpret.
      move: bb_interpret Hbb_interpret => [id_bb_interpret R_bb_interpret] Hbb_interpret.
      case_eq (interpret_program n p body id_bb_interpret R_bb_interpret) => [ [p0_id p0R] Hinterpret HSome | //].
      eapply LoopInBigStep with (id1 := id_bb_interpret) (R1 := R_bb_interpret) (id2 := p0_id) (R2 := p0R).
      * symmetry. by apply Hpheader_id.
      * rewrite -Hbb_interpret.
        by apply interpret_bb_spec.
      * auto.
      * auto.
  - case (interpret_program n p p1 id R) eqn:Hp1 in HDAG.
    move: p0 => [p0_id p0_R] in HDAG Hp1.
    eapply DAGBigStep.
    + apply Hind.
      symmetry.
        by apply Hp1.
    + by apply Hind.
    + by [].
  - rewrite /interpret_program /=.
    case (id =P bb_id) => [-> HBB | /eqP Hne [-> ->]].
    move: HBB.
    rewrite /option_map.
    case_eq (p bb_id) => [ [[params insts] term] Hpbb_id [HBB] | //].
    + eapply BBInBigStep.
      * rewrite Hpbb_id.
          by reflexivity.
      * rewrite HBB.
        by apply interpret_bb_spec.
    + apply BBNotInBigStep.
        by rewrite eq_sym.
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

  (* We need to set eval_map transparent to simplify computations *)
  Transparent eval_map.

  Example progstruct_correct :
    structure_sound prog progstruct.
  Proof.
      by [].
  Qed.

  (* Check that the small step semantics and the big_step semantics on a correct
     program structure behave the same *)
  Example interpret_big_step_small_step_same :
    match (interpret_program 10%nat prog progstruct "entry" (_ !-> 0)) with
    | Some (end_id_bs, end_R_bs) =>
      match (interpret_multi_step 1000 prog "entry" O (_ !-> 0)) with
      | (end_id_ss, end_pc_ss, end_R_ss) => end_pc_ss = O /\ end_id_ss = end_id_bs /\ end_R_bs = end_R_ss
      end
    | None => False
    end.
  Proof.
      by [].
  Qed.

End Example.
