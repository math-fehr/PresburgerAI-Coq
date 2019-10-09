From Coq Require Import ssreflect ssrfun ssrbool.
From PolyAI Require Export TotalMap.
From Coq Require Export Bool.Bool Strings.String Numbers.BinNums ZArith.BinInt.

Local Open Scope type_scope.

(*
This is the definition of a loop aware SSA language.
 *)

Definition vid := string.
Definition bbid := string.

(* Every variable has a value, even the non defined ones *)
Definition RegisterMap := total_map Z.

(* The label is the program counter *)
Definition state := total_map RegisterMap.

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
| Br (bb: bbid) (params: list vid)
| BrC (c: vid) (bbT: bbid) (paramsT: list vid)
      (bbF: bbid) (paramsF: list vid).

(* A basic block. Has a identifier, a list of parameters,
 a list of instructions, and a terminator *)
Definition BasicBlock :=
  bbid * (list vid) * (list Inst) * Term.

(* A program is either a basic block, a loop that contains a header and
 a body, or the consecutive execution of two programs *)
Inductive Program :=
| Loop (header: BasicBlock) (body: option Program)
| DAG (p1 p2: Program)
| BB (bb: BasicBlock).

Local Open Scope string_scope.
Local Open Scope list_scope.

(* [affect_variables R [(o1,i1); ... ; (oN, iN)]] will affect i1 to o1, then i2 to o2... *)
Fixpoint affect_variables (R: RegisterMap) (vars inputs: list vid) :=
  match (vars, inputs) with
  | (nil, _) => R
  | (_, nil) => R
  | (var::vars', input::inputs') => affect_variables (var !-> R input; R) vars' inputs'
  end.

(* Get inputs of a basic block given its id,
   and return None if the id is not found *)
Fixpoint get_inputs_error (p: Program) (id: bbid) :=
  match p with
  | Loop (id', inputs, _, _) None =>
    if id =? id' then Some inputs else None
  | Loop (id', inputs, _, _) (Some p') =>
    if id =? id' then Some inputs else get_inputs_error p' id
  | BB (id', inputs, _, _) =>
    if id =? id' then Some inputs else None
  | DAG p1 p2 =>
    match get_inputs_error p1 id with
    | None => get_inputs_error p2 id
    | res => res
    end
  end.

(* Get inputs of a basic block given its id,
   and return nil if the id is not found *)
Definition get_inputs (p: Program) (id: bbid) :=
  match get_inputs_error p id with
  | Some res => res
  | None => nil
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

(* The semantics of a list of instructions *)
Inductive inst_list_denotation: (list Inst) -> RegisterMap -> RegisterMap -> Prop :=
| EmptyInstListStep (R: RegisterMap) : inst_list_denotation nil R R
| ConsInstListStep (i: Inst) (l: list Inst) (R R' R'': RegisterMap) :
    inst_step i R R' -> inst_list_denotation l R' R'' ->
    inst_list_denotation (i::l) R R''.

(* The semantics of a basic block *)
Inductive bb_denotation: Program -> BasicBlock -> RegisterMap -> (bbid * RegisterMap) -> Prop :=
| BBDenot (p: Program) (id out_id: bbid) (params: list vid) (il: list Inst) (t: Term) (R R' R'': RegisterMap) :
    inst_list_denotation il R R' -> term_step p t R' (out_id, R'') -> bb_denotation p (id,params,il,t) R (out_id, R'').

(* The semantics of a program *)
Inductive program_denotation: Program -> Program -> (bbid * RegisterMap) -> (bbid * RegisterMap) -> Prop :=
| BBInDenot (p: Program) (out_id bb_id: bbid) (params: list vid) (insts: list Inst)
            (term: Term) (R R': RegisterMap):
    bb_denotation p (bb_id, params, insts, term) R (out_id, R') ->
    program_denotation p (BB (bb_id, params, insts, term)) (bb_id, R) (out_id, R')
| BBNotInDenot (p: Program) (in_id bb_id: bbid) (params: list vid) (insts: list Inst)
            (term: Term) (R R': RegisterMap):
    ~~(bb_id =? in_id)%string ->
    program_denotation p (BB (bb_id, params, insts, term)) (in_id, R) (in_id, R)
| DAGDenot (p p1 p2: Program) (R R' R'': RegisterMap) (id id' id'': bbid):
    program_denotation p p1 (id, R) (id', R') ->
    program_denotation p p2 (id', R') (id'', R'') ->
    program_denotation p (DAG p1 p2) (id, R) (id'', R'')
| LoopNotInDenot (p: Program) (header_id: bbid) (params: list vid) (insts: list Inst)
                 (term: Term) (body: option Program) (id: bbid) (R: RegisterMap):
    ~~(header_id =? id)%string ->
    program_denotation p (Loop (header_id, params, insts, term) body) (id, R) (id, R)
| LoopSingleInDenot (p: Program) (header_id: bbid) (params: list vid) (insts: list Inst)
                    (term: Term) (id1 id2: bbid) (R0 R1 R2: RegisterMap):
    bb_denotation p (header_id, params, insts, term) R0 (id1, R1) ->
    program_denotation p (Loop (header_id, params, insts, term) None) (id1, R1) (id2, R2) ->
    program_denotation p (Loop (header_id, params, insts, term) None) (header_id, R0) (id2, R2)
| LoopInDenot (p body: Program) (header_id: bbid) (params: list vid) (insts: list Inst)
              (term: Term) (id1 id2 id3: bbid) (R0 R1 R2 R3: RegisterMap):
    bb_denotation p (header_id, params, insts, term) R0 (id1, R1) ->
    program_denotation p body (id1, R1) (id2, R2) ->
    program_denotation p (Loop (header_id, params, insts, term) (Some body)) (id2, R2) (id3, R3) ->
    program_denotation p (Loop (header_id, params, insts, term) (Some body)) (header_id, R0) (id3, R3).


Definition interpret_instruction (inst: Inst) (R: RegisterMap) :=
  match inst with
  | Const v c => (v !-> c; R)
  | BinOp v opc op1 op2 _ _ => (v !-> bin_op_eval opc (R op1) (R op2); R)
  end.

Theorem interpret_instruction_spec :
  forall inst R, inst_step inst R (interpret_instruction inst R).
Proof.
  move => inst R.
  case inst; constructor.
Qed.

Definition interpret_term (p: Program) (t: Term) (R: RegisterMap) :=
  match t with
  | Br bb params => (bb, affect_variables R (get_inputs p bb) params)
  | BrC c bbT paramsT bbF paramsF =>
    if R c =? 0 then
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
  - case (Z.eqb_spec (R c) 0); by constructor.
Qed.

Fixpoint interpret_inst_list (l: list Inst) (R: RegisterMap) :=
  match l with
  | nil => R
  | inst::l' => interpret_inst_list l' (interpret_instruction inst R)
  end.

Theorem interpret_inst_list_spec :
  forall l R, inst_list_denotation l R (interpret_inst_list l R).
Proof.
  elim => [ | i l0 Hind R /= ].
  - constructor.
  - eapply ConsInstListStep.
    + by apply interpret_instruction_spec.
    + by [].
Qed.

Definition interpret_bb (p: Program) (bb: BasicBlock) (R: RegisterMap) :=
  interpret_term p bb.2 (interpret_inst_list bb.1.2 R).

Theorem interpret_bb_spec :
  forall p bb R, bb_denotation p bb R (interpret_bb p bb R).
Proof.
  move => p [[[bb_id params] insts] term] R.
  move H: (interpret_bb p (bb_id, params, insts, term) R) => bbR'.
  case: bbR' H => a b Hbb.
  eapply BBDenot.
  - apply interpret_inst_list_spec.
  - rewrite -Hbb.
    rewrite /interpret_bb /=.
      by apply interpret_term_spec.
Qed.

Fixpoint interpret_program (fuel: nat) (p sub_p: Program) (id: bbid) (R: RegisterMap) :=
  if fuel is S fuel' then
    match sub_p with
    | BB bb =>
      if (id =? bb.1.1.1)%string then
        Some (interpret_bb p bb R)
      else
        Some (id, R)
    | DAG p1 p2 =>
      if interpret_program fuel' p p1 id R is Some (id', R') then
        interpret_program fuel' p p2 id' R'
      else
        None
    | Loop h None =>
      if (id =? h.1.1.1)%string then
        let (id', R') := interpret_bb p h R in
        interpret_program fuel' p (Loop h None) id' R'
      else
        Some (id, R)
    | Loop h (Some body) =>
      if (id =? h.1.1.1)%string then
        let (id', R') := interpret_bb p h R in
        if interpret_program fuel' p body id' R' is Some (id'', R'') then
          interpret_program fuel' p (Loop h (Some body)) id'' R''
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
    program_denotation p sub_p (id, R) (id', R').
Proof.
  elim => [ p sub_p id R id' R' Hsome // | n Hind p sub_p id R id' R'].
  case sub_p => [ [[[header_id params] insts] term] [ body | ] /= | p1 p2 /= HDAG | [[[bb_id params] insts] term]].
  - case_eq (id =? header_id)%string; last first.
    + move => Hne [-> ->].
      apply LoopNotInDenot.
      by rewrite eqb_sym Hne.
    + move => /eqb_eq -> Hinterpret.
      move Hbb_interpret: (interpret_bb p (header_id, params, insts, term) R) => bb_interpret.
      move: bb_interpret => [id_bb_interpret R_bb_interpret] in Hbb_interpret.
      rewrite Hbb_interpret in Hinterpret.
      move: Hinterpret.
      case_eq (interpret_program n p body id_bb_interpret R_bb_interpret) => [ [p0_id p0R] Hinterpret HSome | //].
      eapply LoopInDenot with (id1 := id_bb_interpret) (R1 := R_bb_interpret) (id2 := p0_id) (R2 := p0R).
      * rewrite -Hbb_interpret.
        by apply interpret_bb_spec.
      * by apply Hind.
      * by apply Hind.
  - case_eq (id =? header_id)%string => [ /eqb_eq -> Hinterpret | Hne [-> ->]].
    + move Hp0: (interpret_bb p (header_id, params, insts, term) R) => [p0_id p0_R].
      apply LoopSingleInDenot with (id1 := p0_id) (R1 := p0_R).
      * rewrite -Hp0.
          by apply interpret_bb_spec.
      * rewrite Hp0 in Hinterpret.
          by apply Hind.
    + apply LoopNotInDenot.
      by rewrite eqb_sym Hne.
  - case (interpret_program n p p1 id R) eqn:Hp1 in HDAG.
    move: p0 => [p0_id p0_R] in HDAG Hp1.
    eapply DAGDenot.
    + apply Hind.
      symmetry.
        by apply Hp1.
    + by apply Hind.
    + by [].
  - rewrite /interpret_program /=.
    case (eqb_spec id bb_id)%string => [-> [HBB] | /eqb_spec Hne [-> ->]].
    + apply BBInDenot.
      rewrite HBB.
      apply interpret_bb_spec.
    + apply BBNotInDenot.
      apply R.
        by rewrite eqb_sym.
Qed.

Section Example.

  Definition entry_bb := ("entry", @nil string,
                          (Const "zero" 0)::(Const "one" 1)::nil,
                          (Br "loop" ("zero"::nil))).

  Definition y_ne_x : "y" <> "x".
  Proof.
      by apply eqb_neq.
  Qed.

  Definition y_ne_one : "y" <> "one".
  Proof.
      by apply eqb_neq.
  Qed.

  Definition c_ne_y : "c" <> "y".
  Proof.
      by apply eqb_neq.
  Qed.

  Definition c_ne_one : "c" <> "one".
  Proof.
      by apply eqb_neq.
  Qed.


  Definition loop_header := ("loop", "x"::nil,
                             (BinOp "y" OpAdd "x" "one" y_ne_x y_ne_one)::
                             (BinOp "c" OpLe "y" "one" c_ne_y c_ne_one)::nil,
                             (BrC "c" "loop" ("y"::nil) "exit" ("y"::nil))).

  Definition loop := Loop loop_header None.

  Definition exit_bb := ("exit", "exitvalue"::nil, @nil Inst, (Br "finished" nil)).

  Definition program := DAG (BB entry_bb) (DAG loop (BB exit_bb)).

  Definition input := ("entry", (_ !-> 0)).

  Transparent eval_map.

  Example program_may_terminate :
    forall R, exists R', program_denotation program program ("entry", R) ("finished", R').
  Proof.
    move => R.
    move Hfinal_state: (interpret_program 10%nat program program "entry" R) => final.
    move: (interpret_program_spec 10 program program "entry" R).
    rewrite Hfinal_state.
    move: final Hfinal_state => [[id' R'] Hfinal | // ].
    move => /(_ id' R' (eq_refl _)) Hgoal.
    exists R'.
    compute in Hfinal.
    by move: Hfinal => [-> _].
  Qed.

End Example.
