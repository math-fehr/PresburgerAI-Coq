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
| ConstInstListStep (i: Inst) (l: list Inst) (R R' R'': RegisterMap) :
    inst_step i R R' -> inst_list_denotation l R' R'' ->
    inst_list_denotation (i::l) R R''.

(* The semantics of a basic block *)
Inductive bb_denotation: Program -> BasicBlock -> RegisterMap -> (bbid * RegisterMap) -> Prop :=
| BBDenot (p: Program) (id out_id: bbid) (params: list vid) (il: list Inst) (t: Term) (R R' R'': RegisterMap) :
    inst_list_denotation il R R' -> term_step p t R' (out_id, R'') -> bb_denotation p (id,params,il,t) R (out_id, R'').

(* The semantics of a program *)
Inductive program_denotation: Program -> Program -> (bbid * RegisterMap) -> (bbid * RegisterMap) -> Prop :=
| BBInDenot (p: Program) (out_id: bbid) (bb: BasicBlock) (R R': RegisterMap):
    bb_denotation p bb R (out_id, R') ->
    program_denotation p (BB bb) (bb.1.1.1, R) (out_id, R')
| BBNotInDenot (p: Program) (in_id: bbid) (bb: BasicBlock) (R: RegisterMap):
    ~~(bb.1.1.1 =? in_id)%string ->
    program_denotation p (BB bb) (in_id, R) (in_id, R)
| DAGDenot (p p1 p2: Program) (R R' R'': RegisterMap) (id id' id'': bbid):
    program_denotation p p1 (id, R) (id', R') ->
    program_denotation p p2 (id', R') (id'', R'') ->
    program_denotation p (DAG p1 p2) (id, R) (id'', R'')
| LoopNotInDenot (p: Program) (header: BasicBlock) (body: option Program) (id: bbid) (R: RegisterMap):
    ~~(header.1.1.1 =? id)%string ->
    program_denotation p (Loop header body) (id, R) (id, R)
| LoopSingleInDenot (p: Program) (header: BasicBlock) (id1 id2: bbid) (R0 R1 R2: RegisterMap):
    bb_denotation p header R0 (id1, R1) ->
    program_denotation p (Loop header None) (id1, R1) (id2, R2) ->
    program_denotation p (Loop header None) (header.1.1.1, R0) (id2, R2)
| LoopInDenot (p body: Program) (header: BasicBlock) (id1 id2 id3: bbid) (R0 R1 R2 R3: RegisterMap):
    bb_denotation p header R0 (id1, R1) ->
    program_denotation p body (id1, R1) (id2, R2) ->
    program_denotation p (Loop header (Some body)) (id2, R2) (id3, R3) ->
    program_denotation p (Loop header (Some body)) (header.1.1.1, R0) (id3, R3).
