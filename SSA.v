Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import PolyAI.TotalMap.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.ZArith.BinInt.


Local Open Scope type_scope.

(*
This is the definition of a SSA language.
A program is a list of SSA instructions.
The label of an instruction is its position in the list.
There is arithmetic instructions, and non conditionals and conditionals
branching instructions.
*)

Definition variable := string.
Definition label := nat.

(* Every variable has a value, even the non defined ones *)
Definition RegisterMap := total_map Z.
(* The label is the program counter *)
Definition state := RegisterMap * label.

Local Open Scope string_scope.

(* Basics binary arithmetic opcodes *)
Inductive BinArithOpCode :=
| OpAdd
| OpMul
| OpLe.

Local Open Scope Z_scope.

(* The evaluation of a binary operation *)
Definition bin_op_eval (R : RegisterMap) (op : BinArithOpCode) (v1 v2 : variable) :=
  match op with
  | OpAdd => (R v1) + (R v2)
  | OpMul => (R v1) * (R v2)
  | OpLe => if (R v1) <=? (R v2) then 1 else 0
  end.

Local Open Scope nat_scope.

(* An SSA instruction *)
Inductive SSA :=
| Const (v: variable) (c: Z)
| BinOp (v: variable) (b: BinArithOpCode) (op1 op2: variable): v <> op1 -> v <> op2 -> SSA.

(* An SSA program *)
Definition Program :=
  list SSA.

(* Do one step given an instruction *)
Definition ssa_step (inst : SSA) (R : RegisterMap) (l : label) :=
  match inst with
  | Const v x => (t_update R v x, l + 1)
  | BinOp v op x1 x2 _ _ => (t_update R v (bin_op_eval R op x1 x2), l + 1)
  end.

(* Small step semantics *)
Inductive step : Program -> state -> state -> Prop :=
| SingleStep (p: Program) (R R': RegisterMap) (l l': label) (s: SSA):
    l < List.length p ->
    l' < List.length p ->
    Some s = List.nth_error p l ->
    (R', l') = ssa_step s R l ->
    step p (R, l) (R', l').

(* The transitive closure of small steps semantics *)
Inductive multi_step : Program -> state -> state -> Prop :=
| MultiRefl : forall p R l, multi_step p (R, l) (R, l)
| MultiStep : forall p s s' s'', multi_step p s s' -> step p s' s'' -> multi_step p s s''.

(* The reachable states *)
Inductive reachable_states : Program -> state -> Prop :=
| Reachable : forall p R s', multi_step p (R, 0) s' -> reachable_states p s'.
