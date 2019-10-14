From Coq Require Import ssreflect ssrfun ssrbool.
Local Set Warnings "-notation-overridden".
From PolyAI Require Import TotalMap ssrZ.
From Coq Require Export Bool.Bool Strings.String Numbers.BinNums.
Require Import Coq.Arith.PeanoNat.


Local Open Scope type_scope.

(*
This is the definition of a SSA language.
A program is a list of SSA instructions.
The label of an instruction is its position in the list.
There is arithmetic instructions, conditionals and non conditionals
branching instructions.
*)

Definition variable := string.

Definition label := nat.

(* Every variable has a value, even the non defined ones *)
Definition RegisterMap := @total_map string_eqType Z.

(* The label is the program counter *)
Definition state := RegisterMap * label.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope Z_scope.

(* Basics binary arithmetic opcodes *)
Inductive BinArithOpCode :=
| OpAdd
| OpMul
| OpLe.

(* The evaluation of a binary operation *)
Definition bin_op_eval (op : BinArithOpCode) (v1 v2 : Z) :=
  match op with
  | OpAdd => v1 + v2
  | OpMul => v1 * v2
  | OpLe => if v1 <=? v2 then 1 else 0
  end.

(* An SSA instruction *)
Inductive Instruction :=
| Const (v: variable) (c: Z)
| BinOp (v: variable) (b: BinArithOpCode) (op1 op2: variable): v != op1 -> v != op2 -> Instruction
| Br (l: label) (params: list (variable * variable))
| BrC (c: variable) (l1: label) (params1: list (variable * variable))
      (l2: label) (params2: list (variable * variable)).

(* An SSA program *)
Definition Program :=
  list Instruction.

(* [affect_variables R [(o1,i1); ... ; (oN, iN)]] will affect i1 to o1, then i2 to o2... *)
Fixpoint affect_variables (R: RegisterMap) (vars: list (variable * variable)) :=
  match vars with
  | nil => R
  | (param, value)::vars' => affect_variables (param !-> R value; R) vars'
  end.

(* Execute an instruction *)
Definition ssa_step (inst : Instruction) (R : RegisterMap) (l : label) :=
  match inst with
  | Const v x => (v !-> x; R, Nat.add l 1)
  | BinOp v op x1 x2 _ _ => (v !-> bin_op_eval op (R x1) (R x2) ; R, Nat.add l 1)
  | Br l' params => (affect_variables R params, l')
  | BrC c l1 params1 l2 params2 =>
    if R c == 0 then
      (affect_variables R params2, l2)
    else
      (affect_variables R params1, l1)
  end.

Local Open Scope nat_scope.

(* Small step semantics *)
Inductive step : Program -> state -> state -> Prop :=
| SingleStep (p: Program) (R R': RegisterMap) (l l': label) (s: Instruction):
    l < List.length p ->
    l' < List.length p ->
    Some s = List.nth_error p l ->
    (R', l') = ssa_step s R l ->
    step p (R, l) (R', l').

(* The transitive closure of small steps semantics *)
Inductive multi_step : Program -> state -> state -> Prop :=
| MultiRefl : forall p R l, multi_step p (R, l) (R, l)
| MultiStep : forall p s s' s'', multi_step p s s' -> step p s' s'' -> multi_step p s s''.

(* The reachable states, starting from label 0 on an arbitrary register map *)
Inductive reachable_states : Program -> state -> Prop :=
| Reachable : forall p R s', multi_step p (R, 0) s' -> reachable_states p s'.
