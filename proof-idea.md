# LLVM-like language
A program is a partial map of blocks indexed by their names.
A position in the program is a pair `(string, nat)`, where the string is the name of the basic block, and the nat is the position in the basic block.
A concrete state is a partial map associating register names (string) to integers.

We define an small step operational semantic named `step`. `step (pos1, state1) (pos2, state2)` express the fact that we can go from the state `state1` at position `pos1` to `state2` at position `pos2` in one small step.
We define `multi_step`, the reflexive and transitive closure of `step` that contains the identity.

# ProgramStructure
This does not allow us to represent program structures, like loop.
We define program structures as being either a Basic block, a DAG, which is a pair of program structure, that should be executed sequentially,
or a Loop, which is a basic block (the loop header) associated optionally with a program structure (the loop body).

The program structure should follow some rules. For instance, a basic block in the right side of a DAG cannot jump to a basic block from the left side.

# Local overapproximation
We have for every position in the code, a relation between concrete states.
We say that we have a local overapproximation on position `pos1` if for every concrete state `inputs` and `state1` such that `inputs -> state1` is in the relation at position `pos1`,
then, for every `pos2, state2` such that `step (pos1, state1) (pos2, state2)`, then `inputs -> state2` is in the relation at position `pos2`.

# Main proof
What we want to prove, is that at the end of the interpretation of a programstructure, we have a local overapproximation on every position that is in the programstructure.

We prove that by induction on the programstructure.
- The case of the basicblock is fairly simple, since we interpret instruction by instruction, until getting to the terminator.
  Note that the terminator cannot jump back to the begining of the basic block, since the basic block is not a loop (otherwise it would be a Loop construct).
  This is already proven in Coq.
- The case of the DAG is also fairly simple since the second program structure cannot jump back to the first one.
  This is also proven in Coq
- The case of the loop is quite different, and is not yet proven.
  We need first to compute the symbolic analysis. For that, at the entry point (the begining of the header of the loop), we set the relation to `forall inputs, inputs -> inputs`, and keep the previous relation as `R_header`.
  Then, we do by recursion the analysis of the header and then the loop body. It gives for every position `pos` a relation `R_pos`.
  We get the backedge, and compute its transitive closure `R^*`.
  We now wish to prove that if we set the relation in every position `pos` of the loop to `R_pos o R^* o R_header`, then we have a local overapproximation everywhere.
  The local overapproximation should stay true after composition to the right, so for every position that is not the loop header, this can be proven fairly easily.
  For the loop header, we use the fact that we computed an overapproximation of the transitive closure to prove that we have a local overapproximation.
  One important point is that the overapproximation we computed is closed by application of the relation. (this is ensured by ISL).

If we have the previous theorem, and also that `inputs -> inputs` is in the entry position of the program, then we have the wanted property: `multi_step (entry_pos, inputs) (pos, state)` implies `inputs -> state` is in the realtion at position `pos`, where `multi_step` is restrained to positions that are in the program structure.
