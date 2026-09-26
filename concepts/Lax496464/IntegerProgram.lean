import Lax496464.Conditions
import Lax496464.EstOrder
import Lax496464.ProperInstances
import Mathlib.Data.Matrix.Mul

/-!
---
title: The integer program of Section 6.2
type: definition
---
When all preprocessing times are equal to $p$, a set of jobs is feasible exactly when it
satisfies two families of linear inequalities in its own indicator vector
$\mathbf{x} \in \{0,1\}^n$:
$$\sum_{i \le j} x_i \le \lfloor s_j / p \rfloor \quad (6), \qquad
  \sum_{i \text{ alive at } s_j} x_i \le m \quad (7),$$
one of each per job $j$. The first is Condition 1 — with equal preprocessing times, the
time the first stage has spent is the number of jobs it has run — and the second is
Condition 2 in its depth form, tested at the start times, where the number of jobs alive
can only increase.

Maximizing $\sum_j w_j x_j$ subject to these is therefore the problem itself, written as
an integer program with $2n$ constraints and $n$ variables.

# Formalization notes

The constraint matrix is indexed by a sum type, one copy of the jobs for each family, so
that the two families can be told apart without an arithmetic encoding of the row index.
Its entries are integers rather than naturals, because the inequalities are, and because
total unimodularity is a statement about an integer matrix.

Constraint (6) is imposed for *every* job, selected or not. That is what the program
says, and it makes the correspondence to feasible sets fail on an instance with a
negative start time: the row of such a job is unsatisfiable even at $\mathbf{x} =
\mathbf{0}$, while the empty set is feasible. Such a job can never be completed just in
time and would be deleted in advance, which is presumably what the paper intends; since
the model here admits negative start times, the correspondence carries the hypothesis
that they are nonnegative.

Properness is *not* needed for the correspondence. It is needed only for the consecutive
ones property of the second family, which is what the fifth lemma is about.
-/

namespace Lax496464.IntegerProgram

open Lax496464.FlowShop Lax496464.FlowShop.Instance

variable (I : Instance)

/-- The constraint matrix: the rows `inl j` are the prefix sums of constraint (6), the
rows `inr j` the jobs alive at `s j` of constraint (7). -/
def matrix : Matrix (I.Job ⊕ I.Job) I.Job ℤ
  | Sum.inl j, i => if i ≤ j then 1 else 0
  | Sum.inr j, i => if s i ≤ s j ∧ s j < (I.d i : ℤ) then 1 else 0

/-- The right-hand sides: `⌊s j / p⌋` for (6) and `m` for (7). -/
def rhs (p : ℕ) : I.Job ⊕ I.Job → ℤ
  | Sum.inl j => s j / p
  | Sum.inr _ => I.machines

/-- The `0/1` vector of a set of jobs. -/
def indicator (Z : Finset I.Job) : I.Job → ℤ := fun i => if i ∈ Z then 1 else 0

end Lax496464.IntegerProgram
