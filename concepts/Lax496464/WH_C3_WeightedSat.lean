import Lax888481.ParameterizedComplexity
import Lax429075.CNF

/-!
---
title: Weighted Satisfiability of CNF Formulas
type: definition
---
An assignment to the variables of a propositional formula $\alpha$ has *weight* $k$ if it sets
exactly $k$ of them to true, and $\alpha$ is *$k$-satisfiable* if some assignment of weight $k$
satisfies it [FG06, Section 4.1].

**$p$-WSat($\Gamma$)** for a class $\Gamma$ of formulas. *Instance:* $\alpha \in \Gamma$ and
$k \in \mathbb N$. *Parameter:* $k$. *Question:* is $\alpha$ $k$-satisfiable?

The classes used are the CNF formulas with clauses of at most $d$ literals, **$d$-CNF**
($\Gamma_{1,d}$ in [FG06]), and the **monotone** CNF formulas, all of whose literals are positive
($\Gamma^+_{2,1}$).

# Formalization Notes

A CNF formula is the archive's `Lax429075.CNF.Formula`, a list of clauses, each a list of literals
with a variable index and a sign. The variables of $\alpha$ are the indices occurring in it, and an
assignment of weight $k$ is a set of $k$ of them, the variables set to true.

The word of an instance lists the number of clauses, then each clause as its length followed by its
literals — $X_i$ written $2i$ and $\neg X_i$ written $2i+1$ — and finally $k$. The class $\Gamma$
restricts the instances only.
-/

namespace Lax496464.WH_C3_WeightedSat

open Lax429075.CNF
open Lax888481.ParameterizedComplexity (Problem)

/-- The variables that occur in a formula. -/
def vars (α : Formula) : Finset ℕ := (α.flatMap fun C => C.map Literal.index).toFinset

/-- `α` is **`k`-satisfiable**: setting some `k` of its variables to true, and the others to false,
satisfies it. -/
def WeightSat (α : Formula) (k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ vars α ∧ S.card = k ∧ eval α (fun i => decide (i ∈ S)) = true

/-- `α ∈ d-CNF`: every clause has at most `d` literals. -/
def IsDCNF (d : ℕ) (α : Formula) : Prop := ∀ C ∈ α, C.length ≤ d

/-- `α` is monotone: every literal is positive. -/
def IsMonotone (α : Formula) : Prop := ∀ C ∈ α, ∀ l ∈ C, l.positive = true

/-- The number standing for a literal: `2i` for `X_i`, `2i + 1` for `¬X_i`. -/
def litCode (l : Literal) : ℕ := 2 * l.index + if l.positive then 0 else 1

/-- The word of a formula: the number of clauses, then each clause as its length and its literals. -/
def encode (α : Formula) : List ℕ := α.length :: α.flatMap fun C => C.length :: C.map litCode

/-- **`p-WSat(Γ)`**, weighted satisfiability for the class `Γ` of CNF formulas. -/
def pWSat (Γ : Set Formula) : Problem where
  Domain := {x | ∃ α ∈ Γ, ∃ k, x = encode α ++ [k]}
  Yes x := ∃ α k, x = encode α ++ [k] ∧ WeightSat α k
  param x := x.getLast?.getD 0

end Lax496464.WH_C3_WeightedSat
