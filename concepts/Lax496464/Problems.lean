import Lax496464.ParameterizedComplexity
import Mathlib.Data.Nat.Log
import Lax496464.WordEncoding

/-!
---
title: The just-in-time flow shop as a problem on words
type: definition
---
The decision problem: given an encoded instance and a threshold $W$, is there a feasible
set of jobs of total weight at least $W$? As a parameterized problem it is taken with the
number $m$ of machines as its parameter, which is the parameterization of the paper's
fourth corollary.

Four further quantities of an instance appear in the running times of the paper's
algorithms and are defined here as functions of the word: the threshold $W$ itself, the
largest processing time $q_{\max}$, the total preprocessing time $P$, and the width
$\omega$ — the largest number of jobs whose second operations are alive at one instant.

# Formalization notes

The parameter is the word's second entry, so a program obtains it at no cost, and it is
manifestly a function of the input rather than something supplied beside it.

$\omega$ is defined as a maximum over the start times of the jobs rather than over all of
$\mathbb{Z}$. The two agree: the number of jobs alive is a step function that can only
increase at a start time, so its maximum is attained at one. Taking the maximum over a
finite set is what makes the definition a computation rather than a supremum, and it is
also how one would compute it.

Both $\omega$ and $q_{\max}$ are read off the word rather than off the decoded instance,
for the same reason as the parameter: a running time stated in terms of a quantity that
is not a function of the input would not be a statement about a program. They occur in
bounds only; no claim of this submission asks a program to compute them.

The running times below are stated as the paper states them, plus a term `sortCost` for
putting the jobs into earliest-start-time order. The paper's algorithmic sections open by
indexing the jobs that way and count nothing for it; a statement about a program reading
an arbitrary word has to, and one pass of a comparison sort is what it costs. Where the
paper's own bound already dominates $n \log n$ the term is omitted.

A word outside the domain has no meaningful threshold, width or largest processing time.
These functions are total regardless, and nothing is claimed about their values there,
since every statement quantifies over admissible words only.
-/

namespace Lax496464.Problems

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.WordEncoding Lax496464.ParameterizedComplexity

/-- The number of jobs of `x` alive at time `t`, as read off the word. -/
def aliveAt (x : List ℕ) (t : ℤ) : ℕ :=
  ((List.range (jobCount x)).filter
    fun i => decide (start x i ≤ t ∧ t < (due x i : ℤ))).length

/-- The **width** `ω` of `x`: the largest number of jobs alive at one instant. -/
def widthOf (x : List ℕ) : ℕ :=
  ((List.range (jobCount x)).map fun j => aliveAt x (start x j)).foldr max 0

/-- The largest processing time `q_max` declared by `x`. -/
def qmaxOf (x : List ℕ) : ℕ :=
  ((List.range (jobCount x)).map (procTime x)).foldr max 0

/-- `n log n` on a word of length `n`: the cost of putting the jobs of `x` into
earliest-start-time order, which the algorithmic sections of the paper assume has been
done. -/
def sortCost (x : List ℕ) : ℕ := (x.length + 1) * (Nat.log 2 (x.length + 2) + 1)

/-- The total preprocessing time declared by `x`. -/
def preSum (x : List ℕ) : ℕ := ((List.range (jobCount x)).map (preTime x)).sum

/-- A word is a yes-instance when its instance has a feasible set of weight at least its
threshold. -/
def Yes (x : List ℕ) : Prop :=
  ∃ (I : Instance) (W : ℕ), EncodesDecisionInstance x I W ∧ HasWeight I W

/-- **Just-in-time scheduling in a two-stage flexible flow shop**, as a parameterized
problem with the number of machines as its parameter. -/
def byMachines : Problem where
  Domain := DecisionInstances
  Yes := Yes
  param x := machineCount x

end Lax496464.Problems
