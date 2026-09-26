import Lax496464.FlowShop

/-!
---
title: Word encoding of an instance
type: definition
---
An instance is handed to a word random access machine as a word of numbers: the number
$n$ of jobs, the number $m$ of machines, then the $n$ preprocessing times, the $n$
processing times, the $n$ due dates and the $n$ weights, in that order. A decision
instance appends the threshold $W$ as a final entry.

# Formalization notes

This is the point at which magnitudes stop being free. The preprocessing times,
processing times, due dates and weights are entries of the word, so a claim about a
program reading it has to say that they are words — which the fitting conditions state,
once, as an explicit inequality against $2^w$. A size measure counting only the number of
jobs would make the due dates of a reduction's output invisible, and a running time
stated against it would not be a claim about anything a machine does.

Cells are read with `List.getD`, which returns $0$ outside the word. The length condition
pins the word down completely, so the default is never reached at a position the other
conditions constrain, and a word of the right length determines its instance.

The threshold is appended last, so that the instance block sits at the same offsets
whether or not a threshold follows it, and the split of the word into its two parts is
determined by the word rather than chosen.

Unlike the instance itself, the word carries no start times: $s_j = d_j - q_j$ is
computed from the word, one subtraction per job, and appears in the predicates below
rather than in the format.
-/

namespace Lax496464.WordEncoding

open Lax496464.FlowShop Lax496464.FlowShop.Instance

/-- The number of jobs declared by a word: its first entry. -/
def jobCount (x : List ℕ) : ℕ := x.getD 0 0

/-- The number of machines declared by a word: its second entry. -/
def machineCount (x : List ℕ) : ℕ := x.getD 1 0

/-- The preprocessing time of job `j`, from the block following the two header
entries. -/
def preTime (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + j) 0

/-- The processing time of job `j`, from the block following the preprocessing times. -/
def procTime (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + jobCount x + j) 0

/-- The due date of job `j`, from the block following the processing times. -/
def due (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + 2 * jobCount x + j) 0

/-- The weight of job `j`, from the block following the due dates. -/
def wt (x : List ℕ) (j : ℕ) : ℕ := x.getD (2 + 3 * jobCount x + j) 0

/-- The threshold of a decision instance: the entry following the four blocks. -/
def threshold (x : List ℕ) : ℕ := x.getD (2 + 4 * jobCount x) 0

/-- The start time `s j = d j - q j` of job `j`, as read off the word. -/
def start (x : List ℕ) (j : ℕ) : ℤ := (due x j : ℤ) - procTime x j

/-- The word `x` encodes the instance `I`. -/
structure EncodesInstance (x : List ℕ) (I : Instance) : Prop where
  /-- The word declares `I`'s jobs. -/
  jobCount_eq : jobCount x = I.jobs
  /-- The word declares `I`'s machines. -/
  machineCount_eq : machineCount x = I.machines
  /-- The word is the two header entries followed by four blocks of one number per job. -/
  length_eq : x.length = 2 + 4 * I.jobs
  /-- The preprocessing times are `I`'s. -/
  preTime_eq : ∀ j : I.Job, preTime x j = I.p j
  /-- The processing times are `I`'s. -/
  procTime_eq : ∀ j : I.Job, procTime x j = I.q j
  /-- The due dates are `I`'s. -/
  due_eq : ∀ j : I.Job, due x j = I.d j
  /-- The weights are `I`'s. -/
  wt_eq : ∀ j : I.Job, wt x j = I.w j

/-- The word `x` presents the instance `I` together with the threshold `W`: an instance
block followed by the single entry `W`. -/
def EncodesDecisionInstance (x : List ℕ) (I : Instance) (W : ℕ) : Prop :=
  ∃ y, x = y ++ [W] ∧ EncodesInstance y I

/-- The words that encode an instance, with no threshold. -/
def Instances : Set (List ℕ) := {x | ∃ I, EncodesInstance x I}

/-- The words that encode a decision instance. -/
def DecisionInstances : Set (List ℕ) := {x | ∃ I W, EncodesDecisionInstance x I W}

end Lax496464.WordEncoding
