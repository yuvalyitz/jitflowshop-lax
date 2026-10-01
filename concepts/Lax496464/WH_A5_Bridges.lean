import Lax496464.WH_A2_FptReductions
import Lax759944.TuringPolytime

/-!
---
title: Polynomial-time and strict reductions are fpt-reductions
type: theorem
---
Most reductions in parameterized complexity are computable in polynomial time, and many are
already proved in the archive in one of the following forms. Each yields an fpt-reduction.

1. **Runs of a program.** A program that halts with the correct output within a fixed-parameter
   bound $B$ at every word length from $B$ on, and writes numbers of at most $B$ bits, computes the
   function in fixed-parameter time. This is the form in which a program verified in the archive's
   IMP+ language arrives, run on the tape `x.length :: x`.
2. **Polynomial time on the word RAM.** On the set of all words, polynomial time in the sense of
   `WH_A1_FptTime` is `Lax759944.RamPolytime.RamPolytime`. A polynomial-time reduction whose parameter
   is bounded by a computable function of the old one is an fpt-reduction.
3. **Polynomial time on a Turing machine** (`Lax759944.TuringPolytime.TuringPolytime`), by the
   archive's equivalence of the two machine models.
4. **The archive's strict fpt-reductions** (`Lax888481.ParameterizedComplexity.IsFptReduction`,
   time $c\,g(k)\,(|x|+1)$ on the tape $x$), when $g$ and $h$ are computable and the output entries
   have fixed-parameter bit length; likewise the archive's strict fpt-algorithms.

# Formalization notes

**Output entries in the strict case.** The strict definition bounds the running time but not the
size of the numbers written: a program that repeatedly squares a number writes, in $m$ steps, a
number of $2^m$ bits. Such an output cannot be read by a further reduction in fixed-parameter time.
The hypothesis `hout` excludes this; it holds for every reduction whose output numbers are
polynomially bounded in its input numbers.

**Tapes.** The strict notion gives the program the word $x$, the polynomial-time notions the word
`x.length :: x`; a program for one tape is converted into one for the other with constant
overhead.
-/

namespace Lax496464.WH_A5_Bridges

open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax759944.RamPolytime Lax759944.TuringPolytime
open Lax888481.ParameterizedComplexity (Problem Fits Decides)
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions

/-- On all words, polynomial time is the archive's polynomial time on the word RAM. -/
axiom polyTimeOn_univ_iff (F : List ℕ → List ℕ) : PolyTimeOn Set.univ F ↔ RamPolytime F

/-- **From runs on the machine.** A program that, on the tape `x.length :: x` of every word `x` of
`D`, halts with output `F x` within `B = f(κ x) · (|x| + 1)^d` steps at every word length `w ≥ B`,
writing only numbers below `2 ^ B`, computes `F` in fixed-parameter time. -/
axiom fptTimeOn_of_runsTo {D : Set (List ℕ)} {κ : List ℕ → ℕ} {F : List ℕ → List ℕ}
    {p : Program} {f : ℕ → ℕ} {d : ℕ} (hf : Computable f)
    (hrun : ∀ x ∈ D, ∀ w : ℕ, fptBound f d (κ x) (bitSize x) ≤ w →
      ∃ t ≤ fptBound f d (κ x) (bitSize x), RunsTo w p (x.length :: x) (F x) t)
    (hout : ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ fptBound f d (κ x) (bitSize x)) :
    FptTimeOn D κ F

/-- **From runs on the machine**, polynomial version: the same with the bound `c · (|x| + 1)^d`. -/
axiom polyTimeOn_of_runsTo {D : Set (List ℕ)} {F : List ℕ → List ℕ} {p : Program} {c d : ℕ}
    (hrun : ∀ x ∈ D, ∀ w : ℕ, c * (bitSize x + 1) ^ d ≤ w →
      ∃ t ≤ c * (bitSize x + 1) ^ d, RunsTo w p (x.length :: x) (F x) t)
    (hout : ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ (c * (bitSize x + 1) ^ d)) :
    PolyTimeOn D F

/-- A polynomial-time computation on the word RAM is polynomial time on every set of inputs. -/
axiom polyTimeOn_of_ramPolytime {F : List ℕ → List ℕ} (D : Set (List ℕ)) :
    RamPolytime F → PolyTimeOn D F

/-- A polynomial-time computation on a Turing machine is polynomial time on every set of inputs. -/
axiom polyTimeOn_of_turingPolytime {F : List ℕ → List ℕ} (D : Set (List ℕ)) :
    TuringPolytime F → PolyTimeOn D F

/-- **A polynomial-time reduction with a computably bounded parameter is an fpt-reduction.** -/
axiom fptReduces_of_polyTime {P Q : Problem} {R : List ℕ → List ℕ} :
    IsReduction P Q R → ParamBounded P Q R → PolyTimeOn P.Domain R → P ≤ᶠᵖᵗ Q

/-- A computation in the archive's strict linear fixed-parameter time, with a computable time factor
and outputs of fixed-parameter bit length, is a fixed-parameter computation. -/
axiom fptTimeOn_of_strict {D : Set (List ℕ)} {κ : List ℕ → ℕ} {F : List ℕ → List ℕ}
    {prog : Program} {c : ℕ} {g : ℕ → ℕ} (hg : Computable g)
    (htime : ∀ w : ℕ, ComputesInTime w prog {x | x ∈ D ∧ Fits c w x ∧ Fits c w (F x)} F
      fun x => c * g (κ x) * (x.length + 1))
    (hout : ∃ (e : ℕ → ℕ) (d : ℕ), Computable e ∧
      ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ (e (κ x) * (bitSize x + 1) ^ d)) :
    FptTimeOn D κ F

/-- **A strict fpt-reduction of the archive** with computable functions and outputs of
fixed-parameter bit length **is an fpt-reduction.** -/
axiom fptReduces_of_strict {P Q : Problem} {R : List ℕ → List ℕ} {prog : Program} {c : ℕ}
    {g h : ℕ → ℕ} (hr : Lax888481.ParameterizedComplexity.IsFptReduction P Q R prog c g h)
    (hg : Computable g) (hh : Computable h)
    (hout : ∃ (e : ℕ → ℕ) (d : ℕ), Computable e ∧
      ∀ x ∈ P.Domain, ∀ v ∈ R x, v < 2 ^ (e (P.param x) * (bitSize x + 1) ^ d)) :
    P ≤ᶠᵖᵗ Q

/-- **A strict fpt-algorithm of the archive** with a computable time factor puts a parameterized
problem into FPT. -/
axiom mem_FPT_of_decides {P : Problem} {prog : Program} {c : ℕ} {g : ℕ → ℕ}
    (hP : IsParameterized P) (hg : Computable g) (hd : Decides P prog c g) : P ∈ FPT

end Lax496464.WH_A5_Bridges
