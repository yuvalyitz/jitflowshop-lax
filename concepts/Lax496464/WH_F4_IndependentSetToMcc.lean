import Lax496464.WH_F2_MccConstruction
import Lax496464.WH_A2_FptReductions
import Lax762056.GraphProblems
import Lax759944.RamPolytime
import Lax888481.PolynomialReduction

/-!
---
title: Independent Set reduces to Multicoloured Clique
type: theorem
---
**Independent Set, parameterized by $k$, fpt-reduces to Multicoloured Clique, parameterized by the
number of colours** [FHRV09, Lemma 1], [CFK+15, Theorem 13.7]. The reduction `reduce` of
`WH_F2_MccConstruction` maps an instance with parameter $k$ to an instance with $k$ colours. It is
computable in time $c\,(k+1)^2\,(|x|+1)$ on the words of instances and in polynomial time on all
words, so it is also a polynomial-time many-one reduction.

**Correctness.** An independent set $\{v_0, \dots, v_{k-1}\}$ of $G$ gives the multicoloured
clique $\{(c, v_c) : c < k\}$: its vertices have distinct colours, copy distinct vertices, and copy
non-adjacent ones. Conversely, a multicoloured clique $\{(c, v_c) : c < k\}$ yields $k$ distinct
vertices $v_c$, pairwise non-adjacent in $G$.

**Running time.** The multicoloured graph has $kn$ vertices, and the program tests each of the
$k^2 n^2$ ordered pairs; the word of the instance has at least $n^2$ entries.

The statements are:

| statement | content |
|---|---|
| `construct_correct` | correctness of the construction on graphs |
| `word_encodes` | the word of the construction encodes the multicoloured graph |
| `reduce_word`, `reduce_off_domain` | `reduce` on the words of instances and on other words |
| `reduce_maps_domain`, `reduce_correct` | instances go to instances, yes to yes and no to no |
| `parameter_preserved` | the parameter is preserved, $k' = k$ |
| `reduce_fptTime` | time $c\,(k+1)^2\,(\lvert x\rvert+1)$ on the word RAM |
| `independentSet_isFptReduction`, `independentSet_fptReduces_mcc` | a strict fpt-reduction of `Lax888481` |
| `reduce_polyTime`, `independentSet_polyReduces_mcc` | polynomial time on every word; a polynomial-time reduction |
| `independentSet_le_mcc` | an fpt-reduction in the sense of `WH_A2_FptReductions` |

# Formalization notes

**Independent Set** is `WH_F1_IndependentSetMatrix.problem`, the archive's `Lax762056` Independent
Set on adjacency-matrix words; its threshold is a lower bound, and a set of at least $k$ independent
vertices contains one of exactly $k$. For $k = 0$ both sides hold, the empty choice being a
multicoloured clique with no colours.

**Words.** `word_encodes` states that the word of the construction satisfies the compressed sparse
row format of `Lax888481.MulticolouredClique`, with strictly increasing adjacency lists and the
colours of the construction. The parameter of a Multicoloured Clique word is its last entry, which
is $k$.

**Two notions of fpt-reduction.** `independentSet_isFptReduction` is the strict fpt-reduction of
`Lax888481.ParameterizedComplexity`, with time $c\,g(k)\,(|x|+1)$ for $g(k) = (k+1)^2$ and new
parameter at most $h(k) = k$. `independentSet_le_mcc` is the fpt-reduction of `WH_A2_FptReductions`.

**Polynomial time.** `reduce_polyTime` is `Lax759944.RamPolytime.RamPolytime` on every word,
malformed words included; the program first checks in one pass that the word is the encoding of an
instance: a run of ones and a zero, a symmetric $0/1$ matrix with zero diagonal whose side is the
length of that run, and a run of ones and a zero.
-/

namespace Lax496464.WH_F4_IndependentSetToMcc

open Lax762056.GraphEncoding (Instance)

-- The construction

/-- **Correctness of the construction.** `G` has an independent set of size at least `k` if
and only if the multicoloured graph has a multicoloured clique. -/
axiom construct_correct (I : Instance) :
    Lax762056.GraphProblems.IndependentSet I ↔
      (WH_F2_MccConstruction.construct I).HasMulticolouredClique

/-- **The word encodes the construction.** -/
axiom word_encodes (I : Instance) :
    Lax888481.MulticolouredClique.EncodesInstance (WH_F2_MccConstruction.word I)
      (WH_F2_MccConstruction.construct I)

-- The reduction on words

section Words

open Lax496464.WH_F1_IndependentSetMatrix (problem)
open Lax496464.WH_F2_MccConstruction (reduce)

/-- On the word of an instance, `reduce` is the word of the construction. -/
axiom reduce_word (I : Instance) :
    reduce (WH_F1_IndependentSetMatrix.word I) = WH_F2_MccConstruction.word I

/-- On a word that presents no instance, `reduce` is the empty word. -/
axiom reduce_off_domain (x : List ℕ) (hx : x ∉ problem.Domain) : reduce x = []

/-- **Instances go to instances.** -/
axiom reduce_maps_domain :
    ∀ x ∈ problem.Domain, reduce x ∈ Lax888481.MulticolouredClique.problem.Domain

/-- **The answer is preserved.** -/
axiom reduce_correct :
    ∀ x ∈ problem.Domain, (problem.Yes x ↔ Lax888481.MulticolouredClique.problem.Yes (reduce x))

/-- **The parameter is preserved**: `k' = k`. -/
axiom parameter_preserved :
    ∀ x ∈ problem.Domain,
      Lax888481.MulticolouredClique.problem.param (reduce x) = problem.param x

end Words

-- Running time and the reductions

section Time

open Lax808846.Ram Lax808846.RamComputes Lax888481.ParameterizedComplexity
open Lax496464.WH_F1_IndependentSetMatrix (problem)
open Lax496464.WH_F2_MccConstruction (reduce)

/-- **Running time in the parameter `k`.** At every word length, on every word of an instance whose
image fits, one program computes `reduce` within `c * (k + 1) ^ 2 * (|x| + 1)` instructions. -/
axiom reduce_fptTime :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ problem.Domain ∧ Fits c w x ∧ Fits c w (reduce x)}
        reduce (fun x => c * (problem.param x + 1) ^ 2 * (x.length + 1))

/-- **The strict fpt-reduction**, with `g k = (k + 1) ^ 2` and `h k = k`. -/
axiom independentSet_isFptReduction :
    ∃ (prog : Lax808846.Ram.Program) (c : ℕ),
      Lax888481.ParameterizedComplexity.IsFptReduction problem
        Lax888481.MulticolouredClique.problem reduce prog c (fun k => (k + 1) ^ 2) (fun k => k)

/-- **Independent Set strictly fpt-reduces to Multicoloured Clique.** -/
axiom independentSet_fptReduces_mcc :
    Lax888481.ParameterizedComplexity.FptReduces problem Lax888481.MulticolouredClique.problem

/-- **Polynomial running time**, on every word. -/
axiom reduce_polyTime : Lax759944.RamPolytime.RamPolytime reduce

/-- **Independent Set reduces to Multicoloured Clique in polynomial time.** -/
axiom independentSet_polyReduces_mcc :
    Lax888481.PolynomialReduction.PolyReduces {x | problem.Yes x}
      {x | Lax888481.MulticolouredClique.problem.Yes x}

end Time

-- The fpt-reduction of the library

section Library

open Lax496464.WH_A2_FptReductions

/-- **`p-Independent-Set ≤fpt Multicoloured Clique`**, on adjacency-matrix words. -/
axiom independentSet_le_mcc :
    WH_F1_IndependentSetMatrix.problem ≤ᶠᵖᵗ Lax888481.MulticolouredClique.problem

end Library

end Lax496464.WH_F4_IndependentSetToMcc
