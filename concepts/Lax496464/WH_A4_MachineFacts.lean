import Lax496464.WH_A1_FptTime

/-!
---
title: Fixed-Parameter Computations Compose
type: theorem
---
The identity is computable in fixed-parameter time, and fixed-parameter computations compose: if
$F$ is computable in time $f(\kappa(x))\cdot|x|^{O(1)}$ on $D$, maps $D$ into $E$ and increases the
parameter by at most a computable function, and $G$ is computable in time
$f'(\kappa'(y))\cdot|y|^{O(1)}$ on $E$, then $G \circ F$ is computable in time
$f''(\kappa(x))\cdot|x|^{O(1)}$ on $D$ for a computable $f''$. Restricting the set of inputs, or
changing the function outside it, preserves the bound.

Two facts about the input size, from which running-time bounds are usually derived, complete the
list: a word has at most as many entries as bits, and each entry is below $2^{|x|}$.

These are the only facts about programs that the calculus of reductions (`WH_A3_ReductionCalculus`)
uses.

# Formalization Notes

The composite runs the first program, keeps its output in memory, and runs the second program on
it. The output of the first program has at most $B_1 = f(\kappa(x))(|x|+1)^d$ entries of at most
$B_1$ bits each, so its bit size is at most $B_1(B_1+1)$, and the second program runs within
$f'(\kappa'(F x))\,(B_1(B_1+1)+1)^{d'}$ steps. Since $\kappa'(F x) \le g(\kappa(x))$ and $f'$ may be
replaced by the computable nondecreasing function $m \mapsto \sum_{i\le m} f'(i)$, this is again a
bound $f''(\kappa(x))\,(|x|+1)^{d''}$ with $f''$ computable.
-/

namespace Lax496464.WH_A4_MachineFacts

open Lax496464.WH_A1_FptTime Lax759944.BinaryWordEncoding

/-- The identity is computable in fixed-parameter time (indeed in linear time). -/
axiom fptTimeOn_id (D : Set (List ℕ)) (κ : List ℕ → ℕ) : FptTimeOn D κ fun x => x

/-- **Composition.** A fixed-parameter computation followed by one on its outputs, whose parameter
is bounded by a computable function of the first parameter, is a fixed-parameter computation. -/
axiom fptTimeOn_comp {D E : Set (List ℕ)} {κ κ' : List ℕ → ℕ} {F G : List ℕ → List ℕ}
    {g : ℕ → ℕ} (hF : FptTimeOn D κ F) (hmaps : ∀ x ∈ D, F x ∈ E) (hg : Computable g)
    (hκ : ∀ x ∈ D, κ' (F x) ≤ g (κ x)) (hG : FptTimeOn E κ' G) :
    FptTimeOn D κ fun x => G (F x)

/-- A bound on a set of inputs holds on every subset. -/
axiom fptTimeOn_mono {D D' : Set (List ℕ)} {κ : List ℕ → ℕ} {F : List ℕ → List ℕ} :
    D' ⊆ D → FptTimeOn D κ F → FptTimeOn D' κ F

/-- Only the values on the inputs of `D` matter. -/
axiom fptTimeOn_congr {D : Set (List ℕ)} {κ : List ℕ → ℕ} {F G : List ℕ → List ℕ} :
    (∀ x ∈ D, F x = G x) → FptTimeOn D κ F → FptTimeOn D κ G

/-- Polynomial time is fixed-parameter time, for every parameter. -/
axiom fptTimeOn_of_polyTimeOn {D : Set (List ℕ)} {F : List ℕ → List ℕ} (κ : List ℕ → ℕ) :
    PolyTimeOn D F → FptTimeOn D κ F

/-- A word has at most as many entries as bits: each entry costs at least its separator. -/
axiom length_le_bitSize (x : List ℕ) : x.length ≤ bitSize x

/-- Every entry of a word is smaller than `2` to the bit size of the word. -/
axiom lt_two_pow_bitSize {x : List ℕ} {v : ℕ} : v ∈ x → v < 2 ^ bitSize x

end Lax496464.WH_A4_MachineFacts
