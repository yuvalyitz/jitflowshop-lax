import Lax496464.WH_B4_Hierarchies
import Lax496464.WH_C2_HittingSet

/-!
---
title: Hitting Set is in W[2]
type: theorem
---
$p$-Hitting-Set is in W[2] [FG06, Example 5.2]. A hypergraph becomes the structure whose universe
has one element per vertex and one per hyperedge, with unary relations $\mathrm{VERT}$ and
$\mathrm{EDGE}$ distinguishing them and the incidence relation $I$, where $I y x$ states that vertex
$y$ lies in hyperedge $x$. A set $X$ of $k$ elements is a hitting set exactly when the structure
satisfies the $\Pi_2$-sentence

$$\mathrm{hs}(X) = \forall x\,\forall z\,\exists y\,\big((\mathrm{EDGE}\,x \to (Xy \wedge \mathrm{VERT}\,y \wedge
Iyx)) \wedge (Xz \to \mathrm{VERT}\,z)\big),$$

whose second conjunct makes the $k$ elements of $X$ vertices [FG06, Example 4.42].

# Formalization notes

In `hsFormula` the variables $x, y, z$ are $0, 1, 2$, and the relation symbols $\mathrm{VERT},
\mathrm{EDGE}, I$ are $0, 1, 2$. Since the universe size is written in binary, the reduction first
restricts the universe to the elements occurring in the sets and maps instances with $k$ larger
than the universe to a fixed no-instance.
-/

namespace Lax496464.WH_E1_HittingSetInW2

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_B4_Hierarchies
open Lax496464.WH_A2_FptReductions Lax496464.WH_C2_HittingSet

/-- `hs(X) = ∀x ∀z ∃y ((EDGE x → (Xy ∧ VERT y ∧ I y x)) ∧ (Xz → VERT z))`. -/
def hsFormula : Formula :=
  .all 0 (.all 2 (.ex 1 (.and
    (Formula.imp (.rel 1 [0]) (.and (.setVar [1]) (.and (.rel 0 [1]) (.rel 2 [1, 0]))))
    (Formula.imp (.setVar [2]) (.rel 0 [2])))))

/-- `hs(X)` is a `Π_2`-formula. -/
axiom hsFormula_isPi : IsPi 2 hsFormula

/-- `hs(X)` is a sentence. -/
axiom hsFormula_isSentence : IsSentence hsFormula

/-- The parameter of `p-Hitting-Set` is computable in polynomial time. -/
axiom hittingSet_isParameterized : IsParameterized HittingSet

/-- **The reduction:** `p-Hitting-Set ≤fpt p-WD_hs`. -/
axiom hittingSet_le_pWD : HittingSet ≤ᶠᵖᵗ pWD hsFormula 1

/-- **`p-Hitting-Set ∈ W[2]`.** -/
axiom hittingSet_mem_W2 : HittingSet ∈ W 2

end Lax496464.WH_E1_HittingSetInW2
