import Lax496464.WH_B4_Hierarchies
import Lax496464.WH_C2_HittingSet
import Lax496464.WH_C3_WeightedSat

/-!
---
title: Hitting Set Is W[2]-Complete
type: theorem
---
$p$-Hitting-Set is W[2]-complete under fpt-reductions [FG06, Theorem 7.14]. It is in W[2]
(`WH_E1_HittingSetInW2`), and it is W[2]-hard in two steps.

1. **Every $\Pi_2$ weighted definability problem reduces to weighted monotone CNF satisfiability**
   [FG06, Theorem 7.1]. Let $\varphi = \forall \bar x\, \exists \bar y\, \psi(X)$ and let $(\mathcal A, k)$
   be an instance. As in `WH_D07_DefinabilityToWSat`, the universe is restricted to a set $U$ of
   polynomially many elements. A witness is an increasing list $t_0 < \dots < t_{k-1}$ of codes of
   $s$-tuples over $U$. The propositional variables describe, for each of $(k+1)^D$ *blocks*, the
   values of $D$ positions of that list, $D$ depending on $\psi$ only. Monotone clauses force
   exactly one value per block and the consistency of any two blocks, so that the true variables
   describe a single list; and for every assignment to $\bar x$, one clause collects the block
   values under which some assignment to $\bar y$ makes $\psi$ true. The weight is the number of
   blocks. This monotone formula replaces the propositional normalization of
   [FG06, Lemma 7.5].
2. **Weighted monotone CNF satisfiability reduces to Hitting Set** [FG06, Theorem 7.14]: the
   hyperedges are the clauses, read as sets of variables; an assignment of weight $k$ satisfies the
   formula exactly when its true variables meet every clause.
-/

namespace Lax496464.WH_E2_HittingSetW2Complete

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_B4_Hierarchies
open Lax496464.WH_A2_FptReductions Lax496464.WH_C2_HittingSet Lax496464.WH_C3_WeightedSat

/-- **Step 1:** weighted definability of a `Π_2`-sentence fpt-reduces to weighted satisfiability of
monotone CNF formulas [FG06, Theorem 7.1(1] for `t = 2`, via Lemmas 7.2 and 7.5). -/
axiom pWD_le_pWSat_monotone {φ : Formula} (s : ℕ) (hφ : IsPi 2 φ) (hs : IsSentence φ) :
    pWD φ s ≤ᶠᵖᵗ pWSat {α | IsMonotone α}

/-- **Step 2:** weighted monotone CNF satisfiability fpt-reduces to `p-Hitting-Set`. -/
axiom pWSat_monotone_le_hittingSet : pWSat {α | IsMonotone α} ≤ᶠᵖᵗ HittingSet

/-- **`p-Hitting-Set` is W[2]-complete** [FG06, Theorem 7.14]. -/
axiom hittingSet_W2_complete : Complete (W 2) HittingSet

end Lax496464.WH_E2_HittingSetW2Complete
