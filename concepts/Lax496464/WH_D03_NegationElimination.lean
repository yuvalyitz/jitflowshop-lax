import Lax496464.WH_B3_LogicProblems
import Lax496464.WH_A2_FptReductions

/-!
---
title: Model checking for Σ₁ reduces to positive Σ₁
type: theorem
---
$p\text{-MC}(\Sigma_1) \le^{\mathrm{fpt}} p\text{-MC}(\Sigma_1^+)$, where $\Sigma_1^+$ is the class of
$\Sigma_1$-formulas without negation symbols [FG06, Lemma 6.11]. This is the first of the three
reductions showing Clique A[1]-hard (`WH_D06_CliqueA1Complete`).

**Construction.** The universe is first restricted: the entries of the tuples are renamed by rank,
and the universe is cut down to $\min(|A|, T + |x|)$ elements, where $T$ is the number of tuple
entries; no $\Sigma_1$-formula of size at most $|x|$ distinguishes the two structures. The structure
is then expanded by a linear order $<$ of the universe and, for each relation $R$ of arity $r$, by
the relations $R_f$ and $R_l$ holding the lexicographically first and last tuples of $R$, the
$2r$-ary successor relation $R_s$ of $R$ in the lexicographic order, and a unary relation holding
the whole universe if $R$ is empty and nothing otherwise. A tuple is *not* in $R$ exactly when $R$
is empty, or the tuple lies lexicographically below the first tuple, strictly between two
successive ones, or above the last one — a positive existential condition. The formula is brought
into negation normal form, every $\neg R\bar x$ is replaced by this condition, and every
$\neg\, x = y$ by $x < y \vee y < x$.

The expansion has size polynomial in that of $\mathcal A$ whatever the arities, whereas adding the
complements of the relations would be exponential in the arity.

**Complexity.** The reduction is computable in polynomial time, and the new formula has size
$O(|\varphi|)$.
-/

namespace Lax496464.WH_D03_NegationElimination

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_A2_FptReductions

/-- **`p-MC(Σ_1) ≤fpt p-MC(Σ_1⁺)`** [FG06, Lemma 6.11]. -/
axiom pMC_sigma1_le_positive :
    pMC {φ | IsSigma 1 φ} ≤ᶠᵖᵗ pMC {φ | IsSigma 1 φ ∧ φ.IsPositive}

end Lax496464.WH_D03_NegationElimination
