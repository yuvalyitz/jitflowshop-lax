import Lax496464.WH_B3_LogicProblems
import Lax496464.WH_A2_FptReductions

/-!
---
title: Positive Σ₁ model checking reduces to binary relations
type: theorem
---
$p\text{-MC}(\Sigma_1^+) \le^{\mathrm{fpt}} p\text{-MC}(\Sigma_1^+[2])$, where $\Sigma_1^+[2]$ is the class
of positive $\Sigma_1$-formulas whose relation symbols have arity at most $2$ [FG06, Lemma 6.13].
This is the second of the three reductions showing Clique A[1]-hard (`WH_D06_CliqueA1Complete`).

**Construction.** The structure is replaced by its *incidence structure* [FG06, Definition 6.12]:
its universe consists of the elements of $\mathcal A$ and one new element $b_{R,\bar a}$ for every
tuple $\bar a$ of every relation $R$; a unary relation $P_R$ holds the new elements of $R$; and
binary relations $E_1, \dots, E_r$ connect $a_i$ to $b_{R,\bar a}$ when $a_i$ is the $i$-th entry of
$\bar a$, where $r$ is the largest arity of an atom of $\varphi$. Every atom $R x_1 \dots x_r$ is
replaced by $\exists y\,(P_R\, y \wedge E_1 x_1 y \wedge \dots \wedge E_r x_r y)$, and the new
quantifiers are moved to the front. The atoms $E_i\,x\,y$ force $x$ to be an element of
$\mathcal A$, and a positive formula stays true when its remaining variables are moved to elements
of $\mathcal A$, so the old elements need no marking relation.

**Complexity.** The reduction is computable in polynomial time, and the new formula has size
$O(|\varphi|)$.
-/

namespace Lax496464.WH_D04_IncidenceStructure

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_A2_FptReductions

/-- **`p-MC(Σ_1⁺) ≤fpt p-MC(Σ_1⁺[2])`** [FG06, Lemma 6.13]. -/
axiom pMC_positive_le_binary :
    pMC {φ | IsSigma 1 φ ∧ φ.IsPositive} ≤ᶠᵖᵗ
      pMC {φ | IsSigma 1 φ ∧ φ.IsPositive ∧ φ.ArityAtMost 2}

end Lax496464.WH_D04_IncidenceStructure
