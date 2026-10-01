import Lax496464.WH_B3_LogicProblems
import Lax496464.WH_A2_FptReductions
import Lax496464.WH_C1_GraphProblems

/-!
---
title: Σ₁ model checking over binary relations reduces to Clique
type: theorem
---
$p\text{-MC}(\Sigma_1[2]) \le^{\mathrm{fpt}} p\text{-Clique}$, where $\Sigma_1[2]$ is the class of
$\Sigma_1$-formulas whose relation symbols have arity at most $2$ [FG06, Lemma 6.14]. This is the
third of the three reductions showing Clique A[1]-hard (`WH_D06_CliqueA1Complete`).

**Construction.** Let $\varphi = \exists \bar x\, \psi$ with $\psi$ quantifier-free, and let $q$ be the
number of atoms of $\psi$, each of which has at most two variables. The vertices range over
*candidate* elements only — the entries of the word that are elements, and the first $|x| + 2q$
elements — which changes no answer, since elements occurring in no relation are interchangeable.
The graph has one copy for every truth valuation $\beta$ of the $q$ atoms; the vertices of a copy
are pairs of a *row* (two per atom, one for each argument place) and a candidate. Two vertices of
the copy of $\beta$ are adjacent when they respect $\beta$ on their atom, agree wherever they carry
the same variable, and $\psi$ is true under $\beta$. A clique of $2q$ vertices then selects values
of the variables that satisfy $\psi$ with atom values $\beta$, and conversely. This replaces the
disjunctive normal form of [FG06, Lemma 6.14] by an enumeration of valuations.

**Complexity.** The new parameter is $2q \le 2|\varphi|$. The graph has $2^q \cdot O(|x|) \cdot 2q$
vertices, so the reduction runs in time $f(|\varphi|)\cdot|x|^{O(1)}$: fixed-parameter, not
polynomial.
-/

namespace Lax496464.WH_D05_BinaryToClique

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_A2_FptReductions
open Lax496464.WH_C1_GraphProblems

/-- **`p-MC(Σ_1[2]) ≤fpt p-Clique`** [FG06, Lemma 6.14]. -/
axiom pMC_binary_le_clique : pMC {φ | IsSigma 1 φ ∧ φ.ArityAtMost 2} ≤ᶠᵖᵗ Clique

end Lax496464.WH_D05_BinaryToClique
