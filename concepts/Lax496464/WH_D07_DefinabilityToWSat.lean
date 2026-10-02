import Lax496464.WH_B3_LogicProblems
import Lax496464.WH_A2_FptReductions
import Lax496464.WH_C3_WeightedSat

/-!
---
title: Weighted Definability of a Π₁ Sentence Reduces to Weighted d-CNF Satisfiability
type: theorem
---
For every $\Pi_1$-sentence $\varphi(X)$ there is a $d \ge 1$ such that
$p\text{-WD}_\varphi \le^{\mathrm{fpt}} p\text{-WSat}(d\text{-CNF})$ [FG06, Lemma 6.37]. Together with
`WH_D08_WSatInA1` this gives $\mathrm{W}[1] \subseteq \mathrm{A}[1]$.

**Construction.** Write the quantifier-free part of $\varphi = \forall x_1 \dots \forall x_r\, \psi$
in conjunctive normal form $\bigwedge_{i \in I} \bigvee_{j \in J} \lambda_{ij}$. Let $U$ be the
elements occurring in the structure's word together with the first $|x| + s\cdot k + r$ elements;
the remaining elements occur in no relation and are interchangeable, so a witness can be moved into
$U$. Take a propositional variable $Y_{\bar a}$ for every $\bar a \in U^s$ ($s$ the arity of $X$),
meaning $\bar a \in X$. For every $i \in I$ and $a_1, \dots, a_r \in U$ form the clause of the
literals $\lambda_{ij}(a_1, \dots, a_r)$: a literal $(\neg) X\bar y$ becomes $(\neg) Y_{\bar a}$ for
the tuple $\bar a$ of values of $\bar y$; a literal without $X$ is evaluated in $\mathcal A$ and
dropped if false, and the whole clause is dropped if it is true. The clauses
$Y_{\bar a} \vee \neg Y_{\bar a}$ make every variable occur. Then $\mathcal A \models \varphi(S)$ iff
$\{Y_{\bar b} : \bar b \in S\}$ satisfies the formula, and $k$ is unchanged.

**Complexity.** The formula has $O(|U|^{r+s}\cdot|\varphi|)$ literals; since $|U|$ grows with $k$,
the reduction runs in time $(|x|\cdot k)^{O(1)}$, fixed-parameter.
-/

namespace Lax496464.WH_D07_DefinabilityToWSat

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_A2_FptReductions
open Lax496464.WH_C3_WeightedSat

/-- **`p-WD_φ ≤fpt p-WSat(d-CNF)`** for every `Π_1`-sentence `φ` and some `d`
[FG06, Lemma 6.37]. -/
axiom pWD_le_pWSat {φ : Formula} (s : ℕ) (hφ : IsPi 1 φ) (hs : IsSentence φ) :
    ∃ d, pWD φ s ≤ᶠᵖᵗ pWSat {α | IsDCNF d α}

end Lax496464.WH_D07_DefinabilityToWSat
