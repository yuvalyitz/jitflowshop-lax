import Lax496464.WH_B4_Hierarchies
import Lax496464.WH_C3_WeightedSat

/-!
---
title: Weighted d-CNF satisfiability is in A[1]
type: theorem
---
For every $d$, $p\text{-WSat}(d\text{-CNF}) \in \mathrm{A}[1]$ [FG06, Theorem 6.28]. Together with
`WH_D07_DefinabilityToWSat` this gives $\mathrm{W}[1] \subseteq \mathrm{A}[1]$.

**Construction.** Given $\alpha \in d$-CNF and $k$, the reduction builds a structure and a
$\Sigma_1$-sentence $\exists x_1 \dots \exists x_k\,(\bigwedge_{i<j} \neg\, x_i = x_j \wedge \psi)$,
with $\psi$ depending on $d$ and $k$ only, such that the sentence holds exactly when a set of $k$
variables satisfies $\alpha$ [FG06, Lemma 6.31]. Each variable is represented by its first
occurrence in $\alpha$. A clause $\neg X_{i_1} \vee \dots \vee \neg X_{i_r} \vee X_{j_1} \vee \dots
\vee X_{j_s}$ is satisfied by the chosen set exactly when the set does not contain all of
$X_{i_1}, \dots, X_{i_r}$ or meets $\{X_{j_1}, \dots, X_{j_s}\}$. For each negative part, the
positive parts form a hypergraph with edges of size at most $d$; its hitting sets of size at most
$k$ are found by a search tree of $d^k$ branches [FG06, Lemma 1.17], and the sets found are stored
in a relation, grouped by negative part. The sentence names the hitting set it uses by further
existentially quantified variables.

**Complexity.** The reduction runs in time $(d+2)^{O(k)}(k+2)^{O(d)}\cdot|x|^{O(1)}$:
fixed-parameter, not polynomial.
-/

namespace Lax496464.WH_D08_WSatInA1

open Lax496464.WH_B4_Hierarchies Lax496464.WH_C3_WeightedSat

/-- **`p-WSat(d-CNF) ∈ A[1]`** [FG06, Theorem 6.28]. -/
axiom pWSat_mem_A1 (d : ℕ) : pWSat {α | IsDCNF d α} ∈ A 1

end Lax496464.WH_D08_WSatInA1
