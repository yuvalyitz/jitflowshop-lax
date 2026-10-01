import Lax496464.WH_F3_NPHard
import Lax496464.WH_F4_IndependentSetToMcc
import Lax762056.IndependentSetHardness

/-!
---
title: Multicoloured Clique is NP-hard
type: theorem
---
**Multicoloured Clique is NP-hard**: every language in NP reduces to it by a map computable in
polynomial time by a Turing machine [FHRV09], [CFK+15, Theorem 13.7].

Independent Set is NP-hard, as proved in the archive (`Lax762056`). The reduction of
`WH_F4_IndependentSetToMcc` is computable in polynomial time on the word RAM, hence by a Turing machine
(`Lax759944`), and preserves the answer. Composing a reduction to Independent Set, the rewriting of
its output bits as a word of numbers, and this reduction gives a reduction to Multicoloured Clique.
The reduction to Independent Set always produces an instance, so the composite always produces the
word of a Multicoloured Clique instance (`mcc_npHard_in`), which is what a further reduction that is
correct only on instances needs.

# Formalization notes

NP-hardness is `WH_F3_NPHard.NPHard`, for the problem without its parameter. The parameterized
statement is `WH_F4_IndependentSetToMcc.independentSet_le_mcc`.
-/

namespace Lax496464.WH_F5_MccNPHard

/-- **Multicoloured Clique is NP-hard.** -/
axiom mcc_npHard : WH_F3_NPHard.NPHard Lax888481.MulticolouredClique.problem

/-- **Multicoloured Clique is NP-hard on its domain**: the reduction moreover always outputs the
word of an instance. -/
axiom mcc_npHard_in : WH_F3_NPHard.NPHardIn Lax888481.MulticolouredClique.problem

end Lax496464.WH_F5_MccNPHard
