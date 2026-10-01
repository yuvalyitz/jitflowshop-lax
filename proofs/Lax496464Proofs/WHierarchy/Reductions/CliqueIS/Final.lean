import Lax496464.WH_D11_IndependentSet
import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.PolyTime

/-! # `p-Clique` and `p-Independent-Set` reduce to each other, by the complement graph

`clique_le_independentSet` and `independentSet_le_clique`: the complement map is a reduction both
ways (`Correct`), computed in polynomial time (`PolyTime`), hence an fpt-reduction both ways. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Final

open Lax496464.WH_A2_FptReductions Lax496464.WH_A5_Bridges Lax496464.WH_C1_GraphProblems
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Correct Lax496464Proofs.WHierarchy.Reductions.CliqueIS.PolyTime

/--
---
conclusion: Lax496464.WH_D11_IndependentSet.clique_le_independentSet
---
The map `(G, k) ↦ (Gᶜ, k)`, computed by one IMP+ program (read the word, build the adjacency
matrix from the CSR blocks, write the CSR word of the complement with the blocks in increasing
order, then `k`) in time quadratic in the word, is a reduction with the parameter unchanged.
-/
theorem clique_le_independentSet : Clique ≤ᶠᵖᵗ IndependentSet :=
  fptReduces_of_polyTime isReduction_clique_is paramBounded_clique_is polyTimeOn_complWord

/--
---
conclusion: Lax496464.WH_D11_IndependentSet.independentSet_le_clique
---
The same map, `(G, k) ↦ (Gᶜ, k)`: an independent set of `G` is a clique of `Gᶜ`.
-/
theorem independentSet_le_clique : IndependentSet ≤ᶠᵖᵗ Clique :=
  fptReduces_of_polyTime isReduction_is_clique paramBounded_is_clique polyTimeOn_complWord

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Final
