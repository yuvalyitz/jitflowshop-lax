import Lax496464.WH_D04_IncidenceStructure
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.PolyTime

/-! # Positive `Σ_1` model checking reduces to the binary case (Flum–Grohe, Lemma 6.13)

`pMC_positive_le_binary`: the incidence reduction of `Correct` is an fpt-reduction, computed in
polynomial time by the program of `PolyTime`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.Final

open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A2_FptReductions Lax496464.WH_A5_Bridges
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct Lax496464Proofs.WHierarchy.Lemmas.Incidence.PolyTime

/--
---
conclusion: Lax496464.WH_D04_IncidenceStructure.pMC_positive_le_binary
---
The incidence structure: the universe gets one new element per tuple (in the order the word lists
them), unary symbols `P_i` hold the new elements of the tuples of `R_i`, binary symbols `E_l`
connect entry `l` of a tuple to its element. Each atom `R_i y_0 … y_{k-1}` becomes
`E_0 y_0 z ∧ … ∧ E_{k-1} y_{k-1} z ∧ P_i z` for a fresh `z`, bound in front with the other
quantifiers. The map is computed by one IMP+ program in cubic time; the new formula is at most six
times as large.
-/
theorem pMC_positive_le_binary :
    pMC {φ | IsSigma 1 φ ∧ φ.IsPositive} ≤ᶠᵖᵗ
      pMC {φ | IsSigma 1 φ ∧ φ.IsPositive ∧ φ.ArityAtMost 2} :=
  fptReduces_of_polyTime isReduction paramBounded polyTimeOn_red

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.Final
