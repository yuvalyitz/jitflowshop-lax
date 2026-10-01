import Lax496464.WH_E1_HittingSetInW2
import Lax496464.WH_E2_HittingSetW2Complete
import Lax496464.WH_E3_DominatingSet
import Lax496464.WH_A3_ReductionCalculus
import Lax496464.WH_B5_HierarchyFacts

/-! The W[2] results assembled from their steps. -/

namespace Lax496464Proofs.WHierarchy.W2Derived

open Lax496464
open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_B4_Hierarchies
open Lax496464.WH_A2_FptReductions Lax496464.WH_A3_ReductionCalculus Lax496464.WH_B5_HierarchyFacts
open Lax496464.WH_C1_GraphProblems Lax496464.WH_C2_HittingSet
open Lax496464.WH_E1_HittingSetInW2 Lax496464.WH_E2_HittingSetW2Complete Lax496464.WH_E3_DominatingSet

/--
---
conclusion: Lax496464.WH_E1_HittingSetInW2.hsFormula_isPi
---
-/
theorem hsFormula_isPi : IsPi 2 hsFormula :=
  ⟨[0, 2], _, rfl, [1], _, rfl, by simp [Alt, Formula.IsQF, Formula.imp]⟩

/--
---
conclusion: Lax496464.WH_E1_HittingSetInW2.hsFormula_isSentence
---
-/
theorem hsFormula_isSentence : IsSentence hsFormula := by
  unfold IsSentence; decide

/--
---
conclusion: Lax496464.WH_E1_HittingSetInW2.hittingSet_mem_W2
---
-/
theorem hittingSet_mem_W2 : HittingSet ∈ W 2 :=
  mem_closure_of_fptReduces hittingSet_isParameterized hittingSet_le_pWD
    (pWD_mem_W 1 WH_E1_HittingSetInW2.hsFormula_isPi WH_E1_HittingSetInW2.hsFormula_isSentence)

/--
---
conclusion: Lax496464.WH_E2_HittingSetW2Complete.hittingSet_W2_complete
---
-/
theorem hittingSet_W2_complete : Complete (W 2) HittingSet :=
  ⟨WH_E1_HittingSetInW2.hittingSet_mem_W2, hard_closure_of fun _ ⟨_, s, hφ, hs, hP⟩ =>
    hP ▸ fptReduces_trans (pWD_le_pWSat_monotone s hφ hs) pWSat_monotone_le_hittingSet⟩

/--
---
conclusion: Lax496464.WH_E3_DominatingSet.dominatingSet_W2_complete
---
-/
theorem dominatingSet_W2_complete : Complete (W 2) DominatingSet :=
  ⟨mem_closure_of_fptReduces dominatingSet_isParameterized dominatingSet_le_hittingSet
      WH_E1_HittingSetInW2.hittingSet_mem_W2,
    hard_of_fptReduces WH_E2_HittingSetW2Complete.hittingSet_W2_complete.2
      hittingSet_le_dominatingSet⟩

end Lax496464Proofs.WHierarchy.W2Derived
