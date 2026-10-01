import Lax496464.WH_D01_CliqueInW1
import Lax496464.WH_D11_IndependentSet
import Lax496464.WH_D12_MulticolouredClique
import Lax496464.WH_E3_DominatingSet
import Lax496464.WH_B5_HierarchyFacts
import Lax496464Proofs.WHierarchy.Machine.LastEntry

/-! The problems whose parameter is the last entry of the word are parameterized problems. -/

namespace Lax496464Proofs.WHierarchy.Parameters

open Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Machine.LastEntry

/--
---
conclusion: Lax496464.WH_D01_CliqueInW1.clique_isParameterized
---
-/
theorem clique_isParameterized : IsParameterized Clique := polyTimeOn_last _

/--
---
conclusion: Lax496464.WH_D11_IndependentSet.independentSet_isParameterized
---
-/
theorem independentSet_isParameterized : IsParameterized IndependentSet := polyTimeOn_last _

/--
---
conclusion: Lax496464.WH_E3_DominatingSet.dominatingSet_isParameterized
---
-/
theorem dominatingSet_isParameterized : IsParameterized DominatingSet := polyTimeOn_last _

/--
---
conclusion: Lax496464.WH_D12_MulticolouredClique.multicolouredClique_isParameterized
---
-/
theorem multicolouredClique_isParameterized :
    IsParameterized Lax888481.MulticolouredClique.problem := polyTimeOn_last _

/--
---
conclusion: Lax496464.WH_B5_HierarchyFacts.pWD_isParameterized
---
-/
theorem pWD_isParameterized (φ : Lax496464.WH_B2_FirstOrder.Formula) (s : ℕ) :
    IsParameterized (pWD φ s) := polyTimeOn_last _

end Lax496464Proofs.WHierarchy.Parameters
