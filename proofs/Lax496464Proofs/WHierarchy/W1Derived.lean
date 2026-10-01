import Lax496464.WH_D01_CliqueInW1
import Lax496464.WH_D02_CliqueInA1
import Lax496464.WH_D03_NegationElimination
import Lax496464.WH_D04_IncidenceStructure
import Lax496464.WH_D05_BinaryToClique
import Lax496464.WH_D06_CliqueA1Complete
import Lax496464.WH_D07_DefinabilityToWSat
import Lax496464.WH_D08_WSatInA1
import Lax496464.WH_D09_W1EqA1
import Lax496464.WH_D10_CliqueW1Complete
import Lax496464.WH_D11_IndependentSet
import Lax496464.WH_D12_MulticolouredClique
import Lax496464.WH_A3_ReductionCalculus
import Lax496464.WH_B5_HierarchyFacts

/-! The W[1] results assembled from their steps: each theorem here uses only the step statements
of its concept and the calculus of reductions. -/

namespace Lax496464Proofs.WHierarchy.W1Derived

open Lax496464
open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems Lax496464.WH_B4_Hierarchies
open Lax496464.WH_A2_FptReductions Lax496464.WH_A3_ReductionCalculus Lax496464.WH_B5_HierarchyFacts
open Lax496464.WH_C1_GraphProblems Lax496464.WH_C3_WeightedSat
open Lax496464.WH_D01_CliqueInW1 Lax496464.WH_D02_CliqueInA1 Lax496464.WH_D03_NegationElimination
open Lax496464.WH_D04_IncidenceStructure Lax496464.WH_D05_BinaryToClique Lax496464.WH_D06_CliqueA1Complete
open Lax496464.WH_D07_DefinabilityToWSat Lax496464.WH_D08_WSatInA1 Lax496464.WH_D09_W1EqA1
open Lax496464.WH_D10_CliqueW1Complete Lax496464.WH_D11_IndependentSet Lax496464.WH_D12_MulticolouredClique

/--
---
conclusion: Lax496464.WH_D01_CliqueInW1.cliqueFormula_isPi
---
-/
theorem cliqueFormula_isPi : IsPi 1 cliqueFormula :=
  ⟨[0, 1], _, rfl, by simp [Alt, Formula.IsQF]⟩

/--
---
conclusion: Lax496464.WH_D01_CliqueInW1.cliqueFormula_isSentence
---
-/
theorem cliqueFormula_isSentence : IsSentence cliqueFormula := by
  unfold IsSentence; decide

/--
---
conclusion: Lax496464.WH_D01_CliqueInW1.clique_mem_W1
---
-/
theorem clique_mem_W1 : Clique ∈ W 1 :=
  mem_closure_of_fptReduces clique_isParameterized clique_le_pWD
    (pWD_mem_W 1 WH_D01_CliqueInW1.cliqueFormula_isPi WH_D01_CliqueInW1.cliqueFormula_isSentence)

/--
---
conclusion: Lax496464.WH_D02_CliqueInA1.clique_mem_A1
---
-/
theorem clique_mem_A1 : Clique ∈ A 1 :=
  mem_closure_of_fptReduces clique_isParameterized clique_le_pMC (pMC_mem_A 1)

/--
---
conclusion: Lax496464.WH_D06_CliqueA1Complete.clique_A1_complete
---
-/
theorem clique_A1_complete : Complete (A 1) Clique := by
  refine ⟨WH_D02_CliqueInA1.clique_mem_A1, hard_closure_of fun P hP => ?_⟩
  rw [Set.mem_singleton_iff] at hP
  subst hP
  exact fptReduces_trans pMC_sigma1_le_positive <| fptReduces_trans pMC_positive_le_binary <|
    fptReduces_trans (pMC_mono fun φ (hφ : IsSigma 1 φ ∧ φ.IsPositive ∧ φ.ArityAtMost 2) =>
      (⟨hφ.1, hφ.2.2⟩ : IsSigma 1 φ ∧ φ.ArityAtMost 2)) pMC_binary_le_clique

/--
---
conclusion: Lax496464.WH_D09_W1EqA1.W1_eq_A1
---
-/
theorem W1_eq_A1 : W 1 = A 1 := by
  apply Set.Subset.antisymm
  · rintro P ⟨hpar, Q, ⟨φ, s, hφ, hs, rfl⟩, hPQ⟩
    obtain ⟨d, hd⟩ := pWD_le_pWSat s hφ hs
    exact mem_closure_of_fptReduces hpar (fptReduces_trans hPQ hd) (pWSat_mem_A1 d)
  · intro P hP
    exact mem_closure_of_fptReduces hP.1 (WH_D06_CliqueA1Complete.clique_A1_complete.2 P hP)
      WH_D01_CliqueInW1.clique_mem_W1

/--
---
conclusion: Lax496464.WH_D10_CliqueW1Complete.clique_W1_complete
---
-/
theorem clique_W1_complete : Complete (W 1) Clique :=
  ⟨WH_D01_CliqueInW1.clique_mem_W1, WH_D09_W1EqA1.W1_eq_A1 ▸ WH_D06_CliqueA1Complete.clique_A1_complete.2⟩

/--
---
conclusion: Lax496464.WH_D10_CliqueW1Complete.clique_W1_hard
---
-/
theorem clique_W1_hard : Hard (W 1) Clique := WH_D10_CliqueW1Complete.clique_W1_complete.2

/--
---
conclusion: Lax496464.WH_D11_IndependentSet.independentSet_W1_complete
---
-/
theorem independentSet_W1_complete : Complete (W 1) IndependentSet :=
  ⟨mem_closure_of_fptReduces independentSet_isParameterized independentSet_le_clique
      WH_D01_CliqueInW1.clique_mem_W1,
    hard_of_fptReduces WH_D10_CliqueW1Complete.clique_W1_hard clique_le_independentSet⟩

/--
---
conclusion: Lax496464.WH_D12_MulticolouredClique.multicolouredClique_W1_complete
---
-/
theorem multicolouredClique_W1_complete : Complete (W 1) Lax888481.MulticolouredClique.problem :=
  ⟨mem_closure_of_fptReduces multicolouredClique_isParameterized multicolouredClique_le_clique
      WH_D01_CliqueInW1.clique_mem_W1,
    hard_of_fptReduces WH_D10_CliqueW1Complete.clique_W1_hard clique_le_multicolouredClique⟩

end Lax496464Proofs.WHierarchy.W1Derived
