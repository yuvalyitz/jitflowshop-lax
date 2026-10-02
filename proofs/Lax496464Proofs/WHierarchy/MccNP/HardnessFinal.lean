import Lax496464Proofs.WHierarchy.MccNP.HardnessProof
import Lax496464Proofs.WHierarchy.MccNP.ReductionCorrectProof
import Lax496464Proofs.WHierarchy.MccNP.ParameterPreservedProof
import Lax496464Proofs.WHierarchy.MccNP.Ram.FptTimeProof
import Lax496464Proofs.WHierarchy.MccNP.Ram.PolyTimeProof
import Lax496464.WH_A5_Bridges

/-!
# Independent Set Reduces to Multicoloured Clique; Multicoloured Clique Is NP-Hard

The general arguments of `HardnessProof` applied to the proved properties of `reduce`, and the
fpt-reduction of `WH_A2_FptReductions` obtained from them by `WH_A5_Bridges.fptReduces_of_polyTime`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.HardnessFinal

open Lax496464.WH_F1_IndependentSetMatrix
open Lax496464.WH_F2_MccConstruction (reduce)
open Lax496464Proofs.WHierarchy.MccNP.ReductionCorrectProof

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.independentSet_isFptReduction
---
Independent Set fpt-reduces to Multicoloured Clique with `g k = (k + 1) ^ 2` and `h k = k`: the map
is correct, sends words of instances to words of instances, preserves the parameter `k`, and runs
in time `c * (k + 1) ^ 2 * (|x| + 1)`.
-/
theorem independentSet_isFptReduction_proved :
    ∃ (prog : Lax808846.Ram.Program) (c : ℕ),
      Lax888481.ParameterizedComplexity.IsFptReduction problem
        Lax888481.MulticolouredClique.problem reduce prog c (fun k => (k + 1) ^ 2) (fun k => k) :=
  HardnessProof.isFptReduction_of reduce_maps_domain_proved reduce_correct_proved
    Lax496464Proofs.WHierarchy.MccNP.ParameterPreservedProof.parameter_preserved_proved
    Lax496464Proofs.WHierarchy.MccNP.Ram.FptTimeProof.reduce_fptTime_proved

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.independentSet_fptReduces_mcc
---
The same fact with the functions `g` and `h` forgotten.
-/
theorem independentSet_fptReduces_mcc_proved :
    Lax888481.ParameterizedComplexity.FptReduces problem Lax888481.MulticolouredClique.problem :=
  HardnessProof.fptReduces_of_isFptReduction independentSet_isFptReduction_proved

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.independentSet_polyReduces_mcc
---
The same map is a polynomial-time reduction on every word.
-/
theorem independentSet_polyReduces_mcc_proved :
    Lax888481.PolynomialReduction.PolyReduces {x | problem.Yes x}
      {x | Lax888481.MulticolouredClique.problem.Yes x} :=
  HardnessProof.polyReduces_of Lax496464Proofs.WHierarchy.MccNP.Ram.PolyTimeProof.reduce_polyTime_proved
    reduce_correct_proved reduce_reject_proved

/--
---
conclusion: Lax496464.WH_F5_MccNPHard.mcc_npHard
---
Multicoloured Clique is NP-hard: Independent Set is (archive), and the reduction is polynomial-time
computable, sends the word of an instance to the word of its construction, and preserves the answer.
-/
theorem mcc_npHard_proved : Lax496464.WH_F3_NPHard.NPHard Lax888481.MulticolouredClique.problem :=
  HardnessProof.mcc_npHard_of Lax496464Proofs.WHierarchy.MccNP.Ram.PolyTimeProof.reduce_polyTime_proved
    reduce_word_proved fun I => by
      rw [← mcc_yes_word I]

/--
---
conclusion: Lax496464.WH_F5_MccNPHard.mcc_npHard_in
---
The same, and the word produced is always the word of an instance: it is the word of the construction
on an instance of Independent Set, which encodes the multicoloured graph.
-/
theorem mcc_npHard_in_proved :
    Lax496464.WH_F3_NPHard.NPHardIn Lax888481.MulticolouredClique.problem :=
  HardnessProof.mcc_npHard_in_of Lax496464Proofs.WHierarchy.MccNP.Ram.PolyTimeProof.reduce_polyTime_proved
    reduce_word_proved (fun I => by rw [← mcc_yes_word I])
    fun I => ⟨_, Lax496464Proofs.WHierarchy.MccNP.WordEncodesProof.word_encodes_proved I⟩

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.independentSet_le_mcc
---
`reduce` is a reduction with the parameter preserved (`g = id`), computable in polynomial time;
`WH_A5_Bridges.fptReduces_of_polyTime` makes it an fpt-reduction.
-/
theorem independentSet_le_mcc_proved :
    Lax496464.WH_A2_FptReductions.FptReduces problem Lax888481.MulticolouredClique.problem :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime (R := reduce)
    ⟨Lax496464.WH_F4_IndependentSetToMcc.reduce_maps_domain,
      Lax496464.WH_F4_IndependentSetToMcc.reduce_correct⟩
    ⟨id, Computable.id, fun x hx =>
      le_of_eq (Lax496464.WH_F4_IndependentSetToMcc.parameter_preserved x hx)⟩
    (Lax496464.WH_A5_Bridges.polyTimeOn_of_ramPolytime _
      Lax496464.WH_F4_IndependentSetToMcc.reduce_polyTime)

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.independentSet_isFptReduction :=
  independentSet_isFptReduction_proved
example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.independentSet_fptReduces_mcc :=
  independentSet_fptReduces_mcc_proved
example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.independentSet_polyReduces_mcc :=
  independentSet_polyReduces_mcc_proved
example : type_of% @Lax496464.WH_F5_MccNPHard.mcc_npHard := mcc_npHard_proved
example : type_of% @Lax496464.WH_F5_MccNPHard.mcc_npHard_in := mcc_npHard_in_proved
example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.independentSet_le_mcc :=
  independentSet_le_mcc_proved

end Lax496464Proofs.WHierarchy.MccNP.HardnessFinal
