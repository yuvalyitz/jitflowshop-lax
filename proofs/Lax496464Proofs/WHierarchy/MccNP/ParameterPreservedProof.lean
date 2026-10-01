import Lax496464.WH_F4_IndependentSetToMcc
import Lax496464Proofs.WHierarchy.MccNP.Shape

/-!
# The parameter is preserved

The word of the multicoloured graph ends with the number `k` of colours, and the parameter of the
word of an instance is its threshold `k` (`Shape.threshold_word`).
-/

namespace Lax496464Proofs.WHierarchy.MccNP.ParameterPreservedProof

open Lax496464.WH_F1_IndependentSetMatrix Lax762056.GraphEncoding
open Lax496464.WH_F2_MccConstruction (reduce)

/-- The parameter of the multicoloured graph's word is the threshold of the instance: the word
ends with `[I.threshold]`. -/
lemma param_construction_word (I : Instance) :
    Lax888481.MulticolouredClique.problem.param (Lax496464.WH_F2_MccConstruction.word I) =
      I.threshold := by
  show ((Lax496464.WH_F2_MccConstruction.word I).getLast?).getD 0 = I.threshold
  unfold Lax496464.WH_F2_MccConstruction.word
  rw [List.getLast?_concat]
  rfl

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.parameter_preserved
---
The parameter is preserved, `k' = k`: the word of an independent-set instance is mapped to the word of
its multicoloured graph, whose last entry is the threshold, which is the parameter of the
independent-set word.
-/
theorem parameter_preserved_proved :
    ∀ x ∈ problem.Domain,
      Lax888481.MulticolouredClique.problem.param (reduce x) = problem.param x := by
  intro x hx
  have hx' : x ∈ Instances := hx
  obtain ⟨I, rfl⟩ := hx'
  have hv : Shape.Valid (word I) := Shape.valid_iff_mem.mpr ⟨I, rfl⟩
  have hd : Shape.decode (word I) = I := Shape.word_injective (Shape.word_decode hv)
  rw [Shape.reduce_valid hv, hd, param_construction_word]
  show I.threshold = threshold (word I)
  rw [Shape.threshold_word]

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.parameter_preserved :=
  parameter_preserved_proved

end Lax496464Proofs.WHierarchy.MccNP.ParameterPreservedProof
