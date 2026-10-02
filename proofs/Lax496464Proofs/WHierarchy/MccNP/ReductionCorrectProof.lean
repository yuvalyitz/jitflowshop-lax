import Lax496464.WH_F4_IndependentSetToMcc
import Lax496464Proofs.WHierarchy.MccNP.Shape
import Lax496464Proofs.WHierarchy.MccNP.CorrectnessProof
import Lax496464Proofs.WHierarchy.MccNP.WordEncodesProof
import Lax496464Proofs.WHierarchy.MccNP.MccUniqueness

/-!
# The Reduction on Words Is Correct

`reduce` on the words of instances and elsewhere, and the facts that it maps instances to
instances and preserves the answer. They follow from the correctness of the construction, the
injectivity of the word of an instance, and `MccUniqueness`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.ReductionCorrectProof

open Lax762056.GraphEncoding (Instance)
open Lax496464.WH_F1_IndependentSetMatrix
open Lax496464.WH_F2_MccConstruction (reduce)
open Lax496464Proofs.WHierarchy.MccNP.Shape

/-- The reduction on the word of an instance is the word of its construction. -/
theorem reduce_word_eq (I : Instance) : reduce (word I) = Lax496464.WH_F2_MccConstruction.word I := by
  have hmem : word I ∈ Instances := ⟨I, rfl⟩
  have hv : Valid (word I) := valid_iff_mem.2 hmem
  rw [reduce_valid hv]
  have : decode (word I) = I := word_injective (word_decode hv)
  rw [this]

/-- The yes-instances of Independent Set are the words of instances with the property. -/
theorem yes_word (I : Instance) :
    problem.Yes (word I) ↔ Lax762056.GraphProblems.IndependentSet I := by
  constructor
  · rintro ⟨I', h, hI'⟩
    have : I' = I := word_injective h.symm
    exact this ▸ hI'
  · intro h; exact ⟨I, rfl, h⟩

theorem mcc_yes_word (I : Instance) :
    Lax888481.MulticolouredClique.problem.Yes (Lax496464.WH_F2_MccConstruction.word I) ↔
      Lax762056.GraphProblems.IndependentSet I := by
  rw [MccUniqueness.yes_iff (Lax496464Proofs.WHierarchy.MccNP.WordEncodesProof.word_encodes_proved I)]
  exact (Lax496464Proofs.WHierarchy.MccNP.CorrectnessProof.construct_correct_proved I).symm

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.reduce_word
---
On the word of an instance the reduction is the word of the construction: the encoding is
injective, so the instance chosen by the definition is the instance itself.
-/
theorem reduce_word_proved (I : Instance) : reduce (word I) = Lax496464.WH_F2_MccConstruction.word I :=
  reduce_word_eq I

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.reduce_off_domain
---
On a word that presents no instance the reduction is the empty word: such a word is not valid.
-/
theorem reduce_off_domain_proved (x : List ℕ) (hx : x ∉ problem.Domain) : reduce x = [] :=
  reduce_invalid fun h => hx (valid_iff_mem.1 h)

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_off_domain := reduce_off_domain_proved

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.reduce_maps_domain
---
The image of the word of an instance is the word of the construction, which encodes it.
-/
theorem reduce_maps_domain_proved :
    ∀ x ∈ problem.Domain, reduce x ∈ Lax888481.MulticolouredClique.problem.Domain := by
  rintro x ⟨I, rfl⟩
  rw [reduce_word_eq]
  exact ⟨_, Lax496464Proofs.WHierarchy.MccNP.WordEncodesProof.word_encodes_proved I⟩

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.reduce_correct
---
Yes-instances go to yes-instances and no-instances to no-instances: both sides are the
correctness of the construction.
-/
theorem reduce_correct_proved :
    ∀ x ∈ problem.Domain, (problem.Yes x ↔ Lax888481.MulticolouredClique.problem.Yes (reduce x)) := by
  rintro x ⟨I, rfl⟩
  rw [reduce_word_eq, yes_word, mcc_yes_word]

/--
A word that presents no instance is not a yes-instance of Independent Set, and is sent to the
empty word, which is not a word of Multicoloured Clique at all.
-/
theorem reduce_reject_proved :
    ∀ x, x ∉ problem.Domain →
      ¬ problem.Yes x ∧ ¬ Lax888481.MulticolouredClique.problem.Yes (reduce x) := by
  intro x hx
  have hinv : ¬ Valid x := fun h => hx (valid_iff_mem.1 h)
  refine ⟨fun ⟨I, h, _⟩ => hx ⟨I, h.symm⟩, ?_⟩
  rw [reduce_invalid hinv]
  rintro ⟨G, ⟨g, hg, -⟩, -⟩
  simp at hg

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_word := reduce_word_proved
example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_maps_domain := reduce_maps_domain_proved
example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_correct := reduce_correct_proved

end Lax496464Proofs.WHierarchy.MccNP.ReductionCorrectProof
