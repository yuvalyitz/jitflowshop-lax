import Lax496464.WH_F4_IndependentSetToMcc
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Correctness of the Multicoloured Graph

An independent set of at least `k` vertices contains `k` distinct pairwise non-adjacent vertices
`v_0, …, v_{k-1}`, and these correspond to the multicoloured cliques `{(c, v_c)}` of the
construction.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.CorrectnessProof

open Lax762056.GraphEncoding (Instance)
open Lax496464 Lax496464.WH_F2_MccConstruction

/-- `k ≤ indepNum` iff there is an injective family of `k` pairwise non-adjacent vertices. -/
theorem le_indepNum_iff {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    k ≤ G.indepNum ↔
      ∃ v : Fin k → Fin n, Function.Injective v ∧ ∀ c c', c ≠ c' → ¬ G.Adj (v c) (v c') := by
  constructor
  · intro hk
    obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (s := s) (n := k)
      (by rw [hs.card_eq]; exact hk)
    have hind : G.IsIndepSet (t : Set (Fin n)) := Set.Pairwise.mono (by exact_mod_cast hts) hs.isIndepSet
    let e : Fin k ≃ t := (Finset.equivFinOfCardEq htc).symm
    refine ⟨fun c => (e c : Fin n), ?_, ?_⟩
    · intro a b h
      exact e.injective (Subtype.ext h)
    · intro c c' hne
      have hne' : (e c : Fin n) ≠ (e c' : Fin n) := fun h => hne (e.injective (Subtype.ext h))
      exact hind (e c).2 (e c').2 hne'
  · rintro ⟨v, hinj, hadj⟩
    have hind : G.IsIndepSet ((Finset.univ.image v : Finset (Fin n)) : Set (Fin n)) := by
      intro a ha b hb hab
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨c', rfl⟩ := hb
      exact hadj c c' (fun h => hab (by rw [h]))
    have := hind.card_le_indepNum
    rwa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at this

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.construct_correct
---
`G` has an independent set of size at least `k` if and only if its multicoloured graph has a
multicoloured clique: the copies `(c, v_c)` of `k` pairwise different, pairwise non-adjacent
vertices form one, and conversely the vertices of a multicoloured clique are such a family.
-/
theorem construct_correct_proved (I : Instance) :
    Lax762056.GraphProblems.IndependentSet I ↔
      (WH_F2_MccConstruction.construct I).HasMulticolouredClique := by
  unfold Lax762056.GraphProblems.IndependentSet
  rw [le_indepNum_iff]
  constructor
  · rintro ⟨v, hinj, hadj⟩
    refine ⟨fun c => finProdFinEquiv (c, v c), ?_, ?_⟩
    · intro c
      simp [construct]
      rfl
    · intro c c' hne
      show WH_F2_MccConstruction.Adj I (finProdFinEquiv.symm (finProdFinEquiv (c, v c)))
        (finProdFinEquiv.symm (finProdFinEquiv (c', v c')))
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact ⟨hne, fun h => hne (hinj h), hadj c c' hne⟩
  · rintro ⟨f, hcol, hadj⟩
    refine ⟨fun c => (finProdFinEquiv.symm (f c)).2, ?_, ?_⟩
    · intro a b h
      by_contra hne
      have h1 := hadj a b hne
      have h2 : WH_F2_MccConstruction.Adj I (finProdFinEquiv.symm (f a)) (finProdFinEquiv.symm (f b)) := h1
      exact h2.2.1 h
    · intro c c' hne
      exact (hadj c c' hne).2.2

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.construct_correct := construct_correct_proved

end Lax496464Proofs.WHierarchy.MccNP.CorrectnessProof
