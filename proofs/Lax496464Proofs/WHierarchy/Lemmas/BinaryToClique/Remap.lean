import Lax496464.WH_B3_LogicProblems
import Mathlib.Tactic

/-!
# Σ₁[2] Model Checking to Clique: Few Candidate Values Suffice

The universe of a structure may be far larger than its word (its size is one number), so the
graph cannot have a vertex per universe element. It does not need one: elements that occur in no
tuple are interchangeable. If `E` contains every element of the universe that occurs in the word,
and every element below `M`, where `M` exceeds the number of entries of the word by the number of
variables, then a quantifier-free formula satisfiable in the universe is satisfiable with values in
`E`: the values of the assignment outside the word are moved, injectively, to unused elements
below `M`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Remap

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder

/-- **A map fixing the tuple entries and injective on the values of the assignment preserves
quantifier-free formulas.** -/
theorem sat_comp_iff (A : Structure) (π : ℕ → ℕ) (V : Set ℕ)
    (hfix : ∀ a ∈ V, (∃ i, ∃ t ∈ A.rel i, a ∈ t) → π a = a)
    (hout : ∀ a ∈ V, (¬ ∃ i, ∃ t ∈ A.rel i, a ∈ t) → ¬ ∃ i, ∃ t ∈ A.rel i, π a ∈ t)
    (hinj : ∀ a ∈ V, ∀ b ∈ V, π a = π b → a = b) :
    ∀ (ψ : Formula), ψ.IsQF → ∀ ρ : ℕ → ℕ, (∀ v ∈ ψ.freeVars, ρ v ∈ V) →
      (Sat A ∅ ψ (fun v => π (ρ v)) ↔ Sat A ∅ ψ ρ)
  | .rel i xs, _, ρ, hV => by
    simp only [Sat]
    have hV' : ∀ v ∈ xs, ρ v ∈ V := fun v hv => hV v (by simp [Formula.freeVars, hv])
    constructor
    · intro h
      have : xs.map (fun v => π (ρ v)) = xs.map ρ := by
        apply List.map_congr_left
        intro v hv
        by_contra hne
        have hnot : ¬ ∃ i, ∃ t ∈ A.rel i, ρ v ∈ t := fun hin => hne (hfix _ (hV' v hv) hin)
        exact hout _ (hV' v hv) hnot ⟨i, _, h, List.mem_map.2 ⟨v, hv, rfl⟩⟩
      rwa [this] at h
    · intro h
      have : xs.map (fun v => π (ρ v)) = xs.map ρ :=
        List.map_congr_left fun v hv => hfix _ (hV' v hv) ⟨i, _, h, List.mem_map.2 ⟨v, hv, rfl⟩⟩
      rwa [this]
  | .setVar xs, _, ρ, _ => by simp [Sat]
  | .eq a b, _, ρ, hV => by
    simp only [Sat]
    exact ⟨hinj _ (hV a (by simp [Formula.freeVars])) _ (hV b (by simp [Formula.freeVars])),
      fun h => by rw [h]⟩
  | .neg φ, hq, ρ, hV => by
    simp only [Sat]
    rw [sat_comp_iff A π V hfix hout hinj φ hq ρ hV]
  | .and φ ψ, hq, ρ, hV => by
    simp only [Sat]
    rw [sat_comp_iff A π V hfix hout hinj φ hq.1 ρ fun v hv => hV v (by simp [Formula.freeVars, hv]),
      sat_comp_iff A π V hfix hout hinj ψ hq.2 ρ fun v hv => hV v (by simp [Formula.freeVars, hv])]
  | .or φ ψ, hq, ρ, hV => by
    simp only [Sat]
    rw [sat_comp_iff A π V hfix hout hinj φ hq.1 ρ fun v hv => hV v (by simp [Formula.freeVars, hv]),
      sat_comp_iff A π V hfix hout hinj ψ hq.2 ρ fun v hv => hV v (by simp [Formula.freeVars, hv])]
  | .ex _ _, hq, _, _ => absurd hq id
  | .all _ _, hq, _, _ => absurd hq id

open Classical in
/-- **Few candidates suffice.** `Uf` contains the tuple entries; `E` contains the elements of `Uf`
in the universe and every element below both `N` and `M`, and `M` is at least the size of `Uf` plus
the number of variables. -/
theorem exists_remap (A : Structure) (ψ : Formula) (hqf : ψ.IsQF) (M : ℕ) (E : Set ℕ)
    (Uf : Finset ℕ) (hU : ∀ i, ∀ t ∈ A.rel i, ∀ a ∈ t, a ∈ Uf)
    (hUE : ∀ a ∈ Uf, a < A.size → a ∈ E) (hrange : ∀ a, a < A.size → a < M → a ∈ E)
    (hM : Uf.card + ψ.freeVars.card ≤ M) {ρ : ℕ → ℕ} (hρ : ∀ v ∈ ψ.freeVars, ρ v < A.size)
    (hsat : Sat A ∅ ψ ρ) : ∃ ρ' : ℕ → ℕ, (∀ v ∈ ψ.freeVars, ρ' v ∈ E) ∧ Sat A ∅ ψ ρ' := by
  by_cases hNM : A.size ≤ M
  · exact ⟨ρ, fun v hv => hrange _ (hρ v hv) (by have := hρ v hv; omega), hsat⟩
  push Not at hNM
  set Vals := ψ.freeVars.image ρ with hVals
  set Fr := Vals.filter (fun a => a ∉ Uf) with hFr
  set Av := (Finset.range M).filter (fun a => a ∉ Uf) with hAv
  have hcardFr : Fr.card ≤ Av.card := by
    have h1 : Fr.card ≤ ψ.freeVars.card :=
      (Finset.card_filter_le _ _).trans Finset.card_image_le
    have h2 : M - Uf.card ≤ Av.card := by
      have hsplit : Av.card + ((Finset.range M).filter (fun a => ¬ (a ∉ Uf))).card = M := by
        rw [hAv, Finset.card_filter_add_card_filter_not, Finset.card_range]
      have h3 : ((Finset.range M).filter (fun a => ¬ (a ∉ Uf))).card ≤ Uf.card := by
        apply Finset.card_le_card
        intro a ha
        simp only [Finset.mem_filter, not_not] at ha
        exact ha.2
      omega
    omega
  obtain ⟨f⟩ : Nonempty (Fr ↪ Av) := Function.Embedding.nonempty_of_card_le (by simpa using hcardFr)
  let π : ℕ → ℕ := fun a => if h : a ∈ Fr then (f ⟨a, h⟩ : ℕ) else a
  have hπFr : ∀ a (h : a ∈ Fr), π a ∈ Av := fun a h => by
    simp only [π, dif_pos h]; exact (f ⟨a, h⟩).2
  have hπnot : ∀ a, a ∉ Fr → π a = a := fun a h => by simp only [π, dif_neg h]
  have hAvU : ∀ b ∈ Av, b ∉ Uf := fun b hb => (Finset.mem_filter.1 hb).2
  have hAvM : ∀ b ∈ Av, b < M := fun b hb => Finset.mem_range.1 (Finset.mem_filter.1 hb).1
  have hValsU : ∀ a ∈ Vals, a ∉ Fr → a ∈ Uf := fun a ha hn => by
    by_contra hU'
    exact hn (Finset.mem_filter.2 ⟨ha, hU'⟩)
  have hUfU : ∀ a, (∃ i, ∃ t ∈ A.rel i, a ∈ t) → a ∈ Uf := fun a ⟨i, t, ht, hat⟩ =>
    hU i t ht a hat
  have hsat' := sat_comp_iff A π ↑Vals
    (fun a _ hin => hπnot a fun hF => (Finset.mem_filter.1 hF).2 (hUfU a hin))
    (fun a ha hnot hin => by
      by_cases hF : a ∈ Fr
      · exact hAvU _ (hπFr a hF) (hUfU _ hin)
      · rw [hπnot a hF] at hin; exact hnot hin)
    (fun a ha b hb hab => by
      by_cases hFa : a ∈ Fr <;> by_cases hFb : b ∈ Fr
      · have : f ⟨a, hFa⟩ = f ⟨b, hFb⟩ := by
          apply Subtype.ext
          simp only [π, dif_pos hFa, dif_pos hFb] at hab
          exact hab
        exact congrArg Subtype.val (f.injective this)
      · exfalso
        rw [hπnot b hFb] at hab
        exact hAvU _ (hπFr a hFa) (hab ▸ hValsU b hb hFb)
      · exfalso
        rw [hπnot a hFa] at hab
        exact hAvU _ (hπFr b hFb) (hab ▸ hValsU a ha hFa)
      · rwa [hπnot a hFa, hπnot b hFb] at hab)
    ψ hqf ρ (fun v hv => Finset.mem_coe.2 (Finset.mem_image_of_mem ρ hv))
  refine ⟨fun v => π (ρ v), fun v hv => ?_, hsat'.2 hsat⟩
  have hmem : ρ v ∈ Vals := Finset.mem_image_of_mem ρ hv
  by_cases hF : ρ v ∈ Fr
  · have hb := hπFr _ hF
    show π (ρ v) ∈ E
    exact hrange _ (by have := hAvM _ hb; omega) (hAvM _ hb)
  · show π (ρ v) ∈ E
    rw [hπnot _ hF]
    exact hUE _ (hValsU _ hmem hF) (hρ v hv)

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Remap
