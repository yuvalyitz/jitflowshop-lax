import Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax

/-! # Negation elimination: free variables and fitting of the translation

The translation keeps every free variable and adds only fresh ones (`c ≤ v < c + cnt p φ`), and it
fits the expanded vocabulary exactly when the formula fits the old one. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.Vars

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Logic.SatFacts Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax

/-! ### Free variables -/

theorem mem_freeVars_lexF : ∀ {ys zs : List ℕ} {v : ℕ}, v ∈ (lexF ys zs).freeVars → v ∈ ys ∨ v ∈ zs
  | [], _, v, h => by simp [lexF, Formula.freeVars] at h
  | _ :: _, [], v, h => by simp [lexF, Formula.freeVars] at h
  | y :: ys, z :: zs, v, h => by
    unfold lexF at h
    split_ifs at h
    · simp [Formula.freeVars] at h; rcases h with rfl | rfl <;> simp
    · simp only [Formula.freeVars, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with (rfl | rfl) | (rfl | rfl) | h
      · simp
      · simp
      · simp
      · simp
      · rcases mem_freeVars_lexF h with h | h <;> simp [h]

theorem freeVars_lexF_left : ∀ {ys zs : List ℕ}, ys.length ≤ zs.length →
    ∀ v ∈ ys, v ∈ (lexF ys zs).freeVars
  | [], _, _, v, h => by simp at h
  | _ :: _, [], hl, v, _ => by simp at hl
  | y :: ys, z :: zs, hl, v, h => by
    unfold lexF
    split_ifs with hys
    · subst hys; simp at h; subst h; simp [Formula.freeVars]
    · rcases List.mem_cons.mp h with rfl | h
      · simp [Formula.freeVars]
      · have := freeVars_lexF_left (zs := zs) (by simp at hl; omega) v h
        simp [Formula.freeVars, this]

theorem mem_range'_iff {c r v : ℕ} : v ∈ List.range' c r ↔ c ≤ v ∧ v < c + r := by
  simp [List.mem_range'_1]

theorem mem_freeVars_negRel {i : ℕ} {ys : List ℕ} {c v : ℕ}
    (h : v ∈ (negRel i ys c).freeVars) : v ∈ ys ∨ (c ≤ v ∧ v < c + 2 * ys.length) := by
  unfold negRel at h
  split_ifs at h with hys
  · simp [Formula.freeVars] at h
  · have hr : ∀ {w : ℕ}, w ∈ List.range' c ys.length → c ≤ w ∧ w < c + 2 * ys.length := by
      intro w hw; rw [mem_range'_iff] at hw; omega
    have hr' : ∀ {w : ℕ}, w ∈ List.range' (c + ys.length) ys.length →
        c ≤ w ∧ w < c + 2 * ys.length := by
      intro w hw; rw [mem_range'_iff] at hw; omega
    simp only [Formula.freeVars, Finset.mem_union, List.mem_toFinset, List.mem_append,
      List.mem_singleton] at h
    rcases h with rfl | (h1 | h2) | ((h1 | h2) | h3 | h4) | h1 | h2
    · left; obtain ⟨y, ys', rfl⟩ := List.exists_cons_of_ne_nil hys; simp
    · exact Or.inr (hr h1)
    · rcases mem_freeVars_lexF h2 with h | h
      · exact Or.inl h
      · exact Or.inr (hr h)
    · exact Or.inr (hr h1)
    · exact Or.inr (hr' h2)
    · rcases mem_freeVars_lexF h3 with h | h
      · exact Or.inr (hr h)
      · exact Or.inl h
    · rcases mem_freeVars_lexF h4 with h | h
      · exact Or.inl h
      · exact Or.inr (hr' h)
    · exact Or.inr (hr' h1)
    · rcases mem_freeVars_lexF h2 with h | h
      · exact Or.inr (hr' h)
      · exact Or.inl h

theorem freeVars_negRel {i : ℕ} {ys : List ℕ} {c : ℕ} :
    ∀ v ∈ ys, v ∈ (negRel i ys c).freeVars := by
  intro v hv
  unfold negRel
  split_ifs with hys
  · subst hys; simp at hv
  · have := freeVars_lexF_left (zs := List.range' c ys.length) (by simp) v hv
    simp only [Formula.freeVars, Finset.mem_union]
    exact Or.inr (Or.inl (Or.inr this))

/-- **The translation adds only fresh variables.** -/
theorem mem_freeVars_tr : ∀ (p : Bool) (φ : Formula) (c : ℕ) {v : ℕ},
    v ∈ (tr p φ c).freeVars → v ∈ φ.freeVars ∨ (c ≤ v ∧ v < c + cnt p φ)
  | true, .rel _ _, _, v, h => Or.inl (by simpa [tr, Formula.freeVars] using h)
  | false, .rel i ys, c, v, h => by
    rcases mem_freeVars_negRel h with h | h
    · exact Or.inl (by simpa [Formula.freeVars] using h)
    · exact Or.inr (by simpa [cnt] using h)
  | true, .setVar _, _, v, h => Or.inl (by simpa [tr, Formula.freeVars] using h)
  | false, .setVar _, _, v, h => Or.inl (by simpa [tr, Formula.freeVars] using h)
  | true, .eq _ _, _, v, h => Or.inl (by simpa [tr, Formula.freeVars] using h)
  | false, .eq x y, _, v, h => by
    left; simp [tr, Formula.freeVars] at h ⊢; tauto
  | p, .neg φ, c, v, h => by
    simpa [tr, cnt, Formula.freeVars] using mem_freeVars_tr (!p) φ c (by simpa [tr] using h)
  | true, .and φ ψ, c, v, h => by
    simp only [tr, Formula.freeVars, Finset.mem_union] at h
    rcases h with h | h
    · rcases mem_freeVars_tr true φ c h with h | h
      · simp [Formula.freeVars, h]
      · right; simp [cnt]; omega
    · rcases mem_freeVars_tr true ψ _ h with h | h
      · simp [Formula.freeVars, h]
      · right; simp [cnt]; omega
  | false, .and φ ψ, c, v, h => by
    simp only [tr, Formula.freeVars, Finset.mem_union] at h
    rcases h with h | h
    · rcases mem_freeVars_tr false φ c h with h | h
      · simp [Formula.freeVars, h]
      · right; simp [cnt]; omega
    · rcases mem_freeVars_tr false ψ _ h with h | h
      · simp [Formula.freeVars, h]
      · right; simp [cnt]; omega
  | true, .or φ ψ, c, v, h => by
    simp only [tr, Formula.freeVars, Finset.mem_union] at h
    rcases h with h | h
    · rcases mem_freeVars_tr true φ c h with h | h
      · simp [Formula.freeVars, h]
      · right; simp [cnt]; omega
    · rcases mem_freeVars_tr true ψ _ h with h | h
      · simp [Formula.freeVars, h]
      · right; simp [cnt]; omega
  | false, .or φ ψ, c, v, h => by
    simp only [tr, Formula.freeVars, Finset.mem_union] at h
    rcases h with h | h
    · rcases mem_freeVars_tr false φ c h with h | h
      · simp [Formula.freeVars, h]
      · right; simp [cnt]; omega
    · rcases mem_freeVars_tr false ψ _ h with h | h
      · simp [Formula.freeVars, h]
      · right; simp [cnt]; omega
  | p, .ex x φ, c, v, h => by
    cases p <;>
    · simp only [tr, Formula.freeVars, Finset.mem_erase] at h
      rcases mem_freeVars_tr _ φ c h.2 with h' | h'
      · simp [Formula.freeVars, h.1, h']
      · right; simpa [cnt] using h'
  | p, .all x φ, c, v, h => by
    cases p <;>
    · simp only [tr, Formula.freeVars, Finset.mem_erase] at h
      rcases mem_freeVars_tr _ φ c h.2 with h' | h'
      · simp [Formula.freeVars, h.1, h']
      · right; simpa [cnt] using h'

/-- **The translation keeps every free variable.** -/
theorem freeVars_sub_tr : ∀ (p : Bool) (φ : Formula) (c : ℕ) {v : ℕ},
    v ∈ φ.freeVars → v ∈ (tr p φ c).freeVars
  | true, .rel _ _, _, v, h => by simpa [tr, Formula.freeVars] using h
  | false, .rel i ys, c, v, h => freeVars_negRel v (by simpa [Formula.freeVars] using h)
  | true, .setVar _, _, v, h => by simpa [tr, Formula.freeVars] using h
  | false, .setVar _, _, v, h => by simpa [tr, Formula.freeVars] using h
  | true, .eq _ _, _, v, h => by simpa [tr, Formula.freeVars] using h
  | false, .eq x y, _, v, h => by simp [tr, Formula.freeVars] at h ⊢; tauto
  | p, .neg φ, c, v, h => by
    simpa [tr] using freeVars_sub_tr (!p) φ c (by simpa [Formula.freeVars] using h)
  | true, .and φ ψ, c, v, h => by
    simp only [tr, Formula.freeVars, Finset.mem_union] at h ⊢
    exact h.imp (freeVars_sub_tr _ _ _) (freeVars_sub_tr _ _ _)
  | false, .and φ ψ, c, v, h => by
    simp only [tr, Formula.freeVars, Finset.mem_union] at h ⊢
    exact h.imp (freeVars_sub_tr _ _ _) (freeVars_sub_tr _ _ _)
  | true, .or φ ψ, c, v, h => by
    simp only [tr, Formula.freeVars, Finset.mem_union] at h ⊢
    exact h.imp (freeVars_sub_tr _ _ _) (freeVars_sub_tr _ _ _)
  | false, .or φ ψ, c, v, h => by
    simp only [tr, Formula.freeVars, Finset.mem_union] at h ⊢
    exact h.imp (freeVars_sub_tr _ _ _) (freeVars_sub_tr _ _ _)
  | p, .ex x φ, c, v, h => by
    cases p <;>
    · simp only [tr, Formula.freeVars, Finset.mem_erase] at h ⊢
      exact ⟨h.1, freeVars_sub_tr _ _ _ h.2⟩
  | p, .all x φ, c, v, h => by
    cases p <;>
    · simp only [tr, Formula.freeVars, Finset.mem_erase] at h ⊢
      exact ⟨h.1, freeVars_sub_tr _ _ _ h.2⟩

/-! ### Fitting the expanded vocabulary -/

/-- `as'` is the expanded vocabulary of `as`: the order `<` (arity `2`), then five symbols per old
symbol. -/
structure ExtAr (as as' : List ℕ) : Prop where
  len : as'.length = 5 * as.length + 1
  zero : as'.getD 0 0 = 2
  blk : ∀ i < as.length, ∀ j < 5, as'.getD (5 * i + 1 + j) 0 = (arBlk (as.getD i 0)).getD j 0

variable {as as' : List ℕ}

theorem ExtAr.zero' (h : ExtAr as as') (h0 : 0 < as'.length) : as'[0] = 2 := by
  have := h.zero
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0, Option.getD_some] at this

theorem fits_lexF (h : ExtAr as as') : ∀ {ys zs : List ℕ}, ys.length = zs.length → ys ≠ [] →
    (lexF ys zs).Fits as' 0
  | [], _, _, hne => (hne rfl).elim
  | _ :: _, [], hl, _ => by simp at hl
  | y :: ys, z :: zs, hl, _ => by
    have h0 : 0 < as'.length := by rw [h.len]; omega
    unfold lexF
    split_ifs with hys
    · exact ⟨h0, by rw [h.zero]; rfl⟩
    · exact ⟨⟨h0, by rw [h.zero]; rfl⟩, trivial, fits_lexF h (by simpa using hl) hys⟩

theorem fits_rel_iff (h : ExtAr as as') (i j : ℕ) (hj : j < 5) (ys : List ℕ) :
    (Formula.rel (5 * i + 1 + j) ys).Fits as' 0 ↔
      i < as.length ∧ ys.length = (arBlk (as.getD i 0)).getD j 0 := by
  simp only [Formula.Fits]
  by_cases hi : i < as.length
  · rw [h.blk i hi j hj, h.len]; simp only [hi, true_and]; omega
  · rw [h.len]; simp only [hi, false_and, iff_false, not_and]; intro h'; omega

theorem fits_negRel_iff (h : ExtAr as as') (i : ℕ) (ys : List ℕ) (c : ℕ) :
    (negRel i ys c).Fits as' 0 ↔ i < as.length ∧ ys.length = as.getD i 0 := by
  unfold negRel
  split_ifs with hys
  · subst hys
    rw [show fI i = 5 * i + 1 + 1 by unfold fI; ring, fits_rel_iff h i 1 (by norm_num)]
    simp only [arBlk, List.length_nil, List.getD_cons_succ, List.getD_cons_zero]
  · have e1 : zI i = 5 * i + 1 + 4 := by unfold zI; ring
    have e2 : fI i = 5 * i + 1 + 1 := by unfold fI; ring
    have e3 : sI i = 5 * i + 1 + 3 := by unfold sI; ring
    have e4 : lI i = 5 * i + 1 + 2 := by unfold lI; ring
    have hne : List.range' c ys.length ≠ [] := by simpa using hys
    have hne' : List.range' (c + ys.length) ys.length ≠ [] := by simpa using hys
    have l1 := fits_lexF h (ys := ys) (zs := List.range' c ys.length) (by simp) hys
    have l2 := fits_lexF h (ys := List.range' c ys.length) (zs := ys) (by simp) hne
    have l3 := fits_lexF h (ys := ys) (zs := List.range' (c + ys.length) ys.length) (by simp) hys
    have l4 := fits_lexF h (ys := List.range' (c + ys.length) ys.length) (zs := ys) (by simp) hne'
    rw [e1, e2, e3, e4]
    simp only [Formula.Fits, l1, l2, l3, l4, and_true, List.length_cons, List.length_nil,
      List.length_range', List.length_append]
    by_cases hi : i < as.length
    · have b4 := h.blk i hi 4 (by decide)
      have b1 := h.blk i hi 1 (by decide)
      have b3 := h.blk i hi 3 (by decide)
      have b2 := h.blk i hi 2 (by decide)
      rw [b4, b1, b3, b2, h.len]
      simp only [arBlk, List.getD_cons_succ, List.getD_cons_zero]
      constructor
      · rintro ⟨-, ⟨-, h1⟩, -⟩; exact ⟨hi, h1⟩
      · rintro ⟨-, h1⟩
        exact ⟨⟨by omega, trivial⟩, ⟨by omega, h1⟩, ⟨by omega, by omega⟩, by omega, h1⟩
    · rw [h.len]; simp only [hi, false_and, iff_false]; rintro ⟨⟨h1, -⟩, -⟩; omega

/-- **The translation fits the expanded vocabulary exactly when the formula fits the old one.** -/
theorem fits_tr_iff (h : ExtAr as as') : ∀ (p : Bool) (φ : Formula) (c : ℕ),
    (tr p φ c).Fits as' 0 ↔ φ.Fits as 0
  | true, .rel i ys, _ => by
    rw [tr, rI, fits_rel_iff h i 0 (by norm_num)]; simp [arBlk, Formula.Fits]
  | false, .rel i ys, c => by rw [tr, fits_negRel_iff h]; rfl
  | true, .setVar _, _ => Iff.rfl
  | false, .setVar _, _ => Iff.rfl
  | true, .eq _ _, _ => Iff.rfl
  | false, .eq _ _, _ => by
    have h0 : 0 < as'.length := by rw [h.len]; omega
    simp [tr, Formula.Fits, h0, h.zero' h0]
  | p, .neg φ, c => by rw [tr]; exact fits_tr_iff h (!p) φ c
  | true, .and φ ψ, c => and_congr (fits_tr_iff h _ φ _) (fits_tr_iff h _ ψ _)
  | false, .and φ ψ, c => and_congr (fits_tr_iff h _ φ _) (fits_tr_iff h _ ψ _)
  | true, .or φ ψ, c => and_congr (fits_tr_iff h _ φ _) (fits_tr_iff h _ ψ _)
  | false, .or φ ψ, c => and_congr (fits_tr_iff h _ φ _) (fits_tr_iff h _ ψ _)
  | true, .ex _ φ, c => fits_tr_iff h _ φ _
  | false, .ex _ φ, c => fits_tr_iff h _ φ _
  | true, .all _ φ, c => fits_tr_iff h _ φ _
  | false, .all _ φ, c => fits_tr_iff h _ φ _

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.Vars
