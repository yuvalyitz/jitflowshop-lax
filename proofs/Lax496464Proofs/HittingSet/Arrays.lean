import Lax496464Proofs.HittingSet.Correct
import Lax391470Proofs.L2ScanModel

/-!
# Positions and Clauses

The scan presents a formula as its literals in order with the clause number of each. A
literal belongs to clause `c` exactly when it stands at a position whose clause number
is `c`.
-/

namespace Lax496464Proofs.HittingSet.Arrays

open Lax429075.CNF Lax391470Proofs.L2ScanModel

/-- The literals of a formula paired with their clause numbers. -/
def tagged (F : Formula) : List (ℕ × Literal) := (cn F).zip (lits F)

theorem tagged_append (d : List Clause) (C : Clause) :
    tagged (d ++ [C]) = tagged d ++ (List.replicate C.length d.length).zip C := by
  unfold tagged
  rw [cn_append, lits_append, List.zip_append (by rw [cn_length])]

theorem mem_zip_replicate {C : Clause} {n j c : ℕ} {l : Literal} (hn : n = C.length) :
    (c, l) ∈ (List.replicate n j).zip C ↔ c = j ∧ l ∈ C := by
  subst hn
  induction C with
  | nil => simp
  | cons a t ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.mem_cons,
        Prod.mk.injEq, ih]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, h⟩) <;> simp [*]
      · rintro ⟨rfl, h | h⟩ <;> simp [*]

theorem mem_cn_lt (d : List Clause) {x : ℕ} (hx : x ∈ cn d) : x < d.length := by
  induction d using List.reverseRecOn with
  | nil => simp [cn] at hx
  | append_singleton d C ih =>
      rw [cn_append, List.mem_append, List.mem_replicate] at hx
      rw [List.length_append, List.length_singleton]
      rcases hx with h | ⟨-, rfl⟩
      · have := ih h; omega
      · omega

/-- A literal is in clause `c` exactly when some position carries it with clause number
`c`. -/
theorem mem_getD_iff_tagged (F : Formula) {c : ℕ} (hc : c < F.length) (l : Literal) :
    l ∈ F.getD c [] ↔ (c, l) ∈ tagged F := by
  induction F using List.reverseRecOn with
  | nil => simp at hc
  | append_singleton d C ih =>
      rw [tagged_append, List.mem_append, mem_zip_replicate rfl]
      rw [List.length_append, List.length_singleton] at hc
      by_cases hcd : c < d.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hcd,
          ← List.getD_eq_getElem?_getD, ih hcd]
        constructor
        · exact Or.inl
        · rintro (h | ⟨rfl, -⟩)
          · exact h
          · omega
      · have hce : c = d.length := by omega
        subst hce
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.getD_some, true_and]
        constructor
        · exact Or.inr
        · rintro (h | h)
          · exfalso
            have := mem_cn_lt d (List.of_mem_zip h).1
            omega
          · exact h

/-- ... in terms of positions. -/
theorem mem_tagged_iff (F : Formula) (c : ℕ) (l : Literal) :
    (c, l) ∈ tagged F ↔
      ∃ p, ∃ hp : p < (lits F).length,
        (cn F)[p]'(by rw [cn_length]; exact hp) = c ∧ (lits F)[p] = l := by
  unfold tagged
  rw [List.mem_iff_getElem]
  have hlen : ((cn F).zip (lits F)).length = (lits F).length := by
    rw [List.length_zip, cn_length, Nat.min_self]
  constructor
  · rintro ⟨i, hi, hget⟩
    rw [List.getElem_zip] at hget
    exact ⟨i, by rw [hlen] at hi; exact hi, (Prod.mk.inj hget).1, (Prod.mk.inj hget).2⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, by rw [hlen]; exact hp, by rw [List.getElem_zip]; exact Prod.ext h1 h2⟩

theorem mem_getD_iff_pos (F : Formula) {c : ℕ} (hc : c < F.length) (l : Literal) :
    l ∈ F.getD c [] ↔
      ∃ p < (lits F).length, (cn F).getD p 0 = c ∧ (lits F).getD p ⟨0, false⟩ = l := by
  rw [mem_getD_iff_tagged F hc, mem_tagged_iff]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, hp, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [cn_length]; exact hp)]; exact h1
    · rw [List.getD_eq_getElem _ _ hp]; exact h2
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, hp, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [cn_length]; exact hp)] at h1; exact h1
    · rw [List.getD_eq_getElem _ _ hp] at h2; exact h2

end Lax496464Proofs.HittingSet.Arrays
