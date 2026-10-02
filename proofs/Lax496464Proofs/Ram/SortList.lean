import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log

/-!
# Bottom-Up Merge Sort, on Lists

The machine sorts an array by passes: pass `k` merges neighbouring runs of length `2^k`.
This file is the pass and its two facts — a pass permutes, and a pass turns sorted runs of
width `w` into sorted runs of width `2w` — and the conclusion that `⌈log₂ n⌉` passes sort
a list of length `n`.
-/

namespace Lax496464Proofs.Ram.SortList

variable (r : ℕ → ℕ → Prop) [DecidableRel r]

/-- The comparison the merge uses. -/
abbrev cmp (a b : ℕ) : Bool := decide (r a b)

/-- One pass: merge the run of the first `w` entries with the run of the next `w`, and go on
from there. -/
def pass (w : ℕ) (l : List ℕ) : List ℕ :=
  if _h : l = [] ∨ w = 0 then l else
    (l.take w).merge ((l.drop w).take w) (cmp r) ++ pass w (l.drop (2 * w))
termination_by l.length
decreasing_by
  have h' := not_or.mp _h
  have hl : 0 < l.length := List.length_pos_iff.mpr h'.1
  have hw : 0 < w := Nat.pos_of_ne_zero h'.2
  simp only [List.length_drop]
  omega

/-- Every aligned run of `w` entries is sorted. -/
inductive Runs (w : ℕ) : List ℕ → Prop
  | nil : Runs w []
  | zero (l : List ℕ) : w = 0 → Runs w l
  | cons (l : List ℕ) : l ≠ [] → 0 < w → (l.take w).Pairwise r → Runs w (l.drop w) → Runs w l

theorem pass_nil (w : ℕ) : pass r w [] = [] := by
  rw [pass]; simp

theorem pass_zero (l : List ℕ) : pass r 0 l = l := by
  rw [pass]; simp

theorem pass_of_ne {w : ℕ} {l : List ℕ} (hw : 0 < w) (hl : l ≠ []) :
    pass r w l = (l.take w).merge ((l.drop w).take w) (cmp r) ++ pass r w (l.drop (2 * w)) := by
  rw [pass]; simp [hl, Nat.pos_iff_ne_zero.mp hw]

omit [DecidableRel r] in
theorem runs_inv {w : ℕ} {l : List ℕ} (hw : 0 < w) (hl : l ≠ []) (h : Runs r w l) :
    (l.take w).Pairwise r ∧ Runs r w (l.drop w) := by
  cases h with
  | nil => exact absurd rfl hl
  | zero _ h0 => omega
  | cons _ _ _ h1 h2 => exact ⟨h1, h2⟩

theorem pass_perm (w : ℕ) (l : List ℕ) : (pass r w l).Perm l := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [pass_zero]
  by_cases hl : l = []
  · subst hl; rw [pass_nil]
  rw [pass_of_ne r hw hl]
  have hlen : 0 < l.length := List.length_pos_iff.mpr hl
  have h1 := ih (l.drop (2 * w)).length (by simp only [List.length_drop]; omega) (l.drop (2 * w)) rfl
  refine ((List.merge_perm_append _).append h1).trans ?_
  have : l = l.take w ++ (l.drop w).take w ++ l.drop (2 * w) := by
    rw [List.append_assoc]
    conv_lhs => rw [← List.take_append_drop w l]
    congr 1
    conv_lhs => rw [← List.take_append_drop w (l.drop w)]
    rw [List.drop_drop, Nat.two_mul]
  conv_rhs => rw [this]

theorem runs_pass [IsTrans ℕ r] [Std.Total r] (w : ℕ) (l : List ℕ) (h : Runs r w l) :
    Runs r (2 * w) (pass r w l) := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact Runs.zero _ (by omega)
  by_cases hl : l = []
  · subst hl; rw [pass_nil]; exact Runs.nil
  obtain ⟨hA, hrest⟩ := runs_inv r hw hl h
  rw [pass_of_ne r hw hl]
  have hlen : 0 < l.length := List.length_pos_iff.mpr hl
  set M := (l.take w).merge ((l.drop w).take w) (cmp r) with hM
  have hBsorted : ((l.drop w).take w).Pairwise r := by
    by_cases hd : l.drop w = []
    · rw [hd]; simp
    · exact (runs_inv r hw hd hrest).1
  have hMs : M.Pairwise r := hA.merge hBsorted
  have hMlen : M.length = (l.take w).length + ((l.drop w).take w).length := List.length_merge _ _ _
  simp only [List.length_take, List.length_drop] at hMlen
  have hMle : M.length ≤ 2 * w := by omega
  have hrest2 : Runs r w (l.drop (2 * w)) := by
    by_cases hd : l.drop w = []
    · have : l.drop (2 * w) = [] := by
        rw [List.drop_eq_nil_iff] at hd ⊢; omega
      rw [this]; exact Runs.nil
    · have := (runs_inv r hw hd hrest).2
      rwa [List.drop_drop, ← Nat.two_mul] at this
  have hIH := ih (l.drop (2 * w)).length (by simp only [List.length_drop]; omega)
    (l.drop (2 * w)) hrest2 rfl
  by_cases hbig : l.drop (2 * w) = []
  · rw [hbig, pass_nil, List.append_nil]
    have hMne : M ≠ [] := List.length_pos_iff.mp (by omega)
    refine Runs.cons _ hMne (by omega) ?_ ?_
    · rwa [List.take_of_length_le hMle]
    · rw [List.drop_of_length_le hMle]; exact Runs.nil
  · have hMeq : M.length = 2 * w := by
      have : ¬ l.length ≤ 2 * w := by
        intro hc; apply hbig; rw [List.drop_eq_nil_iff]; exact hc
      omega
    have hne : M ++ pass r w (l.drop (2 * w)) ≠ [] := by
      intro h0
      have h1 : (M ++ pass r w (l.drop (2 * w))).length = 0 := by rw [h0]; rfl
      rw [List.length_append] at h1; omega
    refine Runs.cons _ hne (by omega) ?_ ?_
    · rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      exact hMs
    · have hd : (M ++ pass r w (l.drop (2 * w))).drop (2 * w) = pass r w (l.drop (2 * w)) := by
        have := List.drop_left (l₁ := M) (l₂ := pass r w (l.drop (2 * w)))
        rwa [hMeq] at this
      rw [hd]; exact hIH

/-- `k` passes, of widths `1, 2, 4, …`. -/
def iter (l : List ℕ) : ℕ → List ℕ
  | 0 => l
  | k + 1 => pass r (2 ^ k) (iter l k)

omit [DecidableRel r] in
theorem runs_one (l : List ℕ) : Runs r 1 l := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  by_cases hl : l = []
  · subst hl; exact Runs.nil
  refine Runs.cons _ hl (by omega) ?_ ?_
  · rcases l with _ | ⟨a, t⟩
    · exact absurd rfl hl
    · simp
  · exact ih (l.drop 1).length (by
      have : 0 < l.length := List.length_pos_iff.mpr hl
      simp only [List.length_drop]; omega) _ rfl

theorem iter_spec [IsTrans ℕ r] [Std.Total r] (l : List ℕ) (k : ℕ) :
    (iter r l k).Perm l ∧ Runs r (2 ^ k) (iter r l k) := by
  induction k with
  | zero => exact ⟨List.Perm.refl _, by simpa [iter] using runs_one r l⟩
  | succ k ih =>
    refine ⟨(pass_perm r _ _).trans ih.1, ?_⟩
    have := runs_pass r _ _ ih.2
    show Runs r (2 ^ (k + 1)) (pass r (2 ^ k) (iter r l k))
    rwa [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [Nat.pow_succ, Nat.mul_comm]]

/-- **`k` passes sort a list of length at most `2ᵏ`.** -/
theorem iter_sorted [IsTrans ℕ r] [Std.Total r] (l : List ℕ) (k : ℕ) (hk : l.length ≤ 2 ^ k) :
    (iter r l k).Perm l ∧ (iter r l k).Pairwise r := by
  obtain ⟨hp, hr⟩ := iter_spec r l k
  refine ⟨hp, ?_⟩
  have hlen : (iter r l k).length ≤ 2 ^ k := by rw [hp.length_eq]; exact hk
  by_cases h0 : iter r l k = []
  · rw [h0]; simp
  obtain ⟨h1, -⟩ := runs_inv r (Nat.two_pow_pos k) h0 hr
  rwa [List.take_of_length_le hlen] at h1

end Lax496464Proofs.Ram.SortList
