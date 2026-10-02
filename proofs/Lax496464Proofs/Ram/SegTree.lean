import Mathlib.Data.Nat.Size
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# A Maximum Tree, as a Pure List

A word RAM keeps a set of jobs, each with a key, in a *maximum tree* over `N = 2^h` leaves:
an array `T` of `2N` cells whose cell `i` (`1 ≤ i < N`) is the larger of cells `2i` and
`2i+1`, and whose leaves, the cells `N … 2N-1`, hold the keys (`0` for an absent job). This
file is the arithmetic of that array with no machine in it:

* `Cons T h` — the array has the shape of a tree;
* `Cons.leaf_le_root` — every leaf is at most the root (the maximum of the keys);
* `ConsExc` — the shape *except along the ancestors of one leaf from level `t` up*, the
  invariant of the pass that re-establishes the shape after a leaf changed;
* `ConsExc.step` / `ConsExc.base` / `ConsExc.final` — one repair step, the start, the end.
-/

namespace Lax496464Proofs.Ram.SegTree

/-- `T` is a maximum tree over `2^h` leaves. -/
def Cons (T : List ℕ) (h : ℕ) : Prop :=
  T.length = 2 * 2 ^ h ∧ ∀ i, 1 ≤ i → i < 2 ^ h →
    T.getD i 0 = max (T.getD (2 * i) 0) (T.getD (2 * i + 1) 0)

theorem getD_set_ne {T : List ℕ} {i j x : ℕ} (h : i ≠ j) : (T.set i x).getD j 0 = T.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]

theorem getD_set_self {T : List ℕ} {i x : ℕ} (h : i < T.length) : (T.set i x).getD i 0 = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]; rfl

/-- The ancestor of `ℓ`, `t` levels up. -/
def anc (ℓ t : ℕ) : ℕ := ℓ / 2 ^ t

theorem anc_zero (ℓ : ℕ) : anc ℓ 0 = ℓ := by simp [anc]

theorem anc_succ (ℓ t : ℕ) : anc ℓ (t + 1) = anc ℓ t / 2 := by
  unfold anc; rw [pow_succ, ← Nat.div_div_eq_div_mul]

theorem anc_le (ℓ t : ℕ) : anc ℓ t ≤ ℓ := Nat.div_le_self _ _

theorem anc_anti {ℓ s t : ℕ} (h : s ≤ t) : anc ℓ t ≤ anc ℓ s :=
  Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) h) (by positivity)

/-- A cell is the maximum of its two children, so no child exceeds its parent. -/
theorem Cons.child_le {T : List ℕ} {h : ℕ} (hc : Cons T h) {u : ℕ} (hu1 : 2 ≤ u)
    (hu2 : u < 2 * 2 ^ h) : T.getD u 0 ≤ T.getD (u / 2) 0 := by
  have hv1 : 1 ≤ u / 2 := by omega
  have hv2 : u / 2 < 2 ^ h := by omega
  have := hc.2 (u / 2) hv1 hv2
  rcases Nat.even_or_odd' u with ⟨k, hk | hk⟩
  · have hd : u / 2 = k := by omega
    rw [hd] at this ⊢
    rw [this]; rw [hk]; exact le_max_left _ _
  · have hd : u / 2 = k := by omega
    rw [hd] at this ⊢
    rw [this]; rw [hk]; exact le_max_right _ _

/-- **Every leaf is below the root.** -/
theorem Cons.leaf_le_anc {T : List ℕ} {h : ℕ} (hc : Cons T h) {ℓ : ℕ} (hℓ : ℓ < 2 * 2 ^ h) :
    ∀ t, 1 ≤ anc ℓ t → T.getD ℓ 0 ≤ T.getD (anc ℓ t) 0 := by
  intro t
  induction t with
  | zero => intro _; rw [anc_zero]
  | succ t ih =>
    intro h1
    rw [anc_succ] at h1 ⊢
    have h2 : 2 ≤ anc ℓ t := by omega
    have h3 := ih (by omega)
    have h4 : anc ℓ t < 2 * 2 ^ h := lt_of_le_of_lt (anc_le ℓ t) hℓ
    exact h3.trans (hc.child_le h2 h4)

theorem anc_root {ℓ h : ℕ} (h1 : 2 ^ h ≤ ℓ) (h2 : ℓ < 2 * 2 ^ h) : anc ℓ h = 1 := by
  unfold anc
  apply le_antisymm
  · have : ℓ / 2 ^ h < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; omega
    omega
  · exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)

theorem Cons.leaf_le_root {T : List ℕ} {h : ℕ} (hc : Cons T h) {ℓ : ℕ} (h1 : 2 ^ h ≤ ℓ)
    (h2 : ℓ < 2 * 2 ^ h) : T.getD ℓ 0 ≤ T.getD 1 0 := by
  have := hc.leaf_le_anc h2 h (by rw [anc_root h1 h2])
  rwa [anc_root h1 h2] at this

/-- **The descent step.** From a cell that is the root's value, one of its two children is
too, and the choice "right if it equals, else left" is right. -/
theorem Cons.descend {T : List ℕ} {h : ℕ} (hc : Cons T h) {i : ℕ} (hi1 : 1 ≤ i)
    (hi2 : i < 2 ^ h) :
    (T.getD (2 * i + 1) 0 = T.getD i 0 → T.getD (2 * i + 1) 0 = T.getD i 0) ∧
      (T.getD (2 * i + 1) 0 ≠ T.getD i 0 → T.getD (2 * i) 0 = T.getD i 0) := by
  refine ⟨id, fun hne => ?_⟩
  have := hc.2 i hi1 hi2
  rcases le_total (T.getD (2 * i) 0) (T.getD (2 * i + 1) 0) with hl | hl
  · rw [max_eq_right hl] at this; exact absurd this.symm hne
  · rw [max_eq_left hl] at this; exact this.symm

/-- **Some leaf holds the root's value.** -/
theorem Cons.exists_leaf {T : List ℕ} {h : ℕ} (hc : Cons T h) :
    ∃ i, 2 ^ h ≤ i ∧ i < 2 * 2 ^ h ∧ T.getD i 0 = T.getD 1 0 := by
  have key : ∀ t, t ≤ h → ∃ i, 2 ^ t ≤ i ∧ i < 2 ^ (t + 1) ∧ T.getD i 0 = T.getD 1 0 := by
    intro t
    induction t with
    | zero => intro _; exact ⟨1, by simp, by simp, rfl⟩
    | succ t ih =>
      intro ht
      obtain ⟨i, hi1, hi2, hiv⟩ := ih (by omega)
      have hpow : 2 ^ (t + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) ht
      have hpos : 1 ≤ 2 ^ t := Nat.one_le_two_pow
      have hpp : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
      have hpp2 : 2 ^ (t + 1 + 1) = 2 * 2 ^ (t + 1) := by ring
      have hi1' : 1 ≤ i := by omega
      have hi2' : i < 2 ^ h := by omega
      have hm := hc.2 i hi1' hi2'
      rcases le_total (T.getD (2 * i) 0) (T.getD (2 * i + 1) 0) with hl | hl
      · rw [max_eq_right hl] at hm
        exact ⟨2 * i + 1, by omega, by omega, by rw [← hm]; exact hiv⟩
      · rw [max_eq_left hl] at hm
        exact ⟨2 * i, by omega, by omega, by rw [← hm]; exact hiv⟩
  obtain ⟨i, h1, h2, h3⟩ := key h le_rfl
  exact ⟨i, h1, by rw [← pow_succ'] ; exact h2, h3⟩

/-! ## Repairing the shape after one leaf changed -/

/-- The shape everywhere except at the ancestors of `ℓ` from level `t` upward. -/
def ConsExc (T : List ℕ) (h ℓ t : ℕ) : Prop :=
  T.length = 2 * 2 ^ h ∧ ∀ v, 1 ≤ v → v < 2 ^ h → (¬ ∃ s, t ≤ s ∧ anc ℓ s = v) →
    T.getD v 0 = max (T.getD (2 * v) 0) (T.getD (2 * v + 1) 0)

theorem ConsExc.final {T : List ℕ} {h ℓ : ℕ} (hℓ : ℓ < 2 * 2 ^ h)
    (hc : ConsExc T h ℓ (h + 1)) : Cons T h := by
  refine ⟨hc.1, fun v hv1 hv2 => hc.2 v hv1 hv2 ?_⟩
  rintro ⟨s, hs, hsv⟩
  have h0 : anc ℓ s = 0 := by
    unfold anc
    rw [Nat.div_eq_of_lt]
    calc ℓ < 2 * 2 ^ h := hℓ
      _ = 2 ^ (h + 1) := by ring
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs
  omega

/-- **The start.** Changing one leaf of a tree leaves it in shape except above that leaf. -/
theorem ConsExc.base {T : List ℕ} {h : ℕ} (hc : Cons T h) {ℓ x : ℕ} (h1 : 2 ^ h ≤ ℓ)
    (_h2 : ℓ < 2 * 2 ^ h) : ConsExc (T.set ℓ x) h ℓ 1 := by
  refine ⟨by simp [hc.1], fun v hv1 hv2 hne => ?_⟩
  have hv2' : v < ℓ := by omega
  have hc1 : 2 * v ≠ ℓ := by
    intro he; apply hne; exact ⟨1, le_rfl, by rw [anc_succ, anc_zero]; omega⟩
  have hc2 : 2 * v + 1 ≠ ℓ := by
    intro he; apply hne; exact ⟨1, le_rfl, by rw [anc_succ, anc_zero]; omega⟩
  have hne1 : ℓ ≠ v := by omega
  rw [getD_set_ne hne1, getD_set_ne (Ne.symm hc1), getD_set_ne (Ne.symm hc2)]
  exact hc.2 v hv1 hv2

/-- **One repair step**: recompute the ancestor `anc ℓ t` from its children. -/
theorem ConsExc.step {T : List ℕ} {h ℓ t : ℕ} (hc : ConsExc T h ℓ t) (ht : 1 ≤ t)
    (hℓ : ℓ < 2 * 2 ^ h) (_hi1 : 1 ≤ anc ℓ t) :
    ConsExc (T.set (anc ℓ t) (max (T.getD (2 * anc ℓ t) 0) (T.getD (2 * anc ℓ t + 1) 0)))
      h ℓ (t + 1) := by
  have hi2 : anc ℓ t < 2 ^ h := by
    have h1 : anc ℓ t ≤ anc ℓ 1 := anc_anti ht
    have h2 : anc ℓ 1 = ℓ / 2 := by rw [anc_succ, anc_zero]
    omega
  set i := anc ℓ t with hi
  have hlen : (T.set i (max (T.getD (2 * i) 0) (T.getD (2 * i + 1) 0))).length = T.length := by
    simp
  refine ⟨by rw [hlen]; exact hc.1, fun v hv1 hv2 hne => ?_⟩
  by_cases hvi : v = i
  · have h2i : i ≠ 2 * i := by omega
    have h2i1 : i ≠ 2 * i + 1 := by omega
    rw [hvi, getD_set_self (by rw [hc.1]; omega), getD_set_ne h2i, getD_set_ne h2i1]
  · have hne' : ¬ ∃ s, t ≤ s ∧ anc ℓ s = v := by
      rintro ⟨s, hs, hsv⟩
      rcases Nat.eq_or_lt_of_le hs with rfl | hlt
      · exact hvi hsv.symm
      · exact hne ⟨s, hlt, hsv⟩
    have hc1 : i ≠ 2 * v := by
      intro he; apply hne
      refine ⟨t + 1, le_rfl, ?_⟩
      rw [anc_succ]; omega
    have hc2 : i ≠ 2 * v + 1 := by
      intro he; apply hne
      refine ⟨t + 1, le_rfl, ?_⟩
      rw [anc_succ]; omega
    rw [getD_set_ne (Ne.symm hvi), getD_set_ne hc1, getD_set_ne hc2]
    exact hc.2 v hv1 hv2 hne'

end Lax496464Proofs.Ram.SegTree
