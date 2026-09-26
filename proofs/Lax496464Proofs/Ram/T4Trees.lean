import Lax496464Proofs.Ram.SegTree
import Lax496464Proofs.Ram.T4Model
import Lax808846Proofs.Lib.Basic

/-!
# The two trees, as functions of the set they hold

`TX` holds `d i + 1` at the leaf of every job `i` of the set and `0` elsewhere, so its root is
one more than the largest due date; `TY` holds `BIG - d i`, so its root says which due date is
the smallest. `lfX`/`lfY` are those leaf functions, and the lemmas are what a tree with such
leaves knows about the set.
-/

namespace Lax496464Proofs.Ram.T4Trees

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464Proofs.Ram.SegTree
open Lax808846Proofs.Reasoning.Lib

variable {J : Instance}

/-- The leaves of `TX`. -/
def lfX (J : Instance) (Act : Finset J.Job) (k : ℕ) : ℕ :=
  if h : k < J.jobs then (if (⟨k, h⟩ : J.Job) ∈ Act then J.d ⟨k, h⟩ + 1 else 0) else 0

/-- The leaves of `TY`. -/
def lfY (J : Instance) (BIG : ℕ) (Act : Finset J.Job) (k : ℕ) : ℕ :=
  if h : k < J.jobs then (if (⟨k, h⟩ : J.Job) ∈ Act then BIG - J.d ⟨k, h⟩ else 0) else 0

/-- The leaves of the array `T` (over `2^h` leaves) are those of `f`. -/
def Leaves (T : List ℕ) (h : ℕ) (f : ℕ → ℕ) : Prop := ∀ ℓ < 2 ^ h, T.getD (2 ^ h + ℓ) 0 = f ℓ

theorem lfX_insert {k : ℕ} (hk : k < J.jobs) (Act : Finset J.Job) :
    upd (lfX J Act) k (J.d ⟨k, hk⟩ + 1) = lfX J (insert ⟨k, hk⟩ Act) := by
  funext ℓ
  by_cases hℓ : ℓ = k
  · subst hℓ; simp [lfX, hk]
  · rw [upd_of_ne _ hℓ]
    unfold lfX
    by_cases h : ℓ < J.jobs
    · have hne : (⟨ℓ, h⟩ : J.Job) ≠ ⟨k, hk⟩ := fun e => hℓ (Fin.mk.inj e)
      simp [h, hne]
    · simp [h]

theorem lfX_erase {k : ℕ} (hk : k < J.jobs) (Act : Finset J.Job) :
    upd (lfX J Act) k 0 = lfX J (Act.erase ⟨k, hk⟩) := by
  funext ℓ
  by_cases hℓ : ℓ = k
  · subst hℓ; simp [lfX, hk]
  · rw [upd_of_ne _ hℓ]
    unfold lfX
    by_cases h : ℓ < J.jobs
    · have hne : (⟨ℓ, h⟩ : J.Job) ≠ ⟨k, hk⟩ := fun e => hℓ (Fin.mk.inj e)
      simp [h, hne]
    · simp [h]

theorem lfY_insert {k : ℕ} (hk : k < J.jobs) (BIG : ℕ) (Act : Finset J.Job) :
    upd (lfY J BIG Act) k (BIG - J.d ⟨k, hk⟩) = lfY J BIG (insert ⟨k, hk⟩ Act) := by
  funext ℓ
  by_cases hℓ : ℓ = k
  · subst hℓ; simp [lfY, hk]
  · rw [upd_of_ne _ hℓ]
    unfold lfY
    by_cases h : ℓ < J.jobs
    · have hne : (⟨ℓ, h⟩ : J.Job) ≠ ⟨k, hk⟩ := fun e => hℓ (Fin.mk.inj e)
      simp [h, hne]
    · simp [h]

theorem lfY_erase {k : ℕ} (hk : k < J.jobs) (BIG : ℕ) (Act : Finset J.Job) :
    upd (lfY J BIG Act) k 0 = lfY J BIG (Act.erase ⟨k, hk⟩) := by
  funext ℓ
  by_cases hℓ : ℓ = k
  · subst hℓ; simp [lfY, hk]
  · rw [upd_of_ne _ hℓ]
    unfold lfY
    by_cases h : ℓ < J.jobs
    · have hne : (⟨ℓ, h⟩ : J.Job) ≠ ⟨k, hk⟩ := fun e => hℓ (Fin.mk.inj e)
      simp [h, hne]
    · simp [h]

/-! ## What the root says -/

theorem root_eq_zero_of_empty {T : List ℕ} {h : ℕ} (hc : Cons T h) {f : ℕ → ℕ}
    (hl : Leaves T h f) (hf : ∀ ℓ, ℓ < 2 ^ h → f ℓ = 0) : T.getD 1 0 = 0 := by
  obtain ⟨i, h1, h2, h3⟩ := hc.exists_leaf
  rw [← h3, show i = 2 ^ h + (i - 2 ^ h) by omega, hl _ (by omega), hf _ (by omega)]

theorem root_ge_leaf {T : List ℕ} {h : ℕ} (hc : Cons T h) {f : ℕ → ℕ} (hl : Leaves T h f)
    {ℓ : ℕ} (hℓ : ℓ < 2 ^ h) : f ℓ ≤ T.getD 1 0 := by
  have := hc.leaf_le_root (ℓ := 2 ^ h + ℓ) (by omega) (by omega)
  rwa [hl ℓ hℓ] at this

/-- The leaf found by descending `TX` is a member of the largest due date. -/
theorem x_max_leaf {T : List ℕ} {h : ℕ} (hc : Cons T h) {Act : Finset J.Job}
    (hl : Leaves T h (lfX J Act)) (hn : J.jobs ≤ 2 ^ h) {ℓ : ℕ} (hℓ : ℓ < 2 ^ h)
    (hroot : T.getD (2 ^ h + ℓ) 0 = T.getD 1 0) (hne : T.getD 1 0 ≠ 0) :
    ∃ hk : ℓ < J.jobs, (⟨ℓ, hk⟩ : J.Job) ∈ Act ∧ ∀ i ∈ Act, J.d i ≤ J.d ⟨ℓ, hk⟩ := by
  have hv := hl ℓ hℓ
  rw [hroot] at hv
  have hk : ℓ < J.jobs := by
    by_contra hn'
    simp [lfX, hn'] at hv
    exact hne hv
  refine ⟨hk, ?_, ?_⟩
  · by_contra hm
    simp [lfX, hk, hm] at hv
    exact hne hv
  · intro i hi
    have h1 := root_ge_leaf hc hl (ℓ := i) (by have := i.isLt; omega)
    have h2 : lfX J Act i = J.d i + 1 := by simp [lfX, i.isLt, hi]
    rw [h2] at h1
    have h3 : lfX J Act ℓ = J.d ⟨ℓ, hk⟩ + 1 := by
      have hmem : (⟨ℓ, hk⟩ : J.Job) ∈ Act := by
        by_contra hm
        simp [lfX, hk, hm] at hv
        exact hne hv
      simp [lfX, hk, hmem]
    have := hl ℓ hℓ
    rw [h3] at this
    omega

theorem root_ne_zero_of_nonempty {T : List ℕ} {h : ℕ} (hc : Cons T h) {Act : Finset J.Job}
    (hl : Leaves T h (lfX J Act)) (hn : J.jobs ≤ 2 ^ h) (hne : Act.Nonempty) :
    T.getD 1 0 ≠ 0 := by
  obtain ⟨i, hi⟩ := hne
  have h1 := root_ge_leaf hc hl (ℓ := i) (by have := i.isLt; omega)
  have h2 : lfX J Act i = J.d i + 1 := by simp [lfX, i.isLt, hi]
  omega

/-- The leaf found by descending `TY` is a member of the smallest due date. -/
theorem y_min_leaf {T : List ℕ} {h : ℕ} (hc : Cons T h) {Act : Finset J.Job} {BIG : ℕ}
    (hBIG : ∀ i : J.Job, J.d i < BIG) (hl : Leaves T h (lfY J BIG Act)) (hn : J.jobs ≤ 2 ^ h)
    {ℓ : ℕ} (hℓ : ℓ < 2 ^ h) (hroot : T.getD (2 ^ h + ℓ) 0 = T.getD 1 0)
    (hne : T.getD 1 0 ≠ 0) :
    ∃ hk : ℓ < J.jobs, (⟨ℓ, hk⟩ : J.Job) ∈ Act ∧ ∀ i ∈ Act, J.d ⟨ℓ, hk⟩ ≤ J.d i := by
  have hv := hl ℓ hℓ
  rw [hroot] at hv
  have hk : ℓ < J.jobs := by
    by_contra hn'
    simp [lfY, hn'] at hv
    exact hne hv
  have hmem : (⟨ℓ, hk⟩ : J.Job) ∈ Act := by
    by_contra hm
    simp [lfY, hk, hm] at hv
    exact hne hv
  refine ⟨hk, hmem, ?_⟩
  intro i hi
  have h1 := root_ge_leaf hc hl (ℓ := i) (by have := i.isLt; omega)
  have h2 : lfY J BIG Act i = BIG - J.d i := by simp [lfY, i.isLt, hi]
  rw [h2] at h1
  have h3 : lfY J BIG Act ℓ = BIG - J.d ⟨ℓ, hk⟩ := by simp [lfY, hk, hmem]
  have := hl ℓ hℓ
  rw [h3] at this
  have := hBIG i
  have := hBIG ⟨ℓ, hk⟩
  omega

theorem y_root_ne_zero_of_nonempty {T : List ℕ} {h : ℕ} (hc : Cons T h) {Act : Finset J.Job}
    {BIG : ℕ} (hBIG : ∀ i : J.Job, J.d i < BIG) (hl : Leaves T h (lfY J BIG Act))
    (hn : J.jobs ≤ 2 ^ h) (hne : Act.Nonempty) : T.getD 1 0 ≠ 0 := by
  obtain ⟨i, hi⟩ := hne
  have h1 := root_ge_leaf hc hl (ℓ := i) (by have := i.isLt; omega)
  have h2 : lfY J BIG Act i = BIG - J.d i := by simp [lfY, i.isLt, hi]
  have := hBIG i
  omega

/-- The root of `TY` is `BIG` minus the smallest due date of the set. -/
theorem y_root_min {T : List ℕ} {h : ℕ} (hc : Cons T h) {Act : Finset J.Job} {BIG : ℕ}
    (hBIG : ∀ i : J.Job, J.d i < BIG) (hl : Leaves T h (lfY J BIG Act)) (hn : J.jobs ≤ 2 ^ h)
    (hne : Act.Nonempty) :
    ∃ c ∈ Act, T.getD 1 0 = BIG - J.d c ∧ ∀ i ∈ Act, J.d c ≤ J.d i := by
  obtain ⟨i, h1, h2, h3⟩ := hc.exists_leaf
  have hne0 := y_root_ne_zero_of_nonempty hc hBIG hl hn hne
  have hi : i = 2 ^ h + (i - 2 ^ h) := by omega
  obtain ⟨hk, hmem, hmin⟩ := y_min_leaf hc hBIG hl hn (ℓ := i - 2 ^ h) (by omega)
    (by rw [← hi]; exact h3) hne0
  refine ⟨⟨i - 2 ^ h, hk⟩, hmem, ?_, hmin⟩
  have := hl (i - 2 ^ h) (by omega)
  rw [← hi, h3] at this
  rw [this]; simp [lfY, hk, hmem]

theorem y_root_zero {T : List ℕ} {h : ℕ} (hc : Cons T h) {BIG : ℕ}
    (hl : Leaves T h (lfY J BIG (∅ : Finset J.Job))) : T.getD 1 0 = 0 :=
  root_eq_zero_of_empty hc hl (fun ℓ _ => by simp [lfY])

end Lax496464Proofs.Ram.T4Trees
