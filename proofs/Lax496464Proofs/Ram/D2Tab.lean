import Lax496464Proofs.Ram.D2Ach
import Lax496464Proofs.Ram.D2Valid

/-!
# Theorem 2, pure layer 6: the table invariant, and how one step preserves it

The main loop fills the numbers `c = N-1, N-2, …, 0`.  `TabOK thr T` says that the entries of `T`
of every code `≥ thr` are right (`Rep` of `AchGe`) and that those of every number `< thr` are still
zero; `ValidOK thr V` says the same about the `VALID` array.  A step, from `thr = c + 1` to `c`,
only has to say what happened to the cells of the number `c`.
-/

namespace Lax496464Proofs.Ram.D2Tab

open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Valid
open Lax496464Proofs.Ram.D2Ach

theorem rep_le {inf t : ℕ} {Q : ℤ → Prop} (h : Rep inf t Q) : t ≤ inf := by
  rcases h with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨v, h0, h1, -, -⟩ <;> omega

/-- The entries of the numbers `≥ thr` are right; those of the numbers `< thr` are zero. -/
def TabOK (J : Instance) (n m W inf N thr : ℕ) (T : List ℕ) : Prop :=
  T.length = N * (W + 1) ∧
  (∀ Zs, SL n m Zs → thr ≤ codeL n m Zs → ∀ r ≤ W,
    Rep inf (T.getD (codeL n m Zs * (W + 1) + r) 0) (fun P' => AchGe J (ofList J Zs) r P')) ∧
  (∀ i, i < N * (W + 1) → i / (W + 1) < thr → T.getD i 0 = 0)

open Classical in
/-- The `VALID` entries of the numbers `≥ thr` are right. -/
noncomputable def ValidOK (n m N thr : ℕ) (V : List ℕ) : Prop :=
  V.length = N ∧ (∀ c', thr ≤ c' → c' < N → V.getD c' 0 = if IsCode n m c' then 1 else 0) ∧
  (∀ i, V.getD i 0 ≤ 1)

theorem div_block (a W r : ℕ) (hr : r ≤ W) : (a * (W + 1) + r) / (W + 1) = a := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega),
    Nat.div_eq_of_lt (by omega)]
  simp

theorem tab_step {J : Instance} {n m W inf N c : ℕ} {T T' : List ℕ} (hN : N = (n + 1) ^ m)
    (hT : TabOK J n m W inf N (c + 1) T) (hlen : T'.length = N * (W + 1))
    (hout : ∀ i, i < N * (W + 1) → i / (W + 1) ≠ c → T'.getD i 0 = T.getD i 0)
    (hblock : ∀ Zs, SL n m Zs → codeL n m Zs = c → ∀ r ≤ W,
      Rep inf (T'.getD (c * (W + 1) + r) 0) (fun P' => AchGe J (ofList J Zs) r P')) :
    TabOK J n m W inf N c T' := by
  obtain ⟨hl, hrep, hzero⟩ := hT
  refine ⟨hlen, ?_, ?_⟩
  · intro Zs hsl hc r hr
    by_cases hcc : codeL n m Zs = c
    · rw [hcc]; exact hblock Zs hsl hcc r hr
    · have hgt : c + 1 ≤ codeL n m Zs := by omega
      have hlt : codeL n m Zs * (W + 1) + r < N * (W + 1) := by
        have h1 := hsl.codeL_lt
        rw [← hN] at h1
        nlinarith
      have hdiv := div_block (codeL n m Zs) W r hr
      rw [hout _ hlt (by rw [hdiv]; exact hcc)]
      exact hrep Zs hsl hgt r hr
  · intro i hi hic
    have hne : i / (W + 1) ≠ c := by omega
    rw [hout i hi hne]
    exact hzero i hi (by omega)

theorem sl_nil (n m : ℕ) : SL n m [] :=
  ⟨List.sortedLT_iff_pairwise.mpr List.Pairwise.nil, by simp, by simp⟩

/-- The only set with the code of the empty set is the empty set. -/
theorem eq_nil_of_code_top {n m : ℕ} {Zs : List ℕ} (h : SL n m Zs)
    (hc : codeL n m Zs = (n + 1) ^ m - 1) : Zs = [] :=
  h.codeL_inj (sl_nil n m) (by rw [hc, codeL_nil])

/-- **A step at the empty set.** -/
theorem tab_step_empty {J : Instance} {n m W inf N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hc : c = N - 1) (hcN : 0 < N) (hT : TabOK J n m W inf N (c + 1) T) :
    TabOK J n m W inf N c (T.set (c * (W + 1)) inf) := by
  have hlenT := hT.1
  have hcR : c * (W + 1) < N * (W + 1) := by
    have : c < N := by omega
    exact Nat.mul_lt_mul_of_pos_right this (by omega)
  refine tab_step hN hT (by rw [List.length_set, hlenT]) ?_ ?_
  · intro i hi hne
    apply ListUtil.getD_set_ne
    intro h
    apply hne
    rw [h]
    exact Nat.mul_div_cancel _ (by omega)
  · intro Zs hsl hcode r hr
    have hZs : Zs = [] := eq_nil_of_code_top hsl (by rw [hcode, hc, hN])
    subst hZs
    rw [ofList_nil]
    by_cases hr0 : r = 0
    · subst hr0
      simp only [Nat.add_zero]
      rw [ListUtil.getD_set_self _ _ _ (by omega)]
      exact Or.inr (Or.inl ⟨rfl, fun P' _ => (achGe_empty 0 P').mpr rfl⟩)
    · have hidx : c * (W + 1) + r < N * (W + 1) := by
        have : c + 1 ≤ N := by omega
        nlinarith
      have hne : c * (W + 1) + r ≠ c * (W + 1) := by omega
      rw [ListUtil.getD_set_ne _ _ _ _ hne]
      have hz := hT.2.2 (c * (W + 1) + r) hidx (by rw [div_block c W r hr]; omega)
      rw [hz]
      exact Or.inl ⟨rfl, fun P' _ h => hr0 ((achGe_empty r P').mp h)⟩

/-- **A step at a number that is not a code.** -/
theorem tab_step_invalid {J : Instance} {n m W inf N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hnc : ¬ IsCode n m c) (hT : TabOK J n m W inf N (c + 1) T) :
    TabOK J n m W inf N c T := by
  refine tab_step hN hT hT.1 (fun i _ _ => rfl) ?_
  intro Zs hsl hcode
  exact absurd ⟨Zs, hsl, hcode⟩ hnc

theorem valid_step {n m N c v : ℕ} {V : List ℕ} (hV : ValidOK n m N (c + 1) V) (hcN : c < N)
    (hv : v = (open Classical in if IsCode n m c then 1 else 0)) :
    ValidOK n m N c (V.set c v) := by
  classical
  obtain ⟨hl, hval, hle⟩ := hV
  refine ⟨by rw [List.length_set, hl], ?_, ?_⟩
  · intro c' hc' hc'N
    by_cases hcc : c' = c
    · subst hcc
      rw [ListUtil.getD_set_self _ _ _ (by omega), hv]
    · rw [ListUtil.getD_set_ne _ _ _ _ hcc]
      exact hval c' (by omega) hc'N
  · intro i
    by_cases hi : i = c
    · subst hi
      by_cases hlt : i < V.length
      · rw [ListUtil.getD_set_self _ _ _ hlt, hv]; split_ifs <;> omega
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set]
        simp [hlt]
    · rw [ListUtil.getD_set_ne _ _ _ _ hi]; exact hle i

end Lax496464Proofs.Ram.D2Tab
