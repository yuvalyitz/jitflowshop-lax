import Lax496464Proofs.Ram.D2Rows
import Lax496464Proofs.Ram.D3Cor3

/-!
# Corollary 3's Machine, Part 1: the Cells of One Set (the Dual Row Block)

For the set with number `c`, whose `X₁` and `X₂` have numbers `c₁, c₂ > c`, the `n+1` cells of its
block are `T[c,u] = max(T[c₁,u], min W (w_j + T[c₂,u+1]))`, the second term present only when the
guard `(u+1)·p + q ≤ d ∧ u+1 ≤ n` holds.  The machine never forms `(u+1)·p`: with
`lim = limOf n p q d` (computed once per job by a division) the guard is `u < lim`
(`guard_iff`).  Cell `u` of number `c` is at `c·(n+1) + u`.
-/

namespace Lax496464Proofs.Ram.D5Row

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)

/-- The last `u + 1` for which the guard holds. -/
def limOf (n p q d : ℕ) : ℕ :=
  if d < q then 0 else if p = 0 then n else min n ((d - q) / p)

theorem limOf_le (n p q d : ℕ) : limOf n p q d ≤ n := by
  unfold limOf; split_ifs <;> omega

/-- **The guard, without the product.** -/
theorem guard_iff (n p q d u : ℕ) :
    ((u + 1) * p + q ≤ d ∧ u + 1 ≤ n) ↔ u < limOf n p q d := by
  unfold limOf
  by_cases hdq : d < q
  · rw [if_pos hdq]
    constructor
    · rintro ⟨h, -⟩; nlinarith [Nat.zero_le ((u + 1) * p)]
    · intro h; omega
  · rw [if_neg hdq]
    by_cases hp : p = 0
    · subst hp
      rw [if_pos rfl]
      simp only [Nat.mul_zero, Nat.zero_add]
      constructor
      · rintro ⟨-, h⟩; omega
      · intro h; exact ⟨by omega, by omega⟩
    · rw [if_neg hp]
      have hp' : 0 < p := Nat.pos_of_ne_zero hp
      constructor
      · rintro ⟨h1, h2⟩
        have : (u + 1) * p ≤ d - q := by omega
        have := (Nat.le_div_iff_mul_le hp').mpr this
        omega
      · intro h
        have h1 : u + 1 ≤ (d - q) / p := by omega
        have := (Nat.le_div_iff_mul_le hp').mp h1
        exact ⟨by omega, by omega⟩

/-- The machine's cell, from the two entries it reads. -/
def cellV (W lim wj t1 t2 u : ℕ) : ℕ :=
  max t1 (if u < lim then min W (wj + t2) else 0)

theorem cellV_eq_dStepU {W n p q d w u t1 t2 : ℕ} :
    cellV W (limOf n p q d) w t1 t2 u = Lax496464Proofs.Ram.D3Cor3.dStepU W n p q d w u t1 t2 := by
  unfold cellV Lax496464Proofs.Ram.D3Cor3.dStepU
  by_cases h : (u + 1) * p + q ≤ d ∧ u + 1 ≤ n
  · rw [if_pos h, if_pos ((guard_iff n p q d u).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((guard_iff n p q d u).mpr h'))]

theorem cellV_le {W lim wj t1 t2 u : ℕ} (h1 : t1 ≤ W) : cellV W lim wj t1 t2 u ≤ W := by
  unfold cellV
  split_ifs <;> omega

/-! ## The limit -/

def limCom : Com :=
  .ite (.lt (V "cd") (V "cq")) (.assign "lim" (.lit 0))
    (.ite (.eq (V "cp") (.lit 0)) (.assign "lim" (V "n"))
      (.seq (.assign "lim" (.bin .div (.bin .sub (V "cd") (V "cq")) (V "cp")))
        (.ite (.lt (V "n") (V "lim")) (.assign "lim" (V "n")) .skip)))

theorem limCom_spec {B : ℕ} (hB : 2 < B) (n p q d : ℕ) (hnB : n < B) (hdB : d < B) (hqB : q < B) (hpB : p < B) :
    Spec B (fun σ => σ.vars "n" = n ∧ σ.vars "cp" = p ∧ σ.vars "cq" = q ∧ σ.vars "cd" = d)
      limCom
      (fun _σ σ' => σ'.vars "lim" = limOf n p q d) 40 := by
  unfold limCom limOf
  run_vcg
  all_goals (simp_all)
  all_goals (try (rw [if_neg (by omega)]))
  all_goals (try (exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)))
  all_goals (try (rw [min_eq_left (by omega)]))


/-! ## One cell -/

/-- One cell of the block. -/
def rowBodyU : Com :=
  .seq (.assign "z1" (.get "TAB" (.bin .add (V "zb1") (V "ri"))))
    (.seq (.ite (.lt (V "ri") (V "lim"))
        (.seq (.assign "ct" (.get "TAB" (.bin .add (.bin .add (V "zb2") (V "ri")) (.lit 1))))
          (.seq (.assign "ct" (.bin .add (V "wj") (V "ct")))
            (.seq (.ite (.lt (V "Wc") (V "ct")) (.assign "ct" (V "Wc")) .skip)
              (.ite (.lt (V "z1") (V "ct")) (.assign "z1" (V "ct")) .skip))))
        .skip)
      (.seq (.store "TAB" (.bin .add (V "zbc") (V "ri")) (V "z1")) (bump "ri")))

theorem rowBodyU_spec {B : ℕ} (hB : 2 < B) (Wc lim wj zb1 zb2 zbc ri t1 t2 : ℕ)
    (hWB : Wc < B) (ht1 : t1 ≤ Wc) (hwW : wj + Wc < B) (hi1 : zb1 + ri < B)
    (hi3 : zbc + ri < B) (hriB : ri + 1 < B) (hlimB : lim < B) (hwjB : wj < B)
    (hg : ri < lim → zb2 + ri + 1 < B ∧ t2 ≤ Wc) :
    Spec B (fun σ => σ.vars "ri" = ri ∧ σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧
        σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧ σ.vars "Wc" = Wc ∧ σ.vars "lim" = lim ∧
        (σ.arrs "TAB").getD (zb1 + ri) 0 = t1 ∧ zb1 + ri < (σ.arrs "TAB").length ∧
        (ri < lim → (σ.arrs "TAB").getD (zb2 + ri + 1) 0 = t2 ∧
          zb2 + ri + 1 < (σ.arrs "TAB").length) ∧
        zbc + ri < (σ.arrs "TAB").length) rowBodyU
      (fun σ σ' => σ'.arrs "TAB" = (σ.arrs "TAB").set (zbc + ri) (cellV Wc lim wj t1 t2 ri) ∧
        σ'.vars "ri" = ri + 1) 100 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hri, hzb1, hzb2, hzbc, hwj, hWc, hlim, hg1, hl1, hg2, hl3⟩ := hσ
  have ht1B : t1 < B := by omega
  unfold cellV
  run_vcg
  all_goals (simp_all)
  all_goals (try (congr 1; omega))
  all_goals (try (rw [if_neg (by omega)]; simp))


/-- The value of cell `r` of the block, from the array as it was before the block was written. -/
def cellVal (Wc lim wj zb1 zb2 : ℕ) (TAB0 : List ℕ) (r : ℕ) : ℕ :=
  cellV Wc lim wj (TAB0.getD (zb1 + r) 0) (TAB0.getD (zb2 + r + 1) 0) r

/-- All the cells of the block. -/
def rowsLoopU : Com :=
  .seq (.assign "ri" (.lit 0)) (.while (.lt (V "ri") (V "R")) rowBodyU)

/-- What the loop over the cells keeps. -/
def RInv (Wc lim wj zb1 zb2 zbc R L : ℕ) (TAB0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧ σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧
  σ.vars "Wc" = Wc ∧ σ.vars "lim" = lim ∧ σ.vars "R" = R ∧
  σ.vars "ri" ≤ R ∧ (σ.arrs "TAB").length = L ∧
  (∀ i, i < L → (i < zbc ∨ zbc + σ.vars "ri" ≤ i) → (σ.arrs "TAB").getD i 0 = TAB0.getD i 0) ∧
  (∀ r, r < σ.vars "ri" → (σ.arrs "TAB").getD (zbc + r) 0 = cellVal Wc lim wj zb1 zb2 TAB0 r)

theorem rowsLoopU_spec {B : ℕ} (hB : 2 < B) (Wc lim wj zb1 zb2 zbc R L : ℕ) (TAB0 : List ℕ)
    (hWB : Wc < B) (hwW : wj + Wc < B) (hwjB : wj < B) (hlimB : lim < B)
    (hLB : L < B) (hRB : R < B) (hL : TAB0.length = L)
    (h1 : zbc + R ≤ zb1) (h2 : zbc + R ≤ zb2) (h1L : zb1 + R ≤ L) (h2L : zb2 + R ≤ L)
    (hcL : zbc + R ≤ L) (hlim : lim < R)
    (hr1 : ∀ r, r < R → TAB0.getD (zb1 + r) 0 ≤ Wc)
    (hr2 : ∀ r, r < lim → TAB0.getD (zb2 + r + 1) 0 ≤ Wc) :
    Spec B (fun σ => σ.arrs "TAB" = TAB0 ∧ σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧
        σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧ σ.vars "Wc" = Wc ∧ σ.vars "lim" = lim ∧
        σ.vars "R" = R) rowsLoopU
      (fun _σ σ' => (σ'.arrs "TAB").length = L ∧
        (∀ i, i < L → (i < zbc ∨ zbc + R ≤ i) → (σ'.arrs "TAB").getD i 0 = TAB0.getD i 0) ∧
        (∀ r, r < R → (σ'.arrs "TAB").getD (zbc + r) 0 = cellVal Wc lim wj zb1 zb2 TAB0 r))
      ((100 + 4) * R + 6) := by
  have hbody : Spec B (fun σ => RInv Wc lim wj zb1 zb2 zbc R L TAB0 σ ∧ σ.vars "ri" < R)
      rowBodyU (fun σ σ' => RInv Wc lim wj zb1 zb2 zbc R L TAB0 σ' ∧
        σ'.vars "ri" = σ.vars "ri" + 1) 100 := by
    refine Spec.of_exists fun σ ⟨hI, hlt⟩ => ?_
    obtain ⟨hzb1, hzb2, hzbc, hwj, hWc, hlm, hR, hri, hlen, hout, hin⟩ := hI
    have hread1 : (σ.arrs "TAB").getD (zb1 + σ.vars "ri") 0 = TAB0.getD (zb1 + σ.vars "ri") 0 :=
      hout _ (by omega) (Or.inr (by omega))
    have hread2 : σ.vars "ri" < lim → (σ.arrs "TAB").getD (zb2 + σ.vars "ri" + 1) 0 =
        TAB0.getD (zb2 + σ.vars "ri" + 1) 0 := fun hl =>
      hout _ (by omega) (Or.inr (by omega))
    obtain ⟨σ', hrun, ⟨hset, hri'⟩, hfv, hfa, -, -⟩ :=
      (rowBodyU_spec hB Wc lim wj zb1 zb2 zbc (σ.vars "ri") (TAB0.getD (zb1 + σ.vars "ri") 0)
        (TAB0.getD (zb2 + σ.vars "ri" + 1) 0) hWB (hr1 _ hlt) hwW (by omega) (by omega)
        (by omega) hlimB hwjB (fun hl => ⟨by omega, hr2 _ hl⟩)).frame.run
        ⟨rfl, hzb1, hzb2, hzbc, hwj, hWc, hlm, hread1, by omega,
          fun hl => ⟨hread2 hl, by omega⟩, by omega⟩
    refine ⟨σ', 100, hrun, le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hri'⟩
    · rw [hfv "zb1" (by decide)]; exact hzb1
    · rw [hfv "zb2" (by decide)]; exact hzb2
    · rw [hfv "zbc" (by decide)]; exact hzbc
    · rw [hfv "wj" (by decide)]; exact hwj
    · rw [hfv "Wc" (by decide)]; exact hWc
    · rw [hfv "lim" (by decide)]; exact hlm
    · rw [hfv "R" (by decide)]; exact hR
    · rw [hri']; omega
    · rw [hset]; simp [hlen]
    · intro i hi hio
      rw [hset, hri']  at *
      have hne : i ≠ zbc + σ.vars "ri" := by omega
      rw [ListUtil.getD_set_ne _ _ _ _ hne]
      exact hout i hi (by omega)
    · intro r hr
      rw [hset]
      rw [hri'] at hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | hr
      · rw [ListUtil.getD_set_ne _ _ _ _ (by omega)]
        exact hin r hr
      · subst hr
        rw [ListUtil.getD_set_self _ _ _ (by omega)]
        unfold cellVal
        rfl
  have hloop := Spec.forRangeZero (B := B) (c := rowBodyU) "ri" "R"
    (RInv Wc lim wj zb1 zb2 zbc R L TAB0) R 100 hRB
    (fun σ h => by obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := h; exact h8)
    (fun σ h => by obtain ⟨-, -, -, -, -, -, h7, -⟩ := h; exact h7) hbody
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hT, h1', h2', h3', h4', h5', h6', h7'⟩
    refine ⟨by simpa using h1', by simpa using h2', by simpa using h3', by simpa using h4',
      by simpa using h5', by simpa using h6', by simpa using h7', by simp, by simp [hT, hL], ?_, ?_⟩
    · intro i hi _
      simp [hT]
    · intro r hr; simp at hr
  · rintro σ σ' - ⟨⟨-, -, -, -, -, -, -, -, hlen, hout, hin⟩, hri⟩
    rw [hri] at hout hin
    exact ⟨hlen, hout, hin⟩

theorem rowsLoopU_wvars : ∀ y ∈ rowsLoopU.wvars, y ∈ ["ri", "z1", "ct"] := by decide

theorem rowsLoopU_warrs : ∀ a ∈ rowsLoopU.warrs, a = "TAB" := by decide

/-- `rowsLoopU_spec`, with its frame stated. -/
theorem rowsLoopU_spec' {B : ℕ} (hB : 2 < B) (Wc lim wj zb1 zb2 zbc R L : ℕ) (TAB0 : List ℕ)
    (hWB : Wc < B) (hwW : wj + Wc < B) (hwjB : wj < B) (hlimB : lim < B)
    (hLB : L < B) (hRB : R < B) (hL : TAB0.length = L)
    (h1 : zbc + R ≤ zb1) (h2 : zbc + R ≤ zb2) (h1L : zb1 + R ≤ L) (h2L : zb2 + R ≤ L)
    (hcL : zbc + R ≤ L) (hlim : lim < R)
    (hr1 : ∀ r, r < R → TAB0.getD (zb1 + r) 0 ≤ Wc)
    (hr2 : ∀ r, r < lim → TAB0.getD (zb2 + r + 1) 0 ≤ Wc) :
    Spec B (fun σ => σ.arrs "TAB" = TAB0 ∧ σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧
        σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧ σ.vars "Wc" = Wc ∧ σ.vars "lim" = lim ∧
        σ.vars "R" = R) rowsLoopU
      (fun σ σ' => (σ'.arrs "TAB").length = L ∧
        (∀ i, i < L → (i < zbc ∨ zbc + R ≤ i) → (σ'.arrs "TAB").getD i 0 = TAB0.getD i 0) ∧
        (∀ r, r < R → (σ'.arrs "TAB").getD (zbc + r) 0 = cellVal Wc lim wj zb1 zb2 TAB0 r) ∧
        (∀ v, v ∉ ["ri", "z1", "ct"] → σ'.vars v = σ.vars v) ∧
        (∀ a, a ≠ "TAB" → σ'.arrs a = σ.arrs a))
      ((100 + 4) * R + 6) := by
  refine ((rowsLoopU_spec hB Wc lim wj zb1 zb2 zbc R L TAB0 hWB hwW hwjB hlimB hLB hRB hL
    h1 h2 h1L h2L hcL hlim hr1 hr2).frame).post ?_
  rintro σ σ' - ⟨⟨hl, ho, hc⟩, hfv, hfa, -, -⟩
  exact ⟨hl, ho, hc, fun v hv => hfv v (fun h => hv (rowsLoopU_wvars v h)),
    fun a ha => hfa a (fun h => ha (rowsLoopU_warrs a h))⟩

end Lax496464Proofs.Ram.D5Row
