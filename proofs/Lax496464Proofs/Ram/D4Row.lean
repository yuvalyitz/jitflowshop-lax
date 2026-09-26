import Lax496464Proofs.Ram.D2Rows
import Lax496464Proofs.Ram.D3Dual

/-!
# Corollary 2's machine: the cells of one set (dual table)

The block of the set with number `c` has the `R+1` rows `t = 0 … R` (`R = P`, the total preprocessing
time); the cell `(c, t)` sits at `c·(R+1) + t`.  For `X₁`, `X₂` with numbers `c₁, c₂ > c` the cell is
`dStep W R p q d w t T[c₁,t] T[c₂,t+p]`: two lookups (the second only when `t + p ≤ R`, and
`t + p + q ≤ d`), the cap `W`, one comparison and one store, `O(1)`.
-/

namespace Lax496464Proofs.Ram.D4Row

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.D3Dual (dStep)

/-- One cell of the row block; `"R"` holds the width `R + 1`. -/
def rowBody4 : Com :=
  .seq (.assign "z1" (.get "TAB" (.bin .add (V "zb1") (V "ri"))))
    (.seq (.assign "zr" (.bin .add (V "ri") (V "cp")))
      (.seq (.ite (.lt (V "zr") (V "R"))
          (.ite (.lt (.bin .add (V "zr") (V "cq")) (.bin .add (V "cd") (.lit 1)))
            (.seq (.assign "ct" (.get "TAB" (.bin .add (V "zb2") (V "zr"))))
              (.seq (.assign "cf" (.bin .add (V "wj") (V "ct")))
                (.seq (.ite (.lt (V "W") (V "cf")) (.assign "cf" (V "W")) .skip)
                  (.ite (.lt (V "z1") (V "cf")) (.assign "z1" (V "cf")) .skip))))
            .skip)
          .skip)
        (.seq (.store "TAB" (.bin .add (V "zbc") (V "ri")) (V "z1")) (bump "ri"))))

theorem rowBody4_spec {B : ℕ} (hB : 2 < B) (W R d q p wj zb1 zb2 zbc ri : ℕ)
    (hWB : W + 1 < B) (hwW : wj + W < B) (hdB : d + 1 < B) (hqB : q < B) (hpB : p < B)
    (hrp : R + p + q + 1 < B) (hi1 : zb1 + ri < B) (hi2 : ri + p ≤ R → zb2 + (ri + p) < B)
    (hi3 : zbc + ri < B) (hriB : ri + 1 < B) (_hriB' : ri < B) (hwjB : wj < B) (hriR : ri ≤ R) :
    Spec B (fun σ => σ.vars "ri" = ri ∧ σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧
        σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧ σ.vars "W" = W ∧ σ.vars "R" = R + 1 ∧
        σ.vars "cd" = d ∧ σ.vars "cq" = q ∧ σ.vars "cp" = p ∧
        (σ.arrs "TAB").getD (zb1 + ri) 0 ≤ W ∧ zb1 + ri < (σ.arrs "TAB").length ∧
        (ri + p ≤ R → zb2 + (ri + p) < (σ.arrs "TAB").length ∧
          (σ.arrs "TAB").getD (zb2 + (ri + p)) 0 ≤ W) ∧
        zbc + ri < (σ.arrs "TAB").length) rowBody4
      (fun σ σ' => σ'.arrs "TAB" = (σ.arrs "TAB").set (zbc + ri)
          (dStep W R p q d wj ri ((σ.arrs "TAB").getD (zb1 + ri) 0)
            ((σ.arrs "TAB").getD (zb2 + (ri + p)) 0)) ∧
        σ'.vars "ri" = ri + 1 ∧ (∀ v, v ∉ ["ri", "z1", "zr", "ct", "cf"] → σ'.vars v = σ.vars v))
      100 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hri, hzb1, hzb2, hzbc, hwj, hW, hR, hd, hq, hp, ht1, hl1, ht2, hl3⟩ := hσ
  run_vcg
  all_goals (simp_all)
  all_goals (try omega)
  all_goals (unfold dStep; split_ifs <;> first | omega | (congr 1; omega) | (simp_all; done) | (simp_all; congr 1; omega))

theorem dStep_le {W R p q d w t v1 v2 : ℕ} (h : v1 ≤ W) : dStep W R p q d w t v1 v2 ≤ W := by
  unfold dStep; split_ifs <;> omega

/-- The value of cell `r` of the block, from the array as it was before the block was written. -/
def cellVal4 (W R d q p wj zb1 zb2 : ℕ) (TAB0 : List ℕ) (r : ℕ) : ℕ :=
  dStep W R p q d wj r (TAB0.getD (zb1 + r) 0) (TAB0.getD (zb2 + (r + p)) 0)

/-- All the cells of the block. -/
def rowsLoop4 : Com :=
  .seq (.assign "ri" (.lit 0)) (.while (.lt (V "ri") (V "R")) rowBody4)

/-- What the loop over the cells keeps. -/
def RInv4 (W R d q p wj zb1 zb2 zbc L : ℕ) (TAB0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧ σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧
  σ.vars "W" = W ∧ σ.vars "cd" = d ∧ σ.vars "cq" = q ∧ σ.vars "cp" = p ∧ σ.vars "R" = R + 1 ∧
  σ.vars "ri" ≤ R + 1 ∧ (σ.arrs "TAB").length = L ∧
  (∀ i, i < L → (i < zbc ∨ zbc + σ.vars "ri" ≤ i) → (σ.arrs "TAB").getD i 0 = TAB0.getD i 0) ∧
  (∀ r, r < σ.vars "ri" → (σ.arrs "TAB").getD (zbc + r) 0 = cellVal4 W R d q p wj zb1 zb2 TAB0 r)

theorem rowsLoop4_core {B : ℕ} (hB : 2 < B) (W R d q p wj zb1 zb2 zbc L : ℕ) (TAB0 : List ℕ)
    (hWB : W + 1 < B) (hwW : wj + W < B) (hdB : d + 1 < B) (hqB : q < B) (hpB : p < B)
    (hrp : R + p + q + 1 < B) (hwjB : wj < B) (hLB : L < B) (hRB : R + 1 < B)
    (hL : TAB0.length = L)
    (h1 : zbc + (R + 1) ≤ zb1) (h2 : zbc + (R + 1) ≤ zb2) (h1L : zb1 + (R + 1) ≤ L)
    (h2L : zb2 + (R + 1) ≤ L) (hcL : zbc + (R + 1) ≤ L)
    (hr1 : ∀ r, r < R + 1 → TAB0.getD (zb1 + r) 0 ≤ W)
    (hr2 : ∀ r, r < R + 1 → TAB0.getD (zb2 + r) 0 ≤ W) :
    Spec B (fun σ => σ.arrs "TAB" = TAB0 ∧ σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧
        σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧ σ.vars "W" = W ∧ σ.vars "cd" = d ∧
        σ.vars "cq" = q ∧ σ.vars "cp" = p ∧ σ.vars "R" = R + 1) rowsLoop4
      (fun _σ σ' => (σ'.arrs "TAB").length = L ∧
        (∀ i, i < L → (i < zbc ∨ zbc + (R + 1) ≤ i) → (σ'.arrs "TAB").getD i 0 = TAB0.getD i 0) ∧
        (∀ r, r < R + 1 → (σ'.arrs "TAB").getD (zbc + r) 0 = cellVal4 W R d q p wj zb1 zb2 TAB0 r))
      ((100 + 4) * (R + 1) + 6) := by
  have hbody : Spec B (fun σ => RInv4 W R d q p wj zb1 zb2 zbc L TAB0 σ ∧ σ.vars "ri" < R + 1)
      rowBody4 (fun σ σ' => RInv4 W R d q p wj zb1 zb2 zbc L TAB0 σ' ∧
        σ'.vars "ri" = σ.vars "ri" + 1) 100 := by
    refine Spec.of_exists fun σ ⟨hI, hlt⟩ => ?_
    obtain ⟨hzb1, hzb2, hzbc, hwj, hW, hd, hq, hp, hR, hri, hlen, hout, hin⟩ := hI
    have hread1 : (σ.arrs "TAB").getD (zb1 + σ.vars "ri") 0 = TAB0.getD (zb1 + σ.vars "ri") 0 :=
      hout _ (by omega) (Or.inr (by omega))
    have hread2 : σ.vars "ri" + p ≤ R → (σ.arrs "TAB").getD (zb2 + (σ.vars "ri" + p)) 0 =
        TAB0.getD (zb2 + (σ.vars "ri" + p)) 0 := fun h =>
      hout _ (by omega) (Or.inr (by omega))
    obtain ⟨σ', hrun, ⟨hset, hri', hfv⟩, -, -⟩ :=
      (rowBody4_spec hB W R d q p wj zb1 zb2 zbc (σ.vars "ri") hWB hwW hdB hqB hpB hrp
        (by omega) (fun h => by omega) (by omega) (by omega) (by omega) hwjB (by omega)).frame.run
        ⟨rfl, hzb1, hzb2, hzbc, hwj, hW, hR, hd, hq, hp,
          by rw [hread1]; exact hr1 _ hlt, by omega,
          fun h => ⟨by omega, by rw [hread2 h]; have := hr2 (σ.vars "ri" + p) (by omega); exact this⟩,
          by omega⟩
    refine ⟨σ', 100, hrun, le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hri'⟩
    · rw [hfv "zb1" (by decide)]; exact hzb1
    · rw [hfv "zb2" (by decide)]; exact hzb2
    · rw [hfv "zbc" (by decide)]; exact hzbc
    · rw [hfv "wj" (by decide)]; exact hwj
    · rw [hfv "W" (by decide)]; exact hW
    · rw [hfv "cd" (by decide)]; exact hd
    · rw [hfv "cq" (by decide)]; exact hq
    · rw [hfv "cp" (by decide)]; exact hp
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
        unfold cellVal4
        rw [hread1]
        by_cases hg : σ.vars "ri" + p ≤ R
        · rw [hread2 hg]
        · simp only [dStep]
          rw [if_neg (fun h => hg h.2), if_neg (fun h => hg h.2)]
  have hloop := Spec.forRangeZero (B := B) (c := rowBody4) "ri" "R"
    (RInv4 W R d q p wj zb1 zb2 zbc L TAB0) (R + 1) 100 hRB
    (fun σ h => by obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := h; exact h10)
    (fun σ h => by obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := h; exact h9) hbody
  refine hloop.conseq ?_ ?_ le_rfl
  · rintro σ ⟨hT, h1', h2', h3', h4', h5', h6', h7', h8', h9'⟩
    refine ⟨by simpa using h1', by simpa using h2', by simpa using h3', by simpa using h4',
      by simpa using h5', by simpa using h6', by simpa using h7', by simpa using h8',
      by simpa using h9', by simp, by simp [hT, hL], ?_, ?_⟩
    · intro i hi _
      simp [hT]
    · intro r hr; simp at hr
  · rintro σ σ' - ⟨⟨-, -, -, -, -, -, -, -, -, -, hlen, hout, hin⟩, hri⟩
    rw [hri] at hout hin
    exact ⟨hlen, hout, hin⟩


theorem rowsLoop4_wvars : ∀ y ∈ rowsLoop4.wvars, y ∈ ["ri", "z1", "zr", "ct", "cf"] := by decide

theorem rowsLoop4_warrs : ∀ a ∈ rowsLoop4.warrs, a = "TAB" := by decide

/-- `rowsLoop4_core`, with its frame stated. -/
theorem rowsLoop4_spec {B : ℕ} (hB : 2 < B) (W R d q p wj zb1 zb2 zbc L : ℕ) (TAB0 : List ℕ)
    (hWB : W + 1 < B) (hwW : wj + W < B) (hdB : d + 1 < B) (hqB : q < B) (hpB : p < B)
    (hrp : R + p + q + 1 < B) (hwjB : wj < B) (hLB : L < B) (hRB : R + 1 < B)
    (hL : TAB0.length = L)
    (h1 : zbc + (R + 1) ≤ zb1) (h2 : zbc + (R + 1) ≤ zb2) (h1L : zb1 + (R + 1) ≤ L)
    (h2L : zb2 + (R + 1) ≤ L) (hcL : zbc + (R + 1) ≤ L)
    (hr1 : ∀ r, r < R + 1 → TAB0.getD (zb1 + r) 0 ≤ W)
    (hr2 : ∀ r, r < R + 1 → TAB0.getD (zb2 + r) 0 ≤ W) :
    Spec B (fun σ => σ.arrs "TAB" = TAB0 ∧ σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧
        σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧ σ.vars "W" = W ∧ σ.vars "cd" = d ∧
        σ.vars "cq" = q ∧ σ.vars "cp" = p ∧ σ.vars "R" = R + 1) rowsLoop4
      (fun σ σ' => (σ'.arrs "TAB").length = L ∧
        (∀ i, i < L → (i < zbc ∨ zbc + (R + 1) ≤ i) → (σ'.arrs "TAB").getD i 0 = TAB0.getD i 0) ∧
        (∀ r, r < R + 1 → (σ'.arrs "TAB").getD (zbc + r) 0 = cellVal4 W R d q p wj zb1 zb2 TAB0 r) ∧
        (∀ v, v ∉ ["ri", "z1", "zr", "ct", "cf"] → σ'.vars v = σ.vars v) ∧
        (∀ a, a ≠ "TAB" → σ'.arrs a = σ.arrs a))
      ((100 + 4) * (R + 1) + 6) := by
  refine ((rowsLoop4_core hB W R d q p wj zb1 zb2 zbc L TAB0 hWB hwW hdB hqB hpB hrp hwjB hLB hRB
    hL h1 h2 h1L h2L hcL hr1 hr2).frame).post ?_
  rintro σ σ' - ⟨⟨hl, ho, hc⟩, hfv, hfa, -, -⟩
  exact ⟨hl, ho, hc, fun v hv => hfv v (fun h => hv (rowsLoop4_wvars v h)),
    fun a ha => hfa a (fun h => ha (rowsLoop4_warrs a h))⟩

end Lax496464Proofs.Ram.D4Row
