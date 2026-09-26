import Lax496464Proofs.Ram.D2Scan1
import Lax496464Proofs.Ram.Col1
import Lax496464Proofs.Ram.Dp1

/-!
# Theorem 2's machine, part 2: the cells of one set

For the set with number `c`, whose `X₁` and `X₂` have numbers `c₁, c₂ > c`, the `W+1` cells of its
row block are `T[c,r] = max(T[c₁,r], f(T[c₂, r ∸ w_j]))`, each `O(1)`: two lookups, `fNat`, a
comparison and one store.  The array is `TAB`, the cell of (number `c`, weight `r`) at `c·R + r`.
-/

namespace Lax496464Proofs.Ram.D2Rows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.Dp1 (fNat)
open Lax496464Proofs.Ram.Col1 (fCom fCom_spec)

/-- One cell of the row block. -/
def rowBody : Com :=
  .seq (.assign "z1" (.get "TAB" (.bin .add (V "zb1") (V "ri"))))
    (.seq (.assign "zr" (.bin .sub (V "ri") (V "wj")))
      (.seq (.assign "ct" (.get "TAB" (.bin .add (V "zb2") (V "zr"))))
        (.seq fCom
          (.seq (.ite (.lt (V "z1") (V "cf")) (.assign "z1" (V "cf")) .skip)
            (.seq (.store "TAB" (.bin .add (V "zbc") (V "ri")) (V "z1")) (bump "ri"))))))

theorem rowBody_spec {B : ℕ} (hB : 2 < B) (inf d q p wj zb1 zb2 zbc ri t1 t2 : ℕ)
    (hinfB : inf < B) (ht1 : t1 ≤ inf) (ht2 : t2 ≤ inf) (hdB : d + 1 < B) (hqB : q < B)
    (hpB : p < B) (hpq : p + q < B) (hi1 : zb1 + ri < B) (hi2 : zb2 + (ri - wj) < B)
    (hi3 : zbc + ri < B) (hriB : ri + 1 < B) (hwjB : wj < B) (hriB' : ri < B) :
    Spec B (fun σ => σ.vars "ri" = ri ∧ σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧
        σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧ σ.vars "cinf" = inf ∧ σ.vars "cd" = d ∧
        σ.vars "cq" = q ∧ σ.vars "cp" = p ∧
        (σ.arrs "TAB").getD (zb1 + ri) 0 = t1 ∧ zb1 + ri < (σ.arrs "TAB").length ∧
        (σ.arrs "TAB").getD (zb2 + (ri - wj)) 0 = t2 ∧ zb2 + (ri - wj) < (σ.arrs "TAB").length ∧
        zbc + ri < (σ.arrs "TAB").length) rowBody
      (fun σ σ' => σ'.arrs "TAB" = (σ.arrs "TAB").set (zbc + ri) (max t1 (fNat inf t2 d q p)) ∧
        σ'.vars "ri" = ri + 1) 100 := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hri, hzb1, hzb2, hzbc, hwj, hinf, hd, hq, hp, hg1, hl1, hg2, hl2, hl3⟩ := hσ
  have hf_le : fNat inf t2 d q p ≤ d + 1 := Lax496464Proofs.Ram.Col1.fNat_le inf t2 d q p
  have hfc := fCom_spec (B := B) hB inf t2 d q p hinfB (by omega) (by omega) hqB hpB hpq hdB
  have ht1B : t1 < B := by omega
  run_vcg [hfc]
  all_goals (simp_all)
  all_goals (try omega)
  all_goals rw [max_eq_right (by omega)]

/-- The value of cell `r` of the block, from the array as it was before the block was written. -/
def cellVal (inf d q p wj zb1 zb2 : ℕ) (TAB0 : List ℕ) (r : ℕ) : ℕ :=
  max (TAB0.getD (zb1 + r) 0) (fNat inf (TAB0.getD (zb2 + (r - wj)) 0) d q p)

/-- All the cells of the block. -/
def rowsLoop : Com :=
  .seq (.assign "ri" (.lit 0)) (.while (.lt (V "ri") (V "R")) rowBody)

/-- What the loop over the cells keeps. -/
def RInv (inf d q p wj zb1 zb2 zbc R L : ℕ) (TAB0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧ σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧
  σ.vars "cinf" = inf ∧ σ.vars "cd" = d ∧ σ.vars "cq" = q ∧ σ.vars "cp" = p ∧ σ.vars "R" = R ∧
  σ.vars "ri" ≤ R ∧ (σ.arrs "TAB").length = L ∧
  (∀ i, i < L → (i < zbc ∨ zbc + σ.vars "ri" ≤ i) → (σ.arrs "TAB").getD i 0 = TAB0.getD i 0) ∧
  (∀ r, r < σ.vars "ri" → (σ.arrs "TAB").getD (zbc + r) 0 = cellVal inf d q p wj zb1 zb2 TAB0 r)

theorem rowsLoop_spec {B : ℕ} (hB : 2 < B) (inf d q p wj zb1 zb2 zbc R L : ℕ) (TAB0 : List ℕ)
    (hinfB : inf < B) (hdB : d + 1 < B) (hqB : q < B) (hpB : p < B) (hpq : p + q < B)
    (hwjB : wj < B) (hLB : L < B) (hRB : R < B) (hL : TAB0.length = L)
    (h1 : zbc + R ≤ zb1) (h2 : zbc + R ≤ zb2) (h1L : zb1 + R ≤ L) (h2L : zb2 + R ≤ L)
    (hcL : zbc + R ≤ L)
    (hr1 : ∀ r, r < R → TAB0.getD (zb1 + r) 0 ≤ inf)
    (hr2 : ∀ r, r < R → TAB0.getD (zb2 + r) 0 ≤ inf) :
    Spec B (fun σ => σ.arrs "TAB" = TAB0 ∧ σ.vars "zb1" = zb1 ∧ σ.vars "zb2" = zb2 ∧
        σ.vars "zbc" = zbc ∧ σ.vars "wj" = wj ∧ σ.vars "cinf" = inf ∧ σ.vars "cd" = d ∧
        σ.vars "cq" = q ∧ σ.vars "cp" = p ∧ σ.vars "R" = R) rowsLoop
      (fun _σ σ' => (σ'.arrs "TAB").length = L ∧
        (∀ i, i < L → (i < zbc ∨ zbc + R ≤ i) → (σ'.arrs "TAB").getD i 0 = TAB0.getD i 0) ∧
        (∀ r, r < R → (σ'.arrs "TAB").getD (zbc + r) 0 = cellVal inf d q p wj zb1 zb2 TAB0 r))
      ((100 + 4) * R + 6) := by
  have hbody : Spec B (fun σ => RInv inf d q p wj zb1 zb2 zbc R L TAB0 σ ∧ σ.vars "ri" < R)
      rowBody (fun σ σ' => RInv inf d q p wj zb1 zb2 zbc R L TAB0 σ' ∧
        σ'.vars "ri" = σ.vars "ri" + 1) 100 := by
    refine Spec.of_exists fun σ ⟨hI, hlt⟩ => ?_
    obtain ⟨hzb1, hzb2, hzbc, hwj, hinf, hd, hq, hp, hR, hri, hlen, hout, hin⟩ := hI
    have hread1 : (σ.arrs "TAB").getD (zb1 + σ.vars "ri") 0 = TAB0.getD (zb1 + σ.vars "ri") 0 :=
      hout _ (by omega) (Or.inr (by omega))
    have hread2 : (σ.arrs "TAB").getD (zb2 + (σ.vars "ri" - wj)) 0 =
        TAB0.getD (zb2 + (σ.vars "ri" - wj)) 0 :=
      hout _ (by omega) (Or.inr (by omega))
    obtain ⟨σ', hrun, ⟨hset, hri'⟩, hfv, hfa, -, -⟩ :=
      (rowBody_spec hB inf d q p wj zb1 zb2 zbc (σ.vars "ri") (TAB0.getD (zb1 + σ.vars "ri") 0)
        (TAB0.getD (zb2 + (σ.vars "ri" - wj)) 0) hinfB (hr1 _ hlt)
        (hr2 _ (by omega)) hdB hqB hpB hpq (by omega) (by omega) (by omega) (by omega) hwjB
        (by omega)).frame.run
        ⟨rfl, hzb1, hzb2, hzbc, hwj, hinf, hd, hq, hp, hread1, by omega,
          hread2, by omega, by omega⟩
    refine ⟨σ', 100, hrun, le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hri'⟩
    · rw [hfv "zb1" (by decide)]; exact hzb1
    · rw [hfv "zb2" (by decide)]; exact hzb2
    · rw [hfv "zbc" (by decide)]; exact hzbc
    · rw [hfv "wj" (by decide)]; exact hwj
    · rw [hfv "cinf" (by decide)]; exact hinf
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
        unfold cellVal
        rfl
  have hloop := Spec.forRangeZero (B := B) (c := rowBody) "ri" "R"
    (RInv inf d q p wj zb1 zb2 zbc R L TAB0) R 100 hRB
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

end Lax496464Proofs.Ram.D2Rows
