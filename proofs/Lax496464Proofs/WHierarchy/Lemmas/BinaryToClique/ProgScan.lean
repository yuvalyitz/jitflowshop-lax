import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval3

/-!
# Σ₁[2] Model Checking to Clique: the Scan of a Block

`scanC` sets `atr = 1` iff some tuple of the block of atom `am1` hits `(aw1, aw2)` (`memX`).
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgScan

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

theorem memN_zero (x : List ℕ) (sb sa w1 w2 : ℕ) : memN x sb sa w1 w2 0 = false := by
  simp [memN]

theorem memN_succ (x : List ℕ) (sb sa w1 w2 j : ℕ) :
    memN x sb sa w1 w2 (j + 1) = (memN x sb sa w1 w2 j || tupHit x sb sa w1 w2 j) := by
  simp [memN, List.range_succ, List.any_append]

/-- The invariant of the scan. -/
def SCI (x : List ℕ) (sb sa w1 w2 cnt : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "asb" = sb ∧ σ.vars "asa" = sa ∧
    σ.vars "aw1" = w1 ∧ σ.vars "aw2" = w2 ∧ σ.vars "acnt" = cnt ∧ σ.vars "asj" ≤ cnt ∧
    σ.vars "atr" = if memN x sb sa w1 w2 (σ.vars "asj") then 1 else 0

set_option maxHeartbeats 2000000 in
theorem scanBody_spec {x : List ℕ} {B sb sa w1 w2 cnt : ℕ} (hB : HB x B)
    (hbig : sb + 1 + cnt * sa + 2 < B) (hw1 : w1 < B) (hw2 : w2 < B) (hsa : sa < B)
    (hcntL : cnt ≤ x.length) :
    Spec B (fun σ => SCI x sb sa w1 w2 cnt σ ∧ σ.vars "asj" < cnt) scanBody
      (fun σ σ' => SCI x sb sa w1 w2 cnt σ' ∧ σ'.vars "asj" = σ.vars "asj" + 1) 60 := by
  have hent := hB.1
  have hL := ProgTok2.HB.len hB
  have hrdB : ∀ i, rd x i < B := rd_lt hent (by omega)
  intro σ ⟨⟨ha, hn, hsb, hsa', hw1', hw2', hcnt, hle, htr⟩, hlt⟩
  have hjm : σ.vars "asj" * sa ≤ cnt * sa := Nat.mul_le_mul_right _ hle
  have hpos : sb + 1 + σ.vars "asj" * sa + 1 < B := by omega
  have hsucc := memN_succ x sb sa w1 w2 (σ.vars "asj")
  have hjB : σ.vars "asj" + 1 < B := by omega
  unfold scanBody
  run_vcg [rdV_spec hent (by omega) "au1" "apos" 0, rdV_spec hent (by omega) "au2" "apos" 1]
  all_goals (try simp only [SCI])
  all_goals first
    | (simp_all [tupHit]; done)
    | (simp_all [tupHit]; omega)

theorem scanLoop_spec {x : List ℕ} {B sb sa w1 w2 cnt : ℕ} (hB : HB x B)
    (hbig : sb + 1 + cnt * sa + 2 < B) (hw1 : w1 < B) (hw2 : w2 < B) (hsa : sa < B)
    (hcntL : cnt ≤ x.length) :
    Spec B (fun σ => SCI x sb sa w1 w2 cnt (σ.setVar "asj" 0)) scanLoop
      (fun _ σ' => SCI x sb sa w1 w2 cnt σ' ∧ σ'.vars "asj" = cnt) ((60 + 4) * cnt + 6) := by
  have hL := ProgTok2.HB.len hB
  exact Spec.forRangeZero "asj" "acnt" (SCI x sb sa w1 w2 cnt) cnt 60 (by omega)
    (fun _ h => h.2.2.2.2.2.2.2.1) (fun _ h => h.2.2.2.2.2.2.1)
    (scanBody_spec hB hbig hw1 hw2 hsa hcntL)

theorem cntX_le (x : List ℕ) (sb : ℕ) : cntX x sb ≤ x.length := by
  unfold cntX; split_ifs <;> omega

set_option maxHeartbeats 2000000 in
/-- **The scan.** -/
theorem scanC_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
        σ.vars "am1" < (σ.arrs "ab").length ∧ σ.vars "am1" < B ∧
        (σ.arrs "ab").getD (σ.vars "am1") 0 ≤ x.length ∧ σ.vars "asa" ≤ Mmax x ∧
        σ.vars "aw1" < B ∧ σ.vars "aw2" < B) scanC
      (fun σ σ' => σ'.vars "atr" = if memX x ((σ.arrs "ab").getD (σ.vars "am1") 0) (σ.vars "asa")
        (σ.vars "aw1") (σ.vars "aw2") then 1 else 0) ((60 + 4) * x.length + 60) := by
  have hent := hB.1
  have hL := ProgTok2.HB.len hB
  have hW := hB.2
  intro σ ⟨ha, hn, hml, hmB, hsb, hsa, hw1, hw2⟩
  set sb := (σ.arrs "ab").getD (σ.vars "am1") 0 with hsbdef
  set sa := σ.vars "asa" with hsadef
  have hcnt := cntX_le x sb
  have hbig : sb + 1 + cntX x sb * sa + 2 < B := by
    have : cntX x sb * sa ≤ x.length * Mmax x := Nat.mul_le_mul hcnt hsa
    nlinarith
  have hsaB : sa < B := by nlinarith
  have hsbB : sb < B := by omega
  -- the prefix: asb, acnt, clamp, atr
  have hpre : Spec B (fun τ => τ = σ)
      (.seq (.assign "asb" (.get "ab" (V "am1")))
      (.seq (rdV "acnt" "asb" 0)
      (.seq (.ite (.lt (V "rt_n") (V "acnt")) (.assign "acnt" (V "rt_n")) .skip)
        (.assign "atr" (.lit 0)))))
      (fun _ τ' => SCI x sb sa (σ.vars "aw1") (σ.vars "aw2") (cntX x sb) (τ'.setVar "asj" 0)) 40 := by
    rintro τ rfl
    run_vcg [rdV_spec hent (by omega) "acnt" "asb" 0]
    all_goals first
      | omega
      | (simp [hn]; omega)
      | (simp [ha, hn]; omega)
      | (simp only [SCI, cntX]; simp_all [memN_zero])
      | (refine ⟨by simp [ha], by simp [hn], ?_, by omega⟩
         simp only [vars_setVar, ↓reduceIte, Nat.add_zero]; rw [← hsbdef]; exact hsbB)
      | (simp_all; omega)
      | (simp_all; exact rd_lt hent (by omega) _)
  obtain ⟨σ1, r1, h1⟩ := hpre σ rfl
  obtain ⟨σ2, r2, h2, hj⟩ := scanLoop_spec hB hbig hw1 hw2 hsaB hcnt σ1 h1
  refine ⟨σ2, (r1.seq r2).mono ?_, ?_⟩
  · have : (60 + 4) * cntX x sb ≤ (60 + 4) * x.length := Nat.mul_le_mul_left _ hcnt
    omega
  · show σ2.vars "atr" = _
    rw [h2.2.2.2.2.2.2.2.2, hj]; rfl

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgScan
