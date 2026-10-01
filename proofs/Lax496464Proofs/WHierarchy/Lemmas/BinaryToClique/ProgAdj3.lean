import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj2

/-! # Σ₁[2] model checking to Clique: the atom test, assembled

`atomC_spec`: when the two rows are the two rows of one atom, the atom test sets its flag exactly
when the atom has the truth value the valuation gives it (`atomOK_eq`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj3

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgScan
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj1 Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj2
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

theorem atomOK_eq (x : List ℕ) (c r1 r2 v1 v2 : ℕ) :
    atomOK (paramsX x) c r1 r2 v1 v2 = decide (atomT x (r1 / 2) (if r1 < r2 then v1 else v2)
      (if r1 < r2 then v2 else v1) = bitv c (r1 / 2)) := rfl

set_option maxHeartbeats 2000000 in
/-- **The atom test.** -/
theorem atomC_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
        σ.arrs "ab" = pad (tok x).ab (x.length + 1) ∧ σ.arrs "ar" = pad (tok x).ar (x.length + 1) ∧
        σ.vars "am1" = σ.vars "r1" / 2 ∧ σ.vars "am1" < qX x ∧ σ.vars "r1" < B ∧
        σ.vars "r2" < B ∧ σ.vars "av1" < B ∧ σ.vars "av2" < B ∧ σ.vars "c1" < B)
      atomC
      (fun σ σ' => σ'.vars "gf" = if atomOK (paramsX x) (σ.vars "c1") (σ.vars "r1") (σ.vars "r2")
        (σ.vars "av1") (σ.vars "av2") then 1 else σ.vars "gf") ((60 + 4) * x.length + 200) := by
  have hW := hB.2
  have hL := ProgTok2.HB.len hB
  have hB2 : 2 < B := by nlinarith
  have hqL := ProgElb.qX_le x
  have hsm := tok_small x
  have hshape := (ProgTokLoop.tok_shape x).1
  intro σ ⟨ha, hn, hab, har, hm, hmq, hr1, hr2, hv1, hv2, hc1⟩
  have hab_l : (tok x).ab.length = qX x := rfl
  have har_l : (tok x).ar.length = qX x := by rw [hshape.2.2]; rfl
  -- order the values
  obtain ⟨σ1, r1, e1⟩ := ordA_spec (B := B) σ ⟨hr1, hr2, hv1, hv2⟩
  set W1 := if σ.vars "r1" < σ.vars "r2" then σ.vars "av1" else σ.vars "av2" with hW1
  set W2 := if σ.vars "r1" < σ.vars "r2" then σ.vars "av2" else σ.vars "av1" with hW2
  have hW1B : W1 < B := by rw [hW1]; split_ifs <;> assumption
  have hW2B : W2 < B := by rw [hW2]; split_ifs <;> assumption
  obtain ⟨σ2, r2, e2⟩ := abt_spec (B := B) σ1 ⟨by rw [e1]; simpa using hc1,
    by rw [e1]; simp; omega, hB2⟩
  have hmB : σ.vars "am1" < B := by omega
  have harv : (σ.arrs "ar").getD (σ.vars "am1") 0 = (tok x).ar.getD (σ.vars "am1") 0 := by
    rw [har, getD_pad]
  have harB : (tok x).ar.getD (σ.vars "am1") 0 ≤ Mmax x := getD_le_of hsm.2.1 _
  have habv : (σ.arrs "ab").getD (σ.vars "am1") 0 = (tok x).ab.getD (σ.vars "am1") 0 := by
    rw [hab, getD_pad]
  have habB : (tok x).ab.getD (σ.vars "am1") 0 ≤ x.length := getD_le_of hsm.1 _
  have harv' : (σ.arrs "ar")[σ.vars "am1"]?.getD 0 = (tok x).ar[σ.vars "am1"]?.getD 0 := by
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]; exact harv
  have habv' : (σ.arrs "ab")[σ.vars "am1"]?.getD 0 = (tok x).ab[σ.vars "am1"]?.getD 0 := by
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]; exact habv
  have harB' : (tok x).ar[σ.vars "am1"]?.getD 0 ≤ Mmax x := by
    rw [← List.getD_eq_getElem?_getD]; exact harB
  have habB' : (tok x).ab[σ.vars "am1"]?.getD 0 ≤ x.length := by
    rw [← List.getD_eq_getElem?_getD]; exact habB
  have harlen : (σ.arrs "ar").length = x.length + 1 := by rw [har, length_pad (by omega)]
  have hablen : (σ.arrs "ab").length = x.length + 1 := by rw [hab, length_pad (by omega)]
  obtain ⟨σ3, r3, e3⟩ := asa_spec (B := B) σ2 ⟨by rw [e2, e1]; simp; omega,
    by rw [e2, e1]; simp [harlen]; omega, by rw [e2, e1]; simp; rw [harv']; nlinarith⟩
  obtain ⟨σ4, r4, h4⟩ := iteB_spec hB σ3 ⟨by rw [e3, e2, e1]; simp [ha], by rw [e3, e2, e1]; simp [hn],
    by rw [e3, e2, e1]; simp [hablen]; omega, by rw [e3, e2, e1]; simp; omega,
    by rw [e3, e2, e1]; simp; rw [habv']; exact habB',
    by rw [e3, e2, e1]; simp; rw [harv']; exact harB',
    by rw [e3, e2, e1]; simp [hW1B], by rw [e3, e2, e1]; simp [hW2B]⟩
  have f4 : ∀ y, y ∉ iteB.wvars → σ4.vars y = σ3.vars y := fun y hy => r4.frame_var y hy
  have hatr : σ4.vars "atr" = atomT x (σ.vars "am1") W1 W2 := by
    rw [h4, e3, e2, e1]
    simp only [vars_setVar, arrs_setVar]
    simp [harv', habv', atomT]
  have hatrB : σ4.vars "atr" ≤ 1 := by
    rw [hatr]; unfold atomT; split_ifs <;> omega
  have habt : σ4.vars "abt" = bitv (σ.vars "c1") (σ.vars "am1") := by
    rw [f4 "abt" (by decide), e3, e2, e1]; simp
  have hgf : σ4.vars "gf" = σ.vars "gf" := by
    rw [f4 "gf" (by decide), e3, e2, e1]; simp
  obtain ⟨σ5, r5, e5⟩ := fin_spec (B := B) σ4 ⟨by omega,
    by rw [habt]; exact lt_of_le_of_lt (bitv_le_one _ _) (by omega), by omega⟩
  refine ⟨σ5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by omega), ?_⟩
  show σ5.vars "gf" = _
  rw [e5, atomOK_eq, ← hm, hatr, habt, ← hW1, ← hW2]
  by_cases hq : atomT x (σ.vars "am1") W1 W2 = bitv (σ.vars "c1") (σ.vars "am1")
  · rw [if_pos hq]; simp [hq]
  · rw [if_neg hq]; simp [hq, hgf]

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj3
