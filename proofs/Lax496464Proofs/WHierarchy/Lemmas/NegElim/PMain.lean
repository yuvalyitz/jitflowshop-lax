import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PForm
import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLayout

/-! # The whole program

`body_run`: from the word in array `a`, the program writes `red x`. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PMain

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre Lax496464Proofs.WHierarchy.Lemmas.NegElim.PStr
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PForm Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWalk
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PDisp
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math

variable {x : List ℕ} {φ : Formula}

/-- The cost of the body. -/
def Kbody (x : List ℕ) : ℕ :=
  20 + (10 + ((44 * x.length + 60 + 4) * sOf x + 6)) + 5 +
  ((34 * x.length + 30 + 4) * nT x + 6) + ((44 * x.length + 30 + 4) * nT x + 6) + 20 +
  (40 * x.length + 40) + (((24 + 4) * MOf x + 10 + 4) * MOf x + 6 + 20) +
  (10 + ((Kw x + 100 + 4) * sOf x + 6)) + ((20 + 4) * x.length + 20) +
  ((20 + 4) * (2 * (x.length - bo x (sOf x))) + 20) +
  (20 + ((1 + (Cond.lt (L 0) (V "h")).size + (Kd x + 60)) * x.length + 1 +
    (Cond.lt (L 0) (V "h")).size))

theorem size_le_n (hd : Dom x φ) : φ.size ≤ x.length := by
  have := Lax496464Proofs.WHierarchy.Logic.FormulaCode.size_le_length_encode φ
  have := hd.fs_eq; omega

set_option maxHeartbeats 4000000 in
/-- **The body writes `red x`.** -/
theorem body_run {A : Structure} (h : EncodesMC x A φ) (hd : Dom x φ) {σ0 : Env}
    (ha : σ0.arrs "a" = x) (hn : σ0.vars "rt_n" = x.length)
    (hE : σ0.arrs "E" = List.replicate x.length 0) (hfo : σ0.arrs "fo" = List.replicate x.length 0)
    (hR : σ0.arrs "R" = List.replicate x.length 0)
    (hst : σ0.arrs "st" = List.replicate (x.length + 2) 0) :
    ∃ σ', Run (Bv x) body σ0 σ' (Kbody x) ∧ σ'.out = σ0.out ++ red x := by
  have hl := len_lt_Bv x
  have hbig := Bv_big x
  have hT := nT_le hd
  have hfs := hd.fs_le
  have hflen := hd.fs_eq
  have hsz := size_le_n hd
  have hcnt := cnt_le true φ
  have hM := MOf_le hd
  -- 1. header
  obtain ⟨σ1, hr1, ⟨hs1, hN1⟩, hk1, ho1⟩ := header_spec hd σ0 ha
  have ha1 : σ1.arrs "a" = x := by rw [hk1.2.1]; exact ha
  -- 2. entries
  obtain ⟨σ2, hr2, ha2, hs2, hp2, hT2, hE2⟩ := entPass_spec hd σ1
    ⟨ha1, hs1, by rw [hk1.2.1]; exact hE⟩
  -- 3. F0
  have hF0 : (V "p").evalB (Bv x) σ2 = some (bo x (sOf x)) := by
    rw [← hp2]; exact evalB_var (by rw [hp2]; omega)
  have hr3 : Run (Bv x) (.assign "F0" (V "p")) σ2 (σ2.setVar "F0" (bo x (sOf x))) 5 :=
    (Run.assign hF0).mono (by simp)
  set σ3 := σ2.setVar "F0" (bo x (sOf x)) with hσ3
  -- 4. first occurrences
  obtain ⟨σ4, hr4, hE4, hT4, hfo4⟩ := foPass_spec hd σ3
    ⟨by simp [hσ3, Env.setVar, hE2], by simp [hσ3, Env.setVar, hT2],
     by rw [hσ3]; simp only [Env.setVar]; rw [hr2.frame_arr "fo" (by decide), hk1.2.1]; exact hfo⟩
  -- 5. ranks
  obtain ⟨σ5, hr5, hR5⟩ := rkPass_spec hd σ4
    ⟨hE4, hfo4, hT4, by
      rw [hr4.frame_arr "R" (by decide), hσ3]; simp only [Env.setVar]
      rw [hr2.frame_arr "R" (by decide), hk1.2.1]; exact hR⟩
  -- frames through the reading phases
  have v5 : ∀ y, y ∉ ["s", "N"] → y ∉ entPass.wvars → y ≠ "F0" → y ∉ foPass.wvars →
      y ∉ rkPass.wvars → σ5.vars y = σ0.vars y := by
    intro y h1 h2 h3 h4 h5
    rw [hr5.frame_var y h5, hr4.frame_var y h4, hσ3]; simp only [Env.setVar]; rw [if_neg h3,
      hr2.frame_var y h2, hk1.1 y h1]
  have a5 : ∀ b, b ∉ entPass.warrs → b ∉ foPass.warrs → b ∉ rkPass.warrs →
      σ5.arrs b = σ0.arrs b := by
    intro b h2 h4 h5
    rw [hr5.frame_arr b h5, hr4.frame_arr b h4, hσ3]; simp only [Env.setVar]
    rw [hr2.frame_arr b h2, hk1.2.1]
  have hN5 : σ5.vars "N" = nOf x := by
    rw [hr5.frame_var "N" (by decide), hr4.frame_var "N" (by decide), hσ3]; simp only [Env.setVar]
    rw [if_neg (by decide), hr2.frame_var "N" (by decide), hN1]
  have hs5 : σ5.vars "s" = sOf x := by
    rw [hr5.frame_var "s" (by decide), hr4.frame_var "s" (by decide), hσ3]; simp only [Env.setVar]
    rw [if_neg (by decide), hs2]
  have hT5 : σ5.vars "T" = nT x := by rw [hr5.frame_var "T" (by decide), hT4]
  have hn5 : σ5.vars "rt_n" = x.length := by
    rw [v5 "rt_n" (by decide) (by decide) (by decide) (by decide) (by decide), hn]
  have ha5 : σ5.arrs "a" = x := by rw [a5 "a" (by decide) (by decide) (by decide), ha]
  have hF05 : σ5.vars "F0" = bo x (sOf x) := by
    rw [hr5.frame_var "F0" (by decide), hr4.frame_var "F0" (by decide), hσ3]; simp [Env.setVar]
  have hst5 : σ5.arrs "st" = List.replicate (x.length + 2) 0 := by
    rw [a5 "st" (by decide) (by decide) (by decide), hst]
  -- 6. the size of the compressed universe
  have hNB : nOf x < Bv x := by unfold nOf; exact getD_lt_Bv x _
  obtain ⟨σ6, hr6, hM6, hk6, ho6⟩ := Mcom_spec σ5 ⟨hN5, hT5, hn5, by omega, hNB⟩
  have ha6 : σ6.arrs "a" = x := by rw [hk6.2.1]; exact ha5
  have hs6 : σ6.vars "s" = sOf x := by rw [hk6.1 "s" (by decide)]; exact hs5
  have hR6 : σ6.arrs "R" = Rw x := by rw [hk6.2.1]; exact hR5
  -- 7–9. the structure
  obtain ⟨σ7, hr7, ho7⟩ := hdOut_value hd σ6 ⟨ha6, hs6, hM6⟩
  obtain ⟨σ8, hr8, ho8⟩ := ltOut_spec hd σ7
    (show σ7.vars "M" = MOf x by rw [hr7.frame_var "M" (by decide)]; exact hM6)
  obtain ⟨σ9, hr9, ho9⟩ := symPass_spec hd σ8
    ⟨by rw [hr8.frame_arr "a" (by decide), hr7.frame_arr "a" (by decide)]; exact ha6,
     by rw [hr8.frame_arr "R" (by decide), hr7.frame_arr "R" (by decide)]; exact hR6,
     by rw [hr8.frame_var "s" (by decide), hr7.frame_var "s" (by decide)]; exact hs6,
     by rw [hr8.frame_var "M" (by decide), hr7.frame_var "M" (by decide)]; exact hM6⟩
  have v9 : ∀ y, y ∉ hdOut.wvars → y ∉ ltOut.wvars → y ∉ symPass.wvars → y ∉ ["M"] →
      σ9.vars y = σ5.vars y := by
    intro y h7 h8 h9 h6
    rw [hr9.frame_var y h9, hr8.frame_var y h8, hr7.frame_var y h7, hk6.1 y h6]
  have a9 : ∀ b, b ∉ hdOut.warrs → b ∉ ltOut.warrs → b ∉ symPass.warrs →
      σ9.arrs b = σ5.arrs b := by
    intro b h7 h8 h9
    rw [hr9.frame_arr b h9, hr8.frame_arr b h8, hr7.frame_arr b h7, hk6.2.1]
  -- 10. the first fresh variable
  obtain ⟨σ10, hr10, hbb10, hk10, ho10⟩ := mxPass_spec (x := x) σ9
    ⟨by rw [a9 "a" (by decide) (by decide) (by decide)]; exact ha5,
     by rw [v9 "rt_n" (by decide) (by decide) (by decide) (by decide)]; exact hn5⟩
  -- 11. the quantifier block
  obtain ⟨σ11, hr11, ho11⟩ := qOut_spec (x := x) (b := bOf x) (f0 := bo x (sOf x)) hfs
    (by unfold bOf; omega) σ10
    ⟨by rw [hk10.1 "rt_n" (by decide), v9 "rt_n" (by decide) (by decide) (by decide) (by decide)];
        exact hn5,
     by rw [hk10.1 "F0" (by decide), v9 "F0" (by decide) (by decide) (by decide) (by decide)];
        exact hF05, hbb10⟩
  -- 12. the walk
  have hdrop : x.drop (bo x (sOf x)) = φ.encode := hd.drop_eq
  obtain ⟨σ12, hr12, ho12⟩ := trPass_spec (x := x) (φ := φ) (b := bOf x) (f0 := bo x (sOf x))
    hdrop hflen (by unfold bOf; omega) σ11
    ⟨by rw [hr11.frame_arr "a" (by decide), hk10.2.1, a9 "a" (by decide) (by decide) (by decide)];
        exact ha5,
     by rw [hr11.frame_arr "st" (by decide), hk10.2.1, a9 "st" (by decide) (by decide) (by decide)];
        exact hst5,
     by rw [hr11.frame_var "bb" (by decide)]; exact hbb10,
     by rw [hr11.frame_var "F0" (by decide), hk10.1 "F0" (by decide),
       v9 "F0" (by decide) (by decide) (by decide) (by decide)]; exact hF05⟩
  -- the run and the output
  refine ⟨σ12, (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq (hr8.seq
    (hr9.seq (hr10.seq (hr11.seq hr12))))))))))).mono (by unfold Kbody; omega), ?_⟩
  have o5 : σ5.out = σ0.out := by
    rw [hr5.out_eq (by decide), hr4.out_eq (by decide), hσ3]; simp only [Env.setVar]
    rw [hr2.out_eq (by decide), ho1]
  rw [ho12, ho11, ho10, ho9, ho8, ho7, ho6, o5]
  have hK : 2 * (x.length - bo x (sOf x)) = 2 * φ.encode.length := by omega
  rw [red, φOf_eq h, word_eq h hd, phiOf, encode_exBlock, hK]
  simp only [List.append_assoc, List.cons_append]

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PMain
