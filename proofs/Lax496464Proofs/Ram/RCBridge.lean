import Lax496464Proofs.Ram.CopyArr
import Lax496464Proofs.Ram.CsrWord
import Lax496464Proofs.Ram.Build

/-!
# From the Scan's Scratch Arrays to `Build.RC`

`ScanProg.lean`'s scan writes into `"OFFS"`/`"MEMS"` arrays sized generously (bounded by the
tape's length, since the true CSR size isn't known until the scan finishes) — but `Build.RC`
demands them sized *exactly* to the CSR data, in arrays literally named `"OFF"`/`"MEM"`
(`Build.lean`'s own programs read those two names verbatim). Since no IMP+ operation resizes
an array in place, the two can't be the same array: this file is the copy that bridges them,
built on `CopyArr.copyLoop`, landing the exact-sized result directly in `"OFF"`/`"MEM"` — the
names `Build.lean` reads.
-/

namespace Lax496464Proofs.Ram.RCBridge

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.CopyArr (copyLoop copyLoop_spec)
open Lax496464.HittingSet (Instance offset member universeSize setCount)
open Lax496464Proofs.Ram.CsrWord (csrWord membersOf setCount_csrWord offset_csrWord_last
  getD_csrWord_n)
open Lax496464Proofs.Ram.Build (RC)

abbrev V (s : String) : Expr := .var s

/-- Copy the scan's discovered CSR data from `"OFFS"`/`"MEMS"` into `"OFF"`/`"MEM"`, exactly
sized. Entirely uniform code — the bounds are read off `"m"` and `"OFFS"` itself
(`OFF[m] = offset (csrWord P k) P.m = (membersOf P).length`, `CsrWord.offset_csrWord_last`),
never a literal tied to any specific instance. -/
def bridgeCopy : Com :=
  .seq (.assign "cb" (.bin .add (V "m") (.lit 1)))
    (.seq (copyLoop "OFFS" "OFF" "ci" "cb")
      (.seq (.assign "cb2" (.get "OFFS" (V "m")))
        (copyLoop "MEMS" "MEM" "ci" "cb2")))

variable (P : Instance) (k : ℕ)

/-- **`bridgeCopy`, for arbitrary scan output.** The same program, the same proof shape, but
with no instance `P`/`k` in sight: `foff`/`fmem` stand for whatever values `"OFFS"`/`"MEMS"`
actually hold (genuine encoding or not — `bridgeCopy`'s code only ever reads them, never
checks them), and `foff m0 = L0` stands for the one structural fact the scan's own state
machine keeps as an invariant regardless of whether the tape is a genuine encoding (the
`m0`-th offset it recorded always equals the length of the member data it recorded). This is
what the total top-level program needs, since it runs `bridgeCopy` before it knows whether the
tape decoded to anything meaningful. -/
theorem bridgeCopy_spec_generic {B m0 L0 : ℕ} (foff fmem : ℕ → ℕ)
    (hm0B : m0 + 1 < B) (hL0B : L0 + 1 < B)
    (hOffValB : ∀ j ≤ m0, foff j < B) (hMemValB : ∀ t < L0, fmem t < B) :
    Spec B (fun σ => σ.vars "m" = m0 ∧ (σ.arrs "OFFS").length ≥ m0 + 1 ∧
        (σ.arrs "OFF").length = m0 + 1 ∧ (σ.arrs "MEM").length = L0 ∧
        (σ.arrs "MEMS").length ≥ L0 ∧
        (∀ j ≤ m0, (σ.arrs "OFFS").getD j 0 = foff j) ∧ foff m0 = L0 ∧
        (∀ t < L0, (σ.arrs "MEMS").getD t 0 = fmem t))
      bridgeCopy
      (fun _ σ' => (σ'.arrs "OFF").length = m0 + 1 ∧ (σ'.arrs "MEM").length = L0 ∧
        (∀ j ≤ m0, (σ'.arrs "OFF").getD j 0 = foff j) ∧
        (∀ t < L0, (σ'.arrs "MEM").getD t 0 = fmem t))
      ((1 + 4) + ((1 + 3 + 4 + 4) * (m0 + 1) + 6) + (1 + 4) +
        ((1 + 3 + 4 + 4) * L0 + 6)) := by
  intro σ0 ⟨hm0, hOFFge0, hOFF2len0, hMEM2len0, hMEMge0, hOFFcorr0, hLeq, hMEMcorr0⟩
  -- Step 1: cb := m + 1
  have hev0 : (V "m").evalB B σ0 = some (σ0.vars "m") := evalB_var (σ := σ0) (x := "m") (by omega)
  rw [hm0] at hev0
  have hev1 : (Expr.bin Bop.add (V "m") (.lit 1)).evalB B σ0 = some (m0 + 1) :=
    evalB_bin hev0 (evalB_lit (B := B) (n := 1) (by omega)) (by simp only [Bop.apply]; omega)
  have hrun1 := Run.assign (B := B) (σ := σ0) (x := "cb") hev1
  set σ1 := σ0.setVar "cb" (m0 + 1) with hσ1def
  have hm1 : σ1.vars "m" = m0 := by simp [hσ1def, Env.setVar, hm0]
  have hcb1 : σ1.vars "cb" = m0 + 1 := by simp [hσ1def, Env.setVar]
  have hOFF1 : σ1.arrs "OFFS" = σ0.arrs "OFFS" := by simp [hσ1def, Env.setVar]
  have hOFF21 : σ1.arrs "OFF" = σ0.arrs "OFF" := by simp [hσ1def, Env.setVar]
  have hMEM1 : σ1.arrs "MEMS" = σ0.arrs "MEMS" := by simp [hσ1def, Env.setVar]
  have hMEM21 : σ1.arrs "MEM" = σ0.arrs "MEM" := by simp [hσ1def, Env.setVar]
  -- Step 2: copyLoop "OFFS" "OFF" "ci" "cb"
  obtain ⟨σ2, hrun2, hq2⟩ := copyLoop_spec (B := B) "OFFS" "OFF" "ci" "cb" (m0 + 1)
    foff (σ1.arrs "OFF")
    (fun σ => σ.vars "cb" = m0 + 1 ∧ σ.arrs "OFFS" = σ1.arrs "OFFS")
    (by omega) (fun i hi => hOffValB i (by omega)) (σ1.arrs "OFFS").length
    (by rw [hOFF1]; exact hOFFge0) (by rw [hOFF21, hOFF2len0])
    (hix := fun σ v ⟨h1, h2⟩ => ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2]⟩)
    (harr := fun σ i v ⟨h1, h2⟩ => ⟨by simp [Env.setArr, h1], by simp [Env.setArr, h2]⟩)
    (hbd := fun σ ⟨h1, h2⟩ => h1)
    (hsrclen := fun σ ⟨h1, h2⟩ => by rw [h2])
    (hsrc := fun σ ⟨h1, h2⟩ i hi => by
      rw [h2, hOFF1]; exact hOFFcorr0 i (by omega))
    σ1 ⟨⟨hcb1, rfl⟩, hOFF21⟩
  obtain ⟨⟨hcb2, hOFF2⟩, hOFF2len2, hOFFcorr2, hOFFrest2⟩ := hq2
  have hm2 : σ2.vars "m" = m0 := by
    have := hrun2.frame_var "m" (by decide); rw [this, hm1]
  have hMEM2 : σ2.arrs "MEMS" = σ1.arrs "MEMS" := hrun2.frame_arr "MEMS" (by decide)
  have hMEM2_2 : σ2.arrs "MEM" = σ1.arrs "MEM" := hrun2.frame_arr "MEM" (by decide)
  -- Step 3: cb2 := OFF[m]
  have hOFFlen2 : (σ2.arrs "OFFS").length ≥ m0 + 1 := by rw [hOFF2, hOFF1]; exact hOFFge0
  have hidxOFF2 : m0 < (σ2.arrs "OFFS").length := by omega
  have hOFFmval : (σ2.arrs "OFFS").getD m0 0 = L0 := by
    rw [hOFF2, hOFF1]; rw [hOFFcorr0 m0 le_rfl]; exact hLeq
  have hOFFmk : (σ2.arrs "OFFS")[m0]? = some L0 := by
    rw [List.getElem?_eq_getElem hidxOFF2]
    congr 1
    rwa [List.getD_eq_getElem (σ2.arrs "OFFS") 0 hidxOFF2] at hOFFmval
  have hevm2 : (V "m").evalB B σ2 = some (σ2.vars "m") := evalB_var (σ := σ2) (x := "m") (by omega)
  rw [hm2] at hevm2
  have hev2 : (Expr.get "OFFS" (V "m")).evalB B σ2 = some L0 :=
    evalB_get hevm2 hOFFmk (by omega)
  have hrun3 := Run.assign (B := B) (σ := σ2) (x := "cb2") hev2
  set σ3 := σ2.setVar "cb2" L0 with hσ3def
  have hcb2v3 : σ3.vars "cb2" = L0 := by simp [hσ3def, Env.setVar]
  have hMEM3 : σ3.arrs "MEMS" = σ1.arrs "MEMS" := by
    have : σ3.arrs "MEMS" = σ2.arrs "MEMS" := by simp [hσ3def, Env.setVar]
    rw [this, hMEM2]
  have hMEM23 : σ3.arrs "MEM" = σ1.arrs "MEM" := by
    have : σ3.arrs "MEM" = σ2.arrs "MEM" := by simp [hσ3def, Env.setVar]
    rw [this, hMEM2_2]
  have hOFF23 : σ3.arrs "OFF" = σ2.arrs "OFF" := by simp [hσ3def, Env.setVar]
  -- Step 4: copyLoop "MEMS" "MEM" "ci" "cb2"
  obtain ⟨σ4, hrun4, hq4⟩ := copyLoop_spec (B := B) "MEMS" "MEM" "ci" "cb2" L0
    fmem (σ3.arrs "MEM")
    (fun σ => σ.vars "cb2" = L0 ∧ σ.arrs "MEMS" = σ1.arrs "MEMS")
    (by omega) (fun i hi => hMemValB i hi) (σ3.arrs "MEMS").length
    (by rw [hMEM3, hMEM1]; exact hMEMge0)
    (by rw [hMEM23, hMEM21, hMEM2len0])
    (hix := fun σ v ⟨h1, h2⟩ => ⟨by simp [Env.setVar, h1], by simp [Env.setVar, h2]⟩)
    (harr := fun σ i v ⟨h1, h2⟩ => ⟨by simp [Env.setArr, h1], by simp [Env.setArr, h2]⟩)
    (hbd := fun σ ⟨h1, h2⟩ => h1)
    (hsrclen := fun σ ⟨h1, h2⟩ => by rw [h2, hMEM3])
    (hsrc := fun σ ⟨h1, h2⟩ i hi => by rw [h2, hMEM1]; exact hMEMcorr0 i hi)
    σ3 ⟨⟨hcb2v3, hMEM3⟩, rfl⟩
  obtain ⟨⟨hcb4, hMEM4⟩, hMEM2len4, hMEMcorr4, hMEMrest4⟩ := hq4
  have hOFF24 : σ4.arrs "OFF" = σ3.arrs "OFF" := (hrun4.frame_arr "OFF" (by decide))
  refine ⟨σ4, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hrun1.seq (hrun2.seq (hrun3.seq hrun4))).mono (by simp only [Expr.size]; omega)
  · rw [hOFF24, hOFF23, hOFF2len2, hOFF21, hOFF2len0]
  · rw [hMEM2len4, hMEM23, hMEM21, hMEM2len0]
  · intro j hj
    rw [hOFF24, hOFF23]
    exact hOFFcorr2 j (by omega)
  · exact hMEMcorr4

end Lax496464Proofs.Ram.RCBridge
