import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs

/-!
# Layouts for `body`

`body` and `readStruct` compile under every layout that contains their scalars and the array `a`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyOk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs

/-- The nesting depth of expressions `body` needs. -/
def bodyTemps : ℕ := 8

set_option maxHeartbeats 4000000 in
theorem body_ok (L : Layout) (hs : ∀ y ∈ bodyVars, y ∈ L.scalars) (ha : "a" ∈ L.arrays)
    (ht : bodyTemps ≤ L.temps) : Com.Ok L body := by
  have h1 := hs "b_o" (by simp [bodyVars])
  have h2 := hs "b_n" (by simp [bodyVars])
  have h3 := hs "b_base" (by simp [bodyVars])
  have h4 := hs "b_K0" (by simp [bodyVars])
  have h5 := hs "b_k" (by simp [bodyVars])
  have h6 := hs "b_N" (by simp [bodyVars])
  have h7 := hs "b_M" (by simp [bodyVars])
  have h8 := hs "b_s" (by simp [bodyVars])
  have h9 := hs "b_t" (by simp [bodyVars])
  have h10 := hs "b_f" (by simp [bodyVars])
  have h11 := hs "b_d" (by simp [bodyVars])
  have h12 := hs "b_off" (by simp [bodyVars])
  have h13 := hs "b_cs" (by simp [bodyVars])
  have h14 := hs "b_us" (by simp [bodyVars])
  have h15 := hs "b_ct" (by simp [bodyVars])
  have h16 := hs "b_ut" (by simp [bodyVars])
  unfold bodyTemps at ht
  simp [body, header, runOnes, pass1, pass2, pass3, pass4, rowCount, rowEmit, emitIf, adjCom,
    adjPrep, adjTest, bump, Com.Ok, Expr.Ok, Cond.Ok, condExpr, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    h10, h11, h12, h13, h14, h15, h16, ha]
  omega

set_option maxHeartbeats 4000000 in
theorem readStruct_ok (L : Layout) (hs : ∀ y ∈ readVars, y ∈ L.scalars) (ha : "a" ∈ L.arrays)
    (ht : bodyTemps ≤ L.temps) : Com.Ok L readStruct := by
  have h1 := hs "b_i" (by simp [readVars])
  have h2 := hs "b_v" (by simp [readVars])
  have h3 := hs "b_rn" (by simp [readVars])
  have h4 := hs "b_e" (by simp [readVars])
  unfold bodyTemps at ht
  simp [readStruct, onesRead, matLoop, bump, Com.Ok, Expr.Ok, Cond.Ok, condExpr, h1, h2, h3, h4, ha]
  omega

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyOk
