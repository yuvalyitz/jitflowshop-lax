import Lax496464.WH_F4_IndependentSetToMcc
import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyStmt
import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyRead
import Lax496464Proofs.WHierarchy.MccNP.Ram.BodyOk

/-!
# The running time in the parameter

The IMP+ program `readStruct; body` is compiled under a layout of its scalars and the array `a`, and
the transfer theorem turns its verified run into the word RAM bound `c * (k + 1) ^ 2 * (|x| + 1)`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.FptTimeProof

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax888481.ParameterizedComplexity Lax496464.WH_F1_IndependentSetMatrix
open Lax496464.WH_F2_MccConstruction (reduce)
open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs Lax496464Proofs.WHierarchy.MccNP.Ram.BodyOk Lax496464Proofs.WHierarchy.MccNP.Ram

/-- The layout: the scalars of the reader and of the body, the array `a`. -/
def layout : Layout := ⟨readVars ++ bodyVars, ["a"], bodyTemps⟩

/-- The whole program: read the word into `a`, then write the reduction. -/
def cmd : Com := .seq readStruct body

/-- The value bound. -/
noncomputable def Bfpt (x : List ℕ) : ℕ := Bbody x + 1

/-- The cost bound. -/
noncomputable def Kfpt (x : List ℕ) : ℕ := (24 * x.length + 60) + Kbody x

theorem cmd_ok : Com.Ok layout cmd := by
  refine ⟨readStruct_ok layout ?_ (by simp [layout]) (by simp [layout]),
    body_ok layout ?_ (by simp [layout]) (by simp [layout])⟩
  · intro y hy; simp [layout, hy]
  · intro y hy; simp [layout, hy]

theorem length_lt_Bbody (x : List ℕ) : x.length + 2 < Bfpt x := by
  unfold Bfpt Bbody; omega

theorem solves {D : Set (List ℕ)} (hD : D ⊆ Instances) :
    Solves layout cmd D reduce Bfpt Kfpt where
  ok := cmd_ok
  inp := by
    intro x hx v hv
    have hv' := BodyHead.entries_le_one (Shape.valid_iff_mem.mpr (hD hx)) v hv
    have := length_lt_Bbody x
    omega
  run := by
    intro x hx
    have hv := Shape.valid_iff_mem.mpr (hD hx)
    have hB := length_lt_Bbody x
    let ext : String → ℕ := fun a => if a = "a" then x.length else 0
    refine ⟨ext, ?_⟩
    obtain ⟨σ1, r1, h1⟩ := BodyRead.readStruct_spec hv (B := Bfpt x) hB (initEnv ext x)
      ⟨rfl, by simp [initEnv, ext]⟩
    obtain ⟨σ2, r2, h2⟩ := body_spec hv (B := Bfpt x) (by unfold Bfpt; omega) σ1 h1.1
    refine ⟨σ2, (r1.seq r2).mono le_rfl, ?_⟩
    rw [h2.1, h1.2.2.1, Shape.reduce_valid hv]
    simp [initEnv]

theorem threshold_eq {x : List ℕ} (hx : Shape.Valid x) : threshold x = Shape.kOf x := by
  have h := Shape.threshold_word (Shape.decode x)
  rw [Shape.word_decode hx, Shape.threshold_decode hx] at h
  exact h

theorem Bbody_eq {x : List ℕ} (hx : Shape.Valid x) :
    Bbody x = x.length + BodyMath.nOf x + BodyMath.psum x (BodyMath.nOf x) + 2 := by
  unfold Bbody
  rw [BodyMain.Mx_eq' hx]
  rfl

theorem fits_of {w : ℕ} {x : List ℕ} (hi : x ∈ Instances) (hfx : Fits 20000 w x)
    (hfr : Fits 20000 w (reduce x)) : layout.FitsWords (Bfpt x) w := by
  have hv := Shape.valid_iff_mem.mpr hi
  have hlen := hv.2.1
  have hx0 : 0 < x.length := by omega
  have h1 := hfx x[0] (List.getElem_mem hx0)
  have hr : reduce x = Lax496464.WH_F2_MccConstruction.word (Shape.decode x) := Shape.reduce_valid hv
  have h2 := hfr (BodyMath.nOf x) (by rw [hr]; exact mem_word_nOf hv)
  have h3 := hfr (BodyMath.psum x (BodyMath.nOf x)) (by rw [hr]; exact mem_word_psum hv)
  have hb := Bbody_eq hv
  have hsq := BodyAdj.sq_bound hv
  refine fitsWords_of_max_le (by unfold Bfpt; omega) ?_
  simp only [Layout.span, layout, readVars, bodyVars, bodyTemps, List.length_append, List.length_cons,
    List.length_nil, max_le_iff, Bfpt]
  constructor <;> omega

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.reduce_fptTime
---
The reduction is computed by one word RAM program, the compilation of the IMP+ program that reads
the word into an array, using its own structure, and then writes the word of the multicoloured
graph: the number of vertices, the number of edges, the offsets, the targets and the colours, each
computed by a pass over all ordered pairs of copies. The program runs within
`c (k + 1)² (|x| + 1)` instructions, and every value it computes is below the value bound that
the fitting conditions on the word and on its image provide.
-/
theorem reduce_fptTime_proved :
    ∃ (prog : Program) (c : ℕ), ∀ w : ℕ,
      ComputesInTime w prog
        {x | x ∈ problem.Domain ∧ Fits c w x ∧ Fits c w (reduce x)}
        reduce (fun x => c * (problem.param x + 1) ^ 2 * (x.length + 1)) := by
  refine ⟨compileProgram layout cmd, 20000, fun w => ?_⟩
  have hs := solves (D := {x | x ∈ Instances ∧ Fits 20000 w x ∧ Fits 20000 w (reduce x)})
    (fun x hx => hx.1)
  refine computesInTime_of_solves hs ?_ ?_
  · rintro x ⟨hi, hfx, hfr⟩
    exact fits_of hi hfx hfr
  · rintro x ⟨hi, -, -⟩
    have hv := Shape.valid_iff_mem.mpr hi
    change _ ≤ 20000 * (threshold x + 1) ^ 2 * (x.length + 1)
    rw [threshold_eq hv]
    simp only [Kfpt, Kbody, bodyC, Layout.const]
    set P := (Shape.kOf x + 1) ^ 2 * (x.length + 1) with hP
    have e1 : 1200 * (Shape.kOf x + 1) ^ 2 * (x.length + 1) = 1200 * P := by rw [hP]; ring
    have e2 : 20000 * (Shape.kOf x + 1) ^ 2 * (x.length + 1) = 20000 * P := by rw [hP]; ring
    have h1 : x.length + 1 ≤ P :=
      Nat.le_mul_of_pos_left _ (by positivity)
    rw [e1, e2]
    omega

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_fptTime := reduce_fptTime_proved

end Lax496464Proofs.WHierarchy.MccNP.Ram.FptTimeProof
