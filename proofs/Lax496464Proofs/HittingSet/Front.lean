import Lax496464Proofs.HittingSet.Correct
import Lax391470Proofs.L2Main

/-!
# Reading and Scanning the Word

The archive's reader puts the bits into an array; its finite-state scan of a formula's
encoding leaves the literals in three flat arrays — indices, signs, clause numbers — with
their number, the number of clauses and one more than the largest index in scalars. If the
scan rejects, the fallback sets the scalars of the formula with one empty clause.
-/

namespace Lax496464Proofs.HittingSet.Front

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax429075.Encoding Lax496464.HittingSetFromSat
open Lax391470Proofs.CnfScan Lax391470Proofs.L2ScanModel Lax391470Proofs.L2Scan
open Lax391470Proofs.Bits Lax391470Proofs.L2Main

abbrev V (s : String) : Expr := .var s
abbrev set (x : String) (n : ℕ) : Com := .assign x (.lit n)

/-- The formula with one empty clause: `C = 1`, no literals, one variable. -/
def reject : Com := .seq (set "C" 1) (.seq (set "k" 0) (set "mx" 1))

/-- Read, scan, fall back. -/
def front : Com :=
  .seq Lax391470Proofs.ReadAll.readAll
    (.seq (set "mx" 1) (.seq scanLoop (.ite (.eq (V "ph") (.lit 4)) .skip reject)))

/-- The array sizes: the word's length for the scan's arrays, twice that plus four for the
marks, which is at least the size of the universe. -/
def ext (n : ℕ) (a : String) : ℕ :=
  if a ∈ ["a", "vr", "sg", "cl"] then n else if a = "mark" then 2 * n + 4 else 0

/-- The formula the input stands for. -/
def Fof (y : List ℕ) : Formula := parseF (bitsOf y)

theorem Fof_accept {y : List ℕ} (h : (run init (bitsOf y)).ph = 4) :
    Fof y = (run init (bitsOf y)).done := by
  unfold Fof parseF; rw [decodeCNF_eq, if_pos h]; rfl

theorem Fof_reject {y : List ℕ} (h : ¬ (run init (bitsOf y)).ph = 4) : Fof y = [[]] := by
  unfold Fof parseF; rw [decodeCNF_eq, if_neg h]; rfl

/-- The default literal of an out-of-range lookup. -/
def dflt : Literal := ⟨0, false⟩

/-- The scan's arrays present `F`. -/
structure Post (F : Formula) (vr sg cl : List ℕ) : Prop where
  hvr : ∀ i < (lits F).length, vr.getD i 0 = ((lits F).getD i dflt).index
  hsg : ∀ i < (lits F).length, sg.getD i 0 = if ((lits F).getD i dflt).positive then 1 else 0
  hcl : ∀ i < (lits F).length, cl.getD i 0 = (cn F).getD i 0

theorem reads_scan : ¬ scanLoop.reads := by
  simp [scanLoop, scanBody, dispatch, phase3, Com.reads]

theorem bound_eq_mxOf (F : Formula) : bound F = mxOf (lits F) := rfl

/-- What the scan and the fallback leave: the formula's dimensions and its arrays. -/
structure Scanned (y : List ℕ) (σ : Env) : Prop where
  hC : σ.vars "C" = (Fof y).length
  hk : σ.vars "k" = (lits (Fof y)).length
  hmx : σ.vars "mx" = bound (Fof y)
  post : Post (Fof y) (σ.arrs "vr") (σ.arrs "sg") (σ.arrs "cl")
  lvr : (σ.arrs "vr").length = y.length
  lsg : (σ.arrs "sg").length = y.length
  lcl : (σ.arrs "cl").length = y.length
  hsz : (lits (Fof y)).length ≤ y.length
  hFl : (Fof y).length ≤ y.length + 1
  hbd : bound (Fof y) ≤ y.length + 1
  hmark : σ.arrs "mark" = List.replicate (2 * y.length + 4) 0
  hout : σ.out = []
  hinp : σ.inp = []

variable {B : ℕ}

/-- The cost of the reading, scanning and fallback. -/
def Kscan (L : ℕ) : ℕ := (12 * L + 10) + 2 + (64 * L + 6) + 10

theorem scan_spec (y : List ℕ) (hyB : ∀ v ∈ y, v < B) (hB : y.length + 8 < B) :
    ∃ σ', Run B front (initEnv (ext y.length) (y.length :: y)) σ' (Kscan y.length) ∧
      Scanned y σ' := by
  obtain ⟨σ0, hσ0⟩ : ∃ σ0, initEnv (ext y.length) (y.length :: y) = σ0 := ⟨_, rfl⟩
  rw [hσ0]
  -- read
  obtain ⟨σ1, r1, ⟨hL1, ha1, ho1, hi1⟩, fv1, fa1, -, -⟩ :=
    (Lax391470Proofs.ReadAll.readAll_spec (B := B) (y := y) hyB (by omega)).frame σ0
      ⟨by rw [← hσ0]; rfl, by rw [← hσ0]; rfl, by rw [← hσ0]; simp [initEnv, ext]⟩
  have z1 : ∀ x, x ∉ ["L", "rt", "rv"] → σ1.vars x = 0 := fun x hx => by
    rw [fv1 x (by rw [wvars_readAll]; simp only [List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hx ⊢; tauto)]
    rw [← hσ0]; rfl
  have ar1 : ∀ a, a ≠ "a" → σ1.arrs a = List.replicate (ext y.length a) 0 :=
    fun a ha => by rw [fa1 a (by simp [warrs_readAll, ha]), ← hσ0]; rfl
  -- mx := 1
  have r2 : Run B (set "mx" 1) σ1 (σ1.setVar "mx" 1) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  -- scan
  obtain ⟨σ3, r3, ⟨I3, p3⟩, fv3, fa3, fi3, -⟩ := (scanLoop_spec (B := B) (y := y) hB hyB).frame
    (σ1.setVar "mx" 1) (by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp only [Env.setVar]
    all_goals try simp [stAt, bitsOf, init, flat, lits, nums, cn, mxOf]
    · exact z1 "ph" (by decide)
    · exact z1 "n" (by decide)
    · exact z1 "C" (by decide)
    · exact z1 "k" (by decide)
    · exact ha1
    · exact hL1
    · rw [ar1 "vr" (by decide)]; simp [ext]
    · rw [ar1 "sg" (by decide)]; simp [ext]
    · rw [ar1 "cl" (by decide)]; simp [ext]
    · exact ho1)
  obtain ⟨hR, -, -, -, lvr, lsg, lcl, out3⟩ := I3
  have hst : stAt y (σ3.vars "p") = run init (bitsOf y) := by
    rw [p3]; unfold stAt; rw [List.take_length]
  rw [hst] at hR
  have hphB : σ3.vars "ph" < B := by
    rw [hR.ph]; have := ph_run_le (bitsOf y); omega
  have hev : (Cond.eq (.var "ph") (.lit 4)).evalB B σ3 = some (σ3.vars "ph" == 4) :=
    evalB_condEq (evalB_var hphB) (evalB_lit (by omega))
  have mk3 : σ3.arrs "mark" = List.replicate (2 * y.length + 4) 0 := by
    rw [fa3 "mark" (by rw [warrs_scan]; decide)]
    show σ1.arrs "mark" = _
    rw [ar1 "mark" (by decide)]; simp [ext]
  have inp3 : σ3.inp = [] := by rw [fi3 reads_scan]; simp [Env.setVar, hi1]
  have hsz := size_run (bitsOf y)
  have hl : (bitsOf y).length = y.length := by simp [bitsOf]
  rw [hl] at hsz
  simp only [Lax391470Proofs.L2ScanModel.size, Nat.max_le] at hsz
  obtain ⟨⟨-, hszf⟩, hszd, hszm⟩ := hsz
  have hseq : ∀ {σ' K}, Run B (.ite (.eq (V "ph") (.lit 4)) .skip reject) σ3 σ' K →
      Run B front σ0 σ' ((12 * y.length + 10) + (2 + ((64 * y.length + 6) + K))) :=
    fun h => r1.seq (r2.seq (r3.seq h))
  by_cases h4 : (run init (bitsOf y)).ph = 4
  · -- accept
    have hF := Fof_accept h4
    have hc := cur_nil h4
    have hflat : flat (run init (bitsOf y)) = lits (run init (bitsOf y)).done := by
      simp [flat, hc]
    have hnums : nums (run init (bitsOf y)) = cn (run init (bitsOf y)).done := by
      simp [nums, hc]
    have e1 := hR.vr; have e2 := hR.sg; have e3 := hR.cl
    rw [hflat] at e1 e2 e3; rw [hnums] at e3
    have hk := hR.k; rw [hflat] at hk
    have hmx := hR.mx; rw [hflat, ← bound_eq_mxOf] at hmx
    have hc4 : σ3.vars "ph" = 4 := by rw [hR.ph, h4]
    refine ⟨σ3, (hseq (Run.ite_true (by rw [hev, hc4]; rfl) Run.skip)).mono (by
      unfold Kscan; simp [Cond.size, Expr.size]; omega), ?_⟩
    rw [hflat] at hszf hszm
    have hC := hR.C
    rw [← hF] at hk hmx hC e1 e2 e3 hszf hszd hszm
    refine ⟨hC, hk, hmx, ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩, lvr, lsg, lcl,
      hszf, by omega, by rw [bound_eq_mxOf]; omega, mk3, out3, inp3⟩
    · rw [getD_of_take _ _ _ hi, e1, getD_map _ _ dflt _ hi]
    · rw [getD_of_take _ _ _ hi, e2, getD_map _ _ dflt _ hi]
    · rw [getD_of_take _ _ _ hi, e3]
  · -- reject: the formula with one empty clause
    have hF := Fof_reject h4
    have hc4 : ¬ σ3.vars "ph" = 4 := by rw [hR.ph]; exact h4
    have rr : Run B reject σ3 (((σ3.setVar "C" 1).setVar "k" 0).setVar "mx" 1) 6 :=
      ((Run.assign (evalB_lit (by omega))).seq ((Run.assign (evalB_lit (by omega))).seq
        (Run.assign (evalB_lit (by omega))))).mono (by simp [Expr.size])
    refine ⟨_, (hseq (Run.ite_false (by rw [hev]; simp [hc4]) rr)).mono (by
      unfold Kscan; simp [Cond.size, Expr.size]; omega), ?_⟩
    have hl0 : (lits [[]]).length = 0 := rfl
    refine ⟨by simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [hF]; rfl,
      by simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [hF]; rfl,
      by simp only [Env.setVar, ↓reduceIte]; rw [hF]; rfl,
      ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩,
      by simpa [Env.setVar] using lvr, by simpa [Env.setVar] using lsg,
      by simpa [Env.setVar] using lcl, by rw [hF, hl0]; omega,
      by rw [hF]; simp, by rw [hF]; show 1 ≤ _; omega, by simpa [Env.setVar] using mk3,
      by simpa [Env.setVar] using out3, by simpa [Env.setVar] using inp3⟩
    all_goals rw [hF, hl0] at hi; omega

end Lax496464Proofs.HittingSet.Front
