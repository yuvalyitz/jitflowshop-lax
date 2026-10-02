import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgGph
import Lax496464Proofs.WHierarchy.Machine.ReadTape

/-!
# Σ₁[2] Model Checking to Clique: the Whole Program

`prog` reads the tape and runs the five phases; from the initial environment (arrays sized by
`ext`) it writes `reduce x`. Also the layout and `Com.Ok`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax496464Proofs.WHierarchy.Machine.ReadTape
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj5 Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRow
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgPass Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgGph
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-- **The program.** -/
def prog : Com := .seq readTape body

/-- The array lengths, for the word `x`. -/
def ext (x : List ℕ) (a : String) : ℕ :=
  if a = "a" then x.length
  else if a = "bs" then sX x
  else if a = "nt" ∨ a = "na" ∨ a = "ab" ∨ a = "ar" ∨ a = "st" then x.length + 1
  else if a = "vs" then 2 * x.length + 2
  else if a = "el" then ProgElb.elN x
  else if a = "ok" then CX x
  else 0

/-- The cost of the body. -/
def Kbody (x : List ℕ) : ℕ :=
  ((60 + 4) * sX x + 40) + ((280 + 4) * x.length + 20) +
    ((30 + 4) * x.length + (30 + 4) * limX x + 40) +
    (((120 + 4) * x.length + 60 + 4) * CX x + 20) + Kg x

set_option maxHeartbeats 4000000 in
/-- **The body** writes the reduction. -/
theorem body_spec {x : List ℕ} {B : ℕ} (hB : BOK x B) (σ0 : Env)
    (ha : σ0.arrs "a" = x) (hn : σ0.vars "rt_n" = x.length) (hout : σ0.out = [])
    (harr : ∀ a, a ≠ "a" → σ0.arrs a = List.replicate (ext x a) 0) :
    Spec B (fun σ => σ = σ0) body (fun _ σ' => σ'.out = reduce x) (Kbody x) := by
  rintro σ rfl
  have hH : HB x B := hB.1.1.1
  have hAB : AB x B := hB.1.1
  have hC : CX x < B := hAB.2.2
  have hL := ProgTok2.HB.len hH
  have hW := hH.2
  have hM : Mmax x + 3 < B := by nlinarith
  have hext : ∀ a, a ≠ "a" → (σ.arrs a) = List.replicate (ext x a) 0 := harr
  -- header
  obtain ⟨σ1, r1, a1, n1, s1, p1, bs1, N1⟩ := hdr_value hH σ ⟨ha, hn, by rw [hext "bs" (by decide)]; rfl⟩
  have fa1 : ∀ a, a ∉ hdr.warrs → σ1.arrs a = σ.arrs a := fun a h => r1.frame_arr a h
  have fv1 : ∀ y, y ∉ hdr.wvars → σ1.vars y = σ.vars y := fun y h => r1.frame_var y h
  -- tokenizer
  obtain ⟨σ2, r2, c2⟩ := ProgTokLoop.tokz_spec hH σ1 ⟨a1, n1, s1, bs1, p1,
    by rw [fa1 "nt" (by decide), hext "nt" (by decide)]; rfl,
    by rw [fa1 "na" (by decide), hext "na" (by decide)]; rfl,
    by rw [fa1 "vs" (by decide), hext "vs" (by decide)]; rfl,
    by rw [fa1 "ab" (by decide), hext "ab" (by decide)]; rfl,
    by rw [fa1 "ar" (by decide), hext "ar" (by decide)]; rfl⟩
  have fa2 : ∀ a, a ∉ tokz.warrs → σ2.arrs a = σ1.arrs a := fun a h => r2.frame_arr a h
  have fv2 : ∀ y, y ∉ tokz.wvars → σ2.vars y = σ1.vars y := fun y h => r2.frame_var y h
  obtain ⟨a2, n2, -, -, -, T2, q2, fl2, nt2, na2, vs2, ab2, ar2⟩ := c2
  -- candidates
  obtain ⟨σ3, r3, k3, ne3, el3⟩ := ProgElb.elb_value hH σ2 ⟨a2, n2, q2,
    by rw [fv2 "zN" (by decide), N1], fl2,
    by rw [fa2 "el" (by decide), fa1 "el" (by decide), hext "el" (by decide)]; rfl⟩
  have fa3 : ∀ a, a ∉ elb.warrs → σ3.arrs a = σ2.arrs a := fun a h => r3.frame_arr a h
  have fv3 : ∀ y, y ∉ elb.wvars → σ3.vars y = σ2.vars y := fun y h => r3.frame_var y h
  -- evaluation
  obtain ⟨σ4, r4, C4, ok4⟩ := ProgEval3.evl_value hC hL hM σ3 ⟨by rw [fv3 "zq" (by decide), q2]; rfl,
    by rw [fv3 "zT" (by decide), T2], by rw [fa3 "nt" (by decide), nt2],
    by rw [fa3 "na" (by decide), na2],
    by rw [fa3 "st" (by decide), fa2 "st" (by decide), fa1 "st" (by decide), hext "st" (by decide)]
       simp [ext],
    by rw [fa3 "ok" (by decide), fa2 "ok" (by decide), fa1 "ok" (by decide), hext "ok" (by decide)]
       rfl⟩
  have fa4 : ∀ a, a ∉ evl.warrs → σ4.arrs a = σ3.arrs a := fun a h => r4.frame_arr a h
  have fv4 : ∀ y, y ∉ evl.wvars → σ4.vars y = σ3.vars y := fun y h => r4.frame_var y h
  -- graph
  obtain ⟨σ5, r5, o5⟩ := gph_spec hB σ4 ⟨⟨by rw [fa4 "a" (by decide), fa3 "a" (by decide), a2],
    by rw [fv4 "rt_n" (by decide), fv3 "rt_n" (by decide), n2],
    by rw [fa4 "ab" (by decide), fa3 "ab" (by decide), ab2],
    by rw [fa4 "ar" (by decide), fa3 "ar" (by decide), ar2],
    by rw [fa4 "el" (by decide), el3], by rw [fa4 "vs" (by decide), fa3 "vs" (by decide), vs2],
    ok4, by rw [fv4 "zk" (by decide), k3], by rw [fv4 "zne" (by decide), ne3]⟩, C4⟩
  have o4 : σ4.out = σ3.out := r4.out_eq (by decide)
  have o3 : σ3.out = σ2.out := r3.out_eq (by decide)
  have o2 : σ2.out = σ1.out := r2.out_eq (by decide)
  have o1 : σ1.out = σ.out := r1.out_eq (by decide)
  refine ⟨σ5, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono (by unfold Kbody; omega), ?_⟩
  show σ5.out = reduce x
  rw [o5, o4, o3, o2, o1, hout, List.nil_append]

/-- **The run.** -/
theorem prog_spec (x : List ℕ) {B : ℕ} (hB : BOK x B) :
    Spec B (fun σ => σ = initEnv (ext x) (x.length :: x)) prog (fun _ σ' => σ'.out = reduce x)
      (16 * x.length + 7 + Kbody x) := by
  have hH : HB x B := hB.1.1.1
  have hL := ProgTok2.HB.len hH
  rintro σ rfl
  obtain ⟨σ1, r1, ha, hn, -, hout, -, harrs⟩ := readTape_spec x (initEnv (ext x) (x.length :: x))
    hH.1 (by omega) rfl (by simp [initEnv, ext]) _ rfl
  obtain ⟨σ2, r2, h2⟩ := body_spec hB σ1 ha hn (by rw [hout]; rfl)
    (fun a ha' => by rw [harrs a ha']; simp [initEnv]) σ1 rfl
  exact ⟨σ2, r1.seq r2, h2⟩

/-! ### The layout -/

/-- The scalars of the program. -/
def scalars : List String :=
  ["rt_n", "rt_i", "rt_v", "zs", "zp", "zhi", "zhc", "zhw", "znx", "zN", "zT", "zq", "zfl", "ztt",
    "zg", "zi", "zn", "zy1", "zy2", "zw", "zk", "zlim", "zne", "zei", "zv", "zej", "zC", "zc",
    "zsp", "zet", "zj", "zm", "zh", "zNG", "gM", "gs", "gt", "gd", "gf", "goff"] ++ adjVars

/-- The layout. -/
def layout : Layout :=
  ⟨scalars, ["a", "bs", "nt", "na", "vs", "ab", "ar", "el", "st", "ok"], 8⟩

set_option maxHeartbeats 8000000 in
theorem prog_ok : Com.Ok layout prog := by
  simp [layout, scalars, adjVars, prog, body, readTape, readLoop, readBody, hdr, hdrLoop, hdrBody,
    rdV, tokz, tokLoop, tokBody, tokStepC, relC, relVars, relSym, pushNode, pushVars, eqC, otherC,
    elb, elLoop1, elBody1, elLoop2, elBody2, evl, evBody, evLoop, evStepC, opC, pushBit, negC, andC,
    orC, gph, pass1, pass2, pass3, rowCount, rowEmit, emitIf, adjCom, decC, testC, rowsC, rowsA,
    atomC, scanC, scanLoop, scanBody, bump, Lax496464Proofs.WHierarchy.Machine.ReadTape.V, ProgDefs.V,
    Com.Ok, Expr.Ok, Cond.Ok, condExpr]

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTop
