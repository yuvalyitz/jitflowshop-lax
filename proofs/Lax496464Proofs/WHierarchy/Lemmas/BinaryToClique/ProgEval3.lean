import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval2

/-!
# Σ₁[2] model checking to Clique: the evaluation under every valuation

`evl` fills `ok[c] = okv x c` for every `c < 2^q`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval3

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTokLoop
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval1 Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval2
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

set_option maxHeartbeats 1000000 in
theorem okStore_spec {B S : ℕ} (l : List ℕ) :
    Spec B (fun σ => SI S l σ ∧ σ.vars "zc" < (σ.arrs "ok").length ∧ σ.vars "zc" < B ∧ S < B ∧
        2 < B)
      (.ite (.eq (V "zsp") (.lit 0)) (.store "ok" (V "zc") (.lit 0))
        (.store "ok" (V "zc") (.get "st" (.sub (V "zsp") (.lit 1)))))
      (fun σ σ' => σ' = σ.setArr "ok" (σ.vars "zc") (l.headD 0)) 20 := by
  rcases l with _ | ⟨v, t⟩
  · intro σ ⟨h, hc, hcB, hS, h2⟩
    have hle := h.le
    have h0 : σ.vars "zsp" = 0 := h.1
    run_vcg
    all_goals first
      | (simp at *; omega)
      | simp_all
  · intro σ ⟨h, hc, hcB, hS, h2⟩
    have hle := h.le
    have h3 : (σ.arrs "st").length = S := h.2.2.1
    have h0 : σ.vars "zsp" = t.length + 1 := h.1
    have htop := top_val h
    have hv := h.head_le
    run_vcg
    all_goals first
      | (simp at *; omega)
      | (rw [htop]; omega)
      | (rw [htop]; rfl)

/-- The invariant of the loop over the valuations. -/
def OI (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "zC" = CX x ∧ σ.vars "zc" ≤ CX x ∧ σ.vars "zT" = (tok x).nd.length ∧
    σ.arrs "nt" = pad ((tok x).nd.map Prod.fst) (x.length + 1) ∧
    σ.arrs "na" = pad ((tok x).nd.map Prod.snd) (x.length + 1) ∧
    (σ.arrs "st").length = x.length + 1 ∧
    σ.arrs "ok" = pad ((List.range (σ.vars "zc")).map (okv x)) (CX x)

theorem okv_eq_sfx (x : List ℕ) (c : ℕ) : okv x c = (sfx x c (tok x).nd.length).headD 0 := by
  rw [sfx_all]; rfl

set_option maxHeartbeats 2000000 in
theorem evBody_spec {x : List ℕ} {B : ℕ} (hC : CX x < B) (hL : 2 * x.length + 6 < B)
    (hM : Mmax x + 3 < B) :
    Spec B (fun σ => OI x σ ∧ σ.vars "zc" < CX x) evBody
      (fun σ σ' => OI x σ' ∧ σ'.vars "zc" = σ.vars "zc" + 1)
      ((120 + 4) * x.length + 60) := by
  intro σ ⟨⟨hzC, hle, hT, hnt, hna, hst, hok⟩, hlt⟩
  have hTL := (tok_shape x).2
  set c := σ.vars "zc" with hcdef
  have hcB : c < B := by omega
  -- zsp := 0
  have r1 : Run B (.assign "zsp" (.lit 0)) σ (σ.setVar "zsp" 0) 2 := by
    have := Run.assign (x := "zsp") (σ := σ) (evalB_lit (n := 0) (B := B) (by omega))
    simpa using this
  have hI1 : EVI x c ((σ.setVar "zsp" 0).setVar "zet" 0) := by
    refine ⟨by simp [hcdef], by simp [hT], by simp [hnt], by simp [hna], by simp, ?_⟩
    simp only [vars_setVar, ↓reduceIte, sfx_zero]
    exact ⟨by simp, holds_nil _, by simp [hst], by simp [Bits]⟩
  obtain ⟨σ2, r2, ⟨hc2, hT2, hnt2, hna2, -, hSI2⟩, het2⟩ :=
    evLoop_spec hcB hL hM (σ.setVar "zsp" 0) hI1
  rw [het2] at hSI2
  have f2 : ∀ y, y ∉ evLoop.wvars → σ2.vars y = (σ.setVar "zsp" 0).vars y := fun y hy =>
    r2.frame_var y hy
  have fa2 : ∀ a, a ∉ evLoop.warrs → σ2.arrs a = (σ.setVar "zsp" 0).arrs a := fun a ha =>
    r2.frame_arr a ha
  have hok2 : σ2.arrs "ok" = pad ((List.range c).map (okv x)) (CX x) := by
    rw [fa2 "ok" (by decide)]; simpa using hok
  have hzC2 : σ2.vars "zC" = CX x := by rw [f2 "zC" (by decide)]; simpa using hzC
  have hst2 : (σ2.arrs "st").length = x.length + 1 := hSI2.2.2.1
  have lok : (σ2.arrs "ok").length = CX x := by
    rw [hok2, length_pad (by simp; omega)]
  obtain ⟨σ3, r3, e3⟩ := okStore_spec (B := B) (S := x.length + 1) (sfx x c (tok x).nd.length) σ2
    ⟨hSI2, by rw [hc2, lok]; omega, by rw [hc2]; omega, by omega, by omega⟩
  rw [hc2] at e3
  have hv : (Expr.add (V "zc") (.lit 1)).evalB B σ3 = some (c + 1) := by
    have := evalB_bin (op := .add) (evalB_var (x := "zc") (σ := σ3) (B := B)
      (by rw [e3]; simp [hc2]; omega)) (evalB_lit (n := 1) (σ := σ3) (B := B) (by omega))
      (by rw [e3]; simp [hc2]; omega)
    rw [e3] at this; simp [hc2] at this; rw [e3]; simpa [hc2] using this
  have r4 : Run B (bump "zc") σ3 (σ3.setVar "zc" (c + 1)) 4 := by
    have := Run.assign (x := "zc") hv
    simpa using this
  refine ⟨_, ((r1.seq (r2.seq (r3.seq r4)))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [hcdef]⟩
  · simp; nlinarith
  · simp [e3, hzC2]
  · simp; omega
  · simp [e3]; rw [f2 "zT" (by decide)]; simpa using hT
  · simp [e3, hnt2]
  · simp [e3, hna2]
  · simp [e3, hst2]
  · simp only [vars_setVar, ↓reduceIte, arrs_setVar, e3, arrs_setArr]
    rw [hok2, ← okv_eq_sfx, pad_set' (by simp) (by simp; omega)]
    simp [List.range_succ]

theorem evLoopC_spec {x : List ℕ} {B : ℕ} (hC : CX x < B) (hL : 2 * x.length + 6 < B)
    (hM : Mmax x + 3 < B) :
    Spec B (fun σ => OI x σ) (.while (.lt (V "zc") (V "zC")) evBody)
      (fun _ σ' => OI x σ' ∧ σ'.vars "zc" = CX x)
      (((120 + 4) * x.length + 60 + 4) * CX x + 4) :=
  Spec.forRange "zc" "zC" (OI x) (CX x) ((120 + 4) * x.length + 60) _
    (fun _ h => by have := h.2.1; omega) (fun _ h => by rw [h.1]; exact hC) (fun _ h => h.1)
    (fun _ h => h.2.1) (evBody_spec hC hL hM) (fun _ h => h)
    (fun _ _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.sub_le _ _)) 4)

set_option maxHeartbeats 2000000 in
/-- **The evaluation.** -/
theorem evl_value {x : List ℕ} {B : ℕ} (hC : CX x < B) (hL : 2 * x.length + 6 < B)
    (hM : Mmax x + 3 < B) :
    Spec B (fun σ => σ.vars "zq" = qX x ∧ σ.vars "zT" = (tok x).nd.length ∧
        σ.arrs "nt" = pad ((tok x).nd.map Prod.fst) (x.length + 1) ∧
        σ.arrs "na" = pad ((tok x).nd.map Prod.snd) (x.length + 1) ∧
        (σ.arrs "st").length = x.length + 1 ∧ σ.arrs "ok" = List.replicate (CX x) 0) evl
      (fun _ σ' => σ'.vars "zC" = CX x ∧ σ'.arrs "ok" = (List.range (CX x)).map (okv x))
      (((120 + 4) * x.length + 60 + 4) * CX x + 20) := by
  unfold evl
  intro σ ⟨hq, hT, hnt, hna, hst, hok⟩
  have hqL := Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgElb.qX_le x
  have hpow : 1 * 2 ^ σ.vars "zq" = CX x := by rw [hq]; simp [CX]
  run_vcg [evLoopC_spec hC hL hM]
  all_goals first
    | omega
    | (obtain ⟨⟨hzC, -, -, -, -, -, hok'⟩, hc⟩ := ‹OI x _ ∧ _›
       rw [hc] at hok'
       exact ⟨hzC, by rw [hok']; unfold pad; simp⟩)
    | (refine ⟨by simp [hpow], by simp, by simp [hT], by simp [hnt], by simp [hna], by simp [hst],
        by simp [hok, pad_nil]⟩)

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval3
