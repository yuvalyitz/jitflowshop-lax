import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx

/-!
# Decoding Blocks and Values; Phase B

`decB_spec`, `decV_spec`: the slots of block `b` (base `k+1`) and the values `v` (base `N+1`) into
an array of length `D`. `phaseB_spec`: phase B writes the words of the block clauses.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseB

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (Ctx Frame BF Frame.refl Frame.trans Frame.mono
  Frame.setVar)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.OutW
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx

variable {B : ℕ} {Dt : Data} {x : List ℕ}

/-! ### Decoding -/

/-- Decode the scalar `src` into the array `arr` of length `D`, in the base in `bs`. -/
theorem dec_spec {src arr bs : String} (hbs : bs ≠ "g_w") {n w0 D : ℕ}
    (hnB : n < B) (hw0 : w0 < B) (hDB : D < B) :
    Spec B (fun σ => σ.vars src = w0 ∧ σ.vars bs = n ∧ (σ.arrs arr).length = D)
      (.seq (.assign "g_w" (V src)) (decG arr "g_w" bs 0 D))
      (fun σ σ' => σ'.arrs arr = digits n D w0 ∧ Frame ["g_w"] [arr] σ σ' ∧ σ'.out = σ.out)
      (20 * D + 3) := by
  intro σ ⟨hs, hb, hl⟩
  have hr1 := RunStep.assign B σ "g_w" (V src) w0 (by rw [← hs]; exact evalB_var (by rw [hs]; exact hw0))
  obtain ⟨σ2, hr2, a2, f2, o2⟩ := decG_spec (B := B) (arr := arr) (w := "g_w") (bs := bs)
    (Ne.symm hbs) hnB (L := D) D 0 w0 hw0 (by omega) (by omega) (σ.setVar "g_w" w0)
    ⟨by simp [Env.setVar], by simp [Env.setVar, hbs, hb], by simp [Env.setVar, hl]⟩
  refine ⟨σ2, (hr1.seq hr2).mono (by simp [Expr.size]; omega), ?_,
    (Frame.setVar σ (by simp) _).trans f2, by rw [o2]; rfl⟩
  rw [a2]
  have : (σ.setVar "g_w" w0).arrs arr = σ.arrs arr := rfl
  rw [this, List.drop_of_length_le (by omega)]
  simp

/-- The digits of block `b`. -/
theorem decB_spec (hB : BB Dt x B) {src arr : String} {b : ℕ}
    (hb : b < (par Dt x).W) :
    Spec B (fun σ => GC Dt x σ ∧ σ.vars src = b ∧ (σ.arrs arr).length = Dt.D) (decB src arr Dt.D)
      (fun σ σ' => σ'.arrs arr = (par Dt x).bd b ∧ Frame ["g_w"] [arr] σ σ' ∧ σ'.out = σ.out)
      (20 * Dt.D + 3) := by
  have hs := hB.small
  refine (dec_spec (B := B) (by decide) (n := kW x + 1) (by omega) (by omega) (by omega)).pre ?_
  rintro σ ⟨hg, h1, h2⟩
  exact ⟨h1, hg.k1, h2⟩

/-- The digits of values `v`. -/
theorem decV_spec (hB : BB Dt x B) {src arr : String} {v : ℕ}
    (hv : v < (par Dt x).C) :
    Spec B (fun σ => GC Dt x σ ∧ σ.vars src = v ∧ (σ.arrs arr).length = Dt.D) (decV src arr Dt.D)
      (fun σ σ' => σ'.arrs arr = (par Dt x).vd v ∧ Frame ["g_w"] [arr] σ σ' ∧ σ'.out = σ.out)
      (20 * Dt.D + 3) := by
  have hs := hB.small
  refine (dec_spec (B := B) (by decide) (n := nU Dt x ^ Dt.s + 1) (by omega) (by omega)
    (by omega)).pre ?_
  rintro σ ⟨hg, h1, h2⟩
  exact ⟨h1, hg.M, h2⟩

theorem digits_bd_lt {k D b : ℕ} : ∀ j, (digits (k + 1) D b).getD j 0 ≤ k := by
  intro j
  rw [List.getD_eq_getElem?_getD]
  rcases h : (digits (k + 1) D b)[j]? with _ | d
  · simp
  · have := digits_lt (n := k + 1) (by omega) D b d (List.mem_of_getElem? h)
    simp; omega

/-! ### Phase B -/

theorem flatMap_single (l : List ℕ) (f : ℕ → ℕ) : l.flatMap (fun e => [f e]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

set_option maxHeartbeats 1000000 in
theorem litWrite_spec (hB : BB Dt x B) {b e : ℕ} (hb : b < (par Dt x).W) (he : e < (par Dt x).C)
    (bv ev : String) :
    Spec B (fun σ => σ.vars bv = b ∧ σ.vars ev = e ∧ σ.vars "g_W" = (par Dt x).W)
      (.write (litE bv ev))
      (fun σ σ' => σ'.out = σ.out ++ [2 * (par Dt x).zv b e] ∧ σ' = { σ with out := σ'.out }) 10 := by
  obtain ⟨l1, l2, l3, l4⟩ := hB.lit_lt hb he
  have hs := hB.small
  intro σ ⟨h1, h2, h3⟩
  have eb : (V bv).evalB B σ = some b := by rw [← h1]; exact evalB_var (by rw [h1]; omega)
  have ee : (V ev).evalB B σ = some e := by rw [← h2]; exact evalB_var (by rw [h2]; omega)
  have eW : (V "g_W").evalB B σ = some (par Dt x).W := by
    rw [← h3]; exact evalB_var (by rw [h3]; omega)
  have e1 : (Expr.lit 1).evalB B σ = some 1 := evalB_lit (by omega)
  have e2 : (Expr.lit 2).evalB B σ = some 2 := evalB_lit (by omega)
  have ea : (Expr.add (.lit 1) (V bv)).evalB B σ = some (1 + b) := evalB_bin e1 eb (by simp; omega)
  have em : (Expr.mul (V "g_W") (V ev)).evalB B σ = some ((par Dt x).W * e) :=
    evalB_bin eW ee (by simp; omega)
  have es : (Expr.add (.add (.lit 1) (V bv)) (.mul (V "g_W") (V ev))).evalB B σ =
      some (1 + b + (par Dt x).W * e) := evalB_bin ea em (by simp; omega)
  have ev : (litE bv ev).evalB B σ = some (2 * (par Dt x).zv b e) := by
    unfold litE Par.zv
    exact evalB_bin e2 es (by simp; omega)
  have hr := RunStep.write B σ _ _ ev
  refine ⟨_, hr.mono (by simp [litE, Expr.size]), rfl, rfl⟩

/-- **Phase B.** -/
theorem phaseB_spec (hB : BB Dt x B) :
    Spec B (GC Dt x) phaseB
      (fun σ σ' => GC Dt x σ' ∧ σ'.out = σ.out ++ (List.range (par Dt x).W).flatMap (bWords Dt x))
      ((((10 + 8) * (par Dt x).C + 6 + 2 + 8) + 8) * (par Dt x).W + 6) := by
  have hs := hB.small
  refine loopC_out (by omega) (GC Dt x) (fun σ v h => h.setVar (by simp [gcVars]) v)
    (fun σ h => h.W) (bWords Dt x) fun b hb => ?_
  intro σ ⟨hg, hbv⟩
  have hC : σ.vars "g_C" = (par Dt x).C := hg.C
  have hr1 := RunStep.write B σ (V "g_C") _ (evalB_var (by rw [hC]; omega))
  set σ1 := { σ with out := σ.out ++ [σ.vars "g_C"] } with hσ1
  have hin := loopC_out (B := B) (x := "g_e") (m := "g_C") (body := .write (litE "g_b" "g_e"))
    (N := (par Dt x).C) (Kb := 10) (by omega) (fun τ => GC Dt x τ ∧ τ.vars "g_b" = b)
    (fun τ v h => ⟨h.1.setVar (by simp [gcVars]) v, by simp [Env.setVar, h.2]⟩)
    (fun τ h => h.1.C) (fun e => [2 * (par Dt x).zv b e]) fun e he => by
      intro τ ⟨⟨hg', hb'⟩, he'⟩
      obtain ⟨τ', hr, ho, heq⟩ := litWrite_spec hB hb he "g_b" "g_e" τ ⟨hb', he', hg'.W⟩
      refine ⟨τ', hr, ?_, ?_, ho⟩
      · rw [heq]; exact ⟨hg'.frame (S := []) (A := []) ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩
          (by simp) (by simp) (fun _ _ => rfl), hb'⟩
      · rw [heq]; exact he'
  obtain ⟨σ2, hr2, ⟨hg2, hb2⟩, ho2⟩ := hin σ1 ⟨hg.frame (S := []) (A := [])
    ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩ (by simp) (by simp) (fun _ _ => rfl), hbv⟩
  refine ⟨σ2, (hr1.seq hr2).mono (by simp [Expr.size]; omega), hg2, hb2, ?_⟩
  rw [ho2, hσ1]
  simp [bWords, hC, flatMap_single]

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PPhaseB
