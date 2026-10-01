import Lax496464Proofs.WHierarchy.HittingSet.WSHSProg
import Lax496464Proofs.WHierarchy.HittingSet.Common
import Lax496464Proofs.WHierarchy.HittingSet.Param

/-! # Weighted monotone satisfiability to Hitting Set: the running time, and the reduction

The program of `WSHSProg` computes the reduction (`wsProg_run`) in polynomial time (`polyTime`);
with the correctness of `WSHSMath` this gives the fpt-reduction from weighted monotone
satisfiability to `p-Hitting-Set` (`pWSat_monotone_le_hittingSet`). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.WSHSFinal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding (bitSize)
open Lax429075.CNF Lax496464.HittingSet Lax496464.WH_C2_HittingSet Lax496464.WH_C3_WeightedSat
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.SetsMath
open Lax496464Proofs.WHierarchy.HittingSet.EmitSets Lax496464Proofs.WHierarchy.HittingSet.WSHSMath
open Lax496464Proofs.WHierarchy.HittingSet.WSHSRead Lax496464Proofs.WHierarchy.HittingSet.WSHSProg
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.HittingSet.EmitNat (V)

/-! ## The word of a formula -/

theorem length_encode (α : Formula) : (encode α).length = 1 + α.length + T α := by
  induction α with
  | nil => simp [encode, T, litsL]
  | cons C α ih =>
      simp only [encode, List.length_cons, List.flatMap_cons, List.length_append,
        List.length_map, T, litsL] at ih ⊢
      omega

theorem code_mem (α : Formula) {C : Clause} (hC : C ∈ α) {l : Literal} (hl : l ∈ C) :
    litCode l ∈ encode α := by
  rw [encode_eq]
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨C, hC, List.mem_cons_of_mem _
    (List.mem_map_of_mem hl)⟩)

theorem index_lt_of_mem (α : Formula) {v : ℕ} (hv : v ∈ litsL α) :
    ∃ C ∈ α, ∃ l ∈ C, v = l.index := by
  simp only [litsL, List.mem_flatMap, List.mem_map] at hv
  obtain ⟨C, hC, l, hl, rfl⟩ := hv
  exact ⟨C, hC, l, hl, rfl⟩

theorem index_le_code (l : Literal) : l.index ≤ litCode l := by unfold litCode; split_ifs <;> omega

/-! ## The run -/

/-- The cost bound of the program. -/
def Kws (x : List ℕ) : ℕ := 1000 * (bitSize x + 1) ^ 3

theorem arith_ws (s T c : ℕ) (hT : T ≤ s) (hc : c ≤ s) :
    (20 * T + 24) * c + 20 + ((34 * T + 24) * T + 6) + (16 * T + 6) + 2 + (24 * T + 6) +
      (1 + 3 + (6 + 3 * (48 * s + 42) +
        (((48 * T + 48 * T + 178) * T + 48 * T + 68 + 4) * c + 6))) ≤ 1000 * (s + 1) ^ 3 := by
  have h1 : (20 * T + 24) * c ≤ (20 * s + 24) * s := Nat.mul_le_mul (by omega) hc
  have h2 : (34 * T + 24) * T ≤ (34 * s + 24) * s := Nat.mul_le_mul (by omega) hT
  have h3 : (48 * T + 48 * T + 178) * T ≤ (96 * s + 178) * s := Nat.mul_le_mul (by omega) hT
  have h4 : ((48 * T + 48 * T + 178) * T + 48 * T + 68 + 4) * c ≤
      ((96 * s + 178) * s + 48 * s + 72) * s := Nat.mul_le_mul (by omega) hc
  have h5 : (20 * s + 24) * s + (34 * s + 24) * s + ((96 * s + 178) * s + 48 * s + 72) * s +
      200 * s + 200 ≤ 1000 * (s + 1) ^ 3 := by
    ring_nf; nlinarith [Nat.zero_le (s ^ 3), Nat.zero_le (s ^ 2)]
  omega

theorem wsProg_run {x : List ℕ} (hx : x ∈ (pWSat {α | IsMonotone α}).Domain) {B : ℕ}
    (hB : 2 ^ (bitSize x + 3) ≤ B) :
    ∃ (ext : String → ℕ) (σ' : Env), Run B wsProg (initEnv ext (x.length :: x)) σ' (Kws x) ∧
      σ'.out = redWS x := by
  classical
  obtain ⟨α, hα, k, rfl⟩ := hx
  set x := encode α ++ [k] with hxdef
  have hs := length_le_bitSize x
  have hxs : ∀ v ∈ x, v < 2 ^ bitSize x := fun v hv => lt_two_pow_bitSize hv
  have hL2 : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
  have hB8 : 2 ^ (bitSize x + 3) = 8 * 2 ^ bitSize x := by ring
  have hlen : x.length = 2 + α.length + T α := by
    rw [hxdef, List.length_append, length_encode]; simp; omega
  have hkmem : k ∈ x := by rw [hxdef]; simp
  have hk2 := hxs k hkmem
  have hkS := size_le_bitSize hkmem
  have hcode : ∀ C ∈ α, ∀ l ∈ C, litCode l < B := fun C hC l hl => by
    have := hxs _ (by rw [hxdef]; exact List.mem_append_left _ (code_mem α hC hl)); omega
  have hfits : WSHSRead.Fits α k B := ⟨hcode, by omega, by omega⟩
  have hlB : ∀ v ∈ litsL α, v < B := fun v hv => by
    obtain ⟨C, hC, l, hl, rfl⟩ := index_lt_of_mem α hv
    exact lt_of_le_of_lt (index_le_code l) (hcode C hC l hl)
  have hFl : (Firsts.firsts (litsL α)).length = T α := by simp [Firsts.firsts, T]
  have hFlt : ∀ v ∈ Firsts.firsts (litsL α), v < T α := by
    intro v hv
    simp only [Firsts.firsts, List.mem_map, List.mem_range] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact List.idxOf_lt_length_of_mem (Compress.getD_mem hp)
  let ext : String → ℕ := fun a =>
    if a = "es_off" then α.length + 1 else if a = "hs_mem" then T α else
      if a = "fp_f" then T α else if a = "es_val" then T α else 0
  refine ⟨ext, ?_⟩
  -- reading
  obtain ⟨σ1, r1, ⟨hc1, hk1, ht1, hoff1, hmem1, -⟩, hv1, ha1, -, ho1⟩ :=
    (wsRead_core (B := B) α k x.length hfits).frame.run (σ := initEnv ext (x.length :: x))
      ⟨by simp [initEnv, hxdef], by simp [initEnv, ext], by simp [initEnv, ext]⟩
  have hw1 : wsRead.NoWrite := by
    simp [wsRead, clauseLoop, clauseBody, litLoop, litBody, Com.NoWrite]
  have ho1' : σ1.out = [] := by rw [ho1 hw1]; rfl
  have hfl1 : (σ1.arrs "fp_f").length = T α := by
    rw [ha1 _ (by simp [wsRead, clauseLoop, clauseBody, litLoop, litBody, Com.warrs])]
    simp [initEnv, ext]
  have hval1 : (σ1.arrs "es_val").length = T α := by
    rw [ha1 _ (by simp [wsRead, clauseLoop, clauseBody, litLoop, litBody, Com.warrs])]
    simp [initEnv, ext]
  -- first occurrences
  obtain ⟨σ2, r2, ⟨hF2, hp2⟩, hv2, ha2, -, ho2⟩ :=
    (Firsts.firstsLoop_spec (B := B) (litsL α) hlB (by have := hfits.T_lt; unfold T at this; omega)).frame.run
      (σ := σ1) ⟨by simp [Env.setVar, hmem1], by simp [Env.setVar, ht1, T],
        by simp [Env.setVar], by simp [Env.setVar, hfl1, T], by simp [Env.setVar]⟩
  have hff2 := Firsts.firsts_eq_of_FInv hF2 hp2
  have hwf : ∀ y, y ∉ ["fp_p", "fp_q", "fp_r"] → σ2.vars y = σ1.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    exact hv2 y (by simp [Firsts.firstsLoop, Firsts.firstBody, Firsts.scanLoop, Firsts.scanBody,
      Com.wvars, hy.1, hy.2.1, hy.2.2])
  have ha2' : ∀ b, b ≠ "fp_f" → σ2.arrs b = σ1.arrs b := fun b hb =>
    ha2 b (by simp [Firsts.firstsLoop, Firsts.firstBody, Firsts.scanLoop, Firsts.scanBody,
      Com.warrs, hb])
  have ho2' : σ2.out = [] := by
    rw [ho2 (by simp [Firsts.firstsLoop, Firsts.firstBody, Firsts.scanLoop, Firsts.scanBody,
      Com.NoWrite]), ho1']
  -- copy
  obtain ⟨σ3, r3, hval3, ha3, -, ho3, hv3⟩ :=
    (copyF_spec (B := B) (Firsts.firsts (litsL α)) (T α) hFl
      (fun v hv => by have := hFlt v hv; omega) (by omega)).run (σ := σ2)
      ⟨hff2, by rw [hwf _ (by decide), ht1], by rw [ha2' _ (by decide), hval1]⟩
  -- count
  have r4 := Run.assign (B := B) (σ := σ3) (x := "ws_d") (e := .lit 0) (v := 0)
    (evalB_lit (by omega))
  obtain ⟨σ5, r5, hd5, ha5, -, ho5, hv5⟩ :=
    (countD_spec (B := B) (Firsts.firsts (litsL α)) (T α) hFl
      (fun v hv => by have := hFlt v hv; omega) (by omega)).run (σ := σ3.setVar "ws_d" 0)
      ⟨by simp [Env.setVar, ha3 "fp_f" (by decide), hff2],
        by simp [Env.setVar]; rw [hv3 _ (by decide), hwf _ (by decide), ht1],
        by simp [Env.setVar]⟩
  replace hd5 : σ5.vars "ws_d" = (vars α).card := by
    rw [hd5, vars_eq]; exact fixCount_firsts (litsL α)
  have hDT : (vars α).card ≤ T α := by rw [vars_eq]; exact List.toFinset_card_le _
  have e5 : ∀ y, y ≠ "ws_i" → y ≠ "ws_d" → y ∉ ["fp_p", "fp_q", "fp_r"] →
      σ5.vars y = σ1.vars y := by
    intro y h1 h2 h3
    rw [hv5 y h1 h2]; simp only [Env.setVar, if_neg h2]; rw [hv3 y h1, hwf y h3]
  have hk5 : σ5.vars "ws_k" = k := by
    rw [e5 _ (by decide) (by decide) (by decide), hk1]
  have hc : (Cond.lt (V "ws_d") (V "ws_k")).evalB B σ5 = some (decide ((vars α).card < k)) := by
    rw [evalB_condLt (evalB_var (by rw [hd5]; omega)) (evalB_var (by rw [hk5]; omega)), hd5, hk5]
  have ho5' : σ5.out = [] := by rw [ho5, show (σ3.setVar "ws_d" 0).out = σ3.out from rfl, ho3, ho2']
  have hcost : ∀ K, K ≤ 1 + 3 + (6 + 3 * (48 * bitSize x + 42) +
      ((Kset (T α) (T α) + 4) * α.length + 6)) →
      Kread α + ((34 * (litsL α).length + 24) * (litsL α).length + 6 + (16 * T α + 6 +
        (1 + (Expr.lit 0).size + (24 * T α + 6 + K)))) ≤ Kws x := by
    intro K hK
    have := arith_ws (bitSize x) (T α) α.length (by omega) (by omega)
    have hl : (litsL α).length = T α := rfl
    rw [hl]; unfold Kread Kset at *; unfold Kws; simp only [size_lit]; omega
  rw [redWS_word]
  by_cases hkD : k ≤ (vars α).card
  · rw [if_pos hkD]
    have hc' : (Cond.lt (V "ws_d") (V "ws_k")).evalB B σ5 = some false := by
      rw [hc]; simp; omega
    -- the setup
    have hT5 : σ5.vars "hs_t" = T α := by rw [e5 _ (by decide) (by decide) (by decide), ht1]
    have hc5 : σ5.vars "ws_c" = α.length := by rw [e5 _ (by decide) (by decide) (by decide), hc1]
    have r6 : Run B wsSetup σ5 (((σ5.setVar "es_U" (T α)).setVar "es_m" α.length).setVar
        "es_self" 0) 6 := by
      have a1 := Run.assign (B := B) (σ := σ5) (x := "es_U") (e := V "hs_t") (v := T α)
        (by rw [← hT5]; exact evalB_var (by rw [hT5]; omega))
      have a2 := Run.assign (B := B) (σ := σ5.setVar "es_U" (T α)) (x := "es_m") (e := V "ws_c")
        (v := α.length) (by
          have : (σ5.setVar "es_U" (T α)).vars "ws_c" = α.length := by simp [Env.setVar, hc5]
          rw [← this]; exact evalB_var (by rw [this]; omega))
      have a3 := Run.assign (B := B) (σ := (σ5.setVar "es_U" (T α)).setVar "es_m" α.length)
        (x := "es_self") (e := .lit 0) (v := 0) (evalB_lit (by omega))
      exact (a1.seq (a2.seq a3)).mono (by simp)
    set σ6 := ((σ5.setVar "es_U" (T α)).setVar "es_m" α.length).setVar "es_self" 0 with hσ6
    -- the header
    obtain ⟨σ7, r7, ho7, ha7, -, hv7⟩ : ∃ σ7, Run B wsHeader σ6 σ7 (3 * (48 * bitSize x + 42)) ∧
        σ7.out = σ6.out ++ (bitsNat (T α) ++ bitsNat α.length ++ bitsNat k) ∧
        σ7.arrs = σ6.arrs ∧ σ7.inp = σ6.inp ∧
        ∀ y, y ≠ "en_v" → y ≠ "en_u" → y ≠ "en_s" → y ≠ "en_i" → σ7.vars y = σ6.vars y := by
      have hT6 : σ6.vars "hs_t" = T α := by simp [hσ6, Env.setVar, hT5]
      have hc6 : σ6.vars "ws_c" = α.length := by simp [hσ6, Env.setVar, hc5]
      have hk6 : σ6.vars "ws_k" = k := by simp [hσ6, Env.setVar, hk5]
      obtain ⟨s1, q1, o1, a1, i1, v1⟩ := (DSHSProg.emitVar (B := B) "hs_t" (T α) (bitSize x)
        (by omega) ((Words.size_le_self _).trans (by omega))).run hT6
      obtain ⟨s2, q2, o2, a2, i2, v2⟩ := (DSHSProg.emitVar (B := B) "ws_c" α.length (bitSize x)
        (by omega) ((Words.size_le_self _).trans (by omega))).run (σ := s1)
        (by rw [v1 _ (by decide) (by decide) (by decide) (by decide), hc6])
      obtain ⟨s3, q3, o3, a3, i3, v3⟩ := (DSHSProg.emitVar (B := B) "ws_k" k (bitSize x)
        (by omega) hkS).run (σ := s2)
        (by rw [v2 _ (by decide) (by decide) (by decide) (by decide),
          v1 _ (by decide) (by decide) (by decide) (by decide), hk6])
      refine ⟨s3, (q1.seq (q2.seq q3)).mono (by omega), by rw [o3, o2, o1]; simp,
        by rw [a3, a2, a1], by rw [i3, i2, i1], fun y h1 h2 h3 h4 => ?_⟩
      rw [v3 y h1 h2 h3 h4, v2 y h1 h2 h3 h4, v1 y h1 h2 h3 h4]
    -- the sets
    have hb : Bounds (Firsts.firsts (litsL α)) (offL α) (T α) α.length (T α) B := by
      refine ⟨by simp [offL], fun j hj => ?_, fun j hj => ?_, by rw [hFl],
        fun v hv => by have := hFlt v hv; omega, by omega⟩
      · rw [offL_getD α hj]; exact cOff_le_T α hj
      · rw [offL_getD α (by omega), offL_getD α (by omega)]; exact cOff_mono α (by omega)
    have e7 : ∀ y, y ≠ "en_v" → y ≠ "en_u" → y ≠ "en_s" → y ≠ "en_i" → y ≠ "es_self" →
        y ≠ "es_m" → y ≠ "es_U" → σ7.vars y = σ5.vars y := by
      intro y h1 h2 h3 h4 h5 h6 h7
      rw [hv7 y h1 h2 h3 h4]; simp [hσ6, Env.setVar, h5, h6, h7]
    have ha7' : σ7.arrs = σ5.arrs := by rw [ha7]; rfl
    obtain ⟨σ8, r8, ho8, -, -, -⟩ :=
      (setsLoop_spec (B := B) (Firsts.firsts (litsL α)) (offL α) false (T α) α.length (T α)
        hb).run (σ := σ7)
        ⟨by rw [ha7', ha5]; simp only [Env.setVar]; exact hval3,
          by rw [ha7', ha5]; simp only [Env.setVar]; rw [ha3 _ (by decide), ha2' _ (by decide), hoff1],
          by rw [hv7 _ (by decide) (by decide) (by decide) (by decide)]; simp [hσ6, Env.setVar],
          by rw [hv7 _ (by decide) (by decide) (by decide) (by decide)]; simp [hσ6, Env.setVar],
          by rw [hv7 _ (by decide) (by decide) (by decide) (by decide)]; simp [hσ6, Env.setVar]⟩
    refine ⟨σ8, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (Run.ite_false hc'
      (r6.seq (r7.seq r8)))))))).mono ?_, ?_⟩
    · refine hcost _ ?_
      simp only [size_condLt, size_var]; omega
    rw [ho8, ho7, show σ6.out = σ5.out from rfl, ho5', hsOfF, word_ofPred]
    simp [T]
  · rw [if_neg hkD]
    have hc' : (Cond.lt (V "ws_d") (V "ws_k")).evalB B σ5 = some true := by
      rw [hc]; simp; omega
    obtain ⟨σ6, r6, ho6⟩ := (writeNoHS_spec (B := B) (by omega)).run (σ := σ5) trivial
    refine ⟨σ6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (Run.ite_true hc' r6)))))).mono ?_, ?_⟩
    · refine hcost _ ?_
      simp only [size_condLt, size_var]; omega
    rw [ho6, ho5', word_noInst]; rfl

/-! ## Compilation and bounds -/

/-- The scalars of the program. -/
def wsVars : List String :=
  ["ws_len", "ws_c", "ws_j", "ws_l", "ws_q", "ws_v", "ws_k", "hs_t", "fp_p", "fp_q", "fp_r",
    "ws_i", "ws_d", "es_U", "es_m", "es_self", "es_j", "es_lo", "es_hi", "es_cnt", "es_a", "es_c",
    "es_p", "en_v", "en_u", "en_s", "en_i"]

def layout : Layout := ⟨wsVars, ["es_off", "hs_mem", "fp_f", "es_val"], 8⟩

set_option maxHeartbeats 4000000 in
theorem wsProg_ok : Com.Ok layout wsProg := by
  simp [layout, wsVars, wsProg, wsRead, clauseLoop, clauseBody, litLoop, litBody,
    Firsts.firstsLoop, Firsts.firstBody, Firsts.scanLoop, Firsts.scanBody, copyF, copyBody, countD,
    WSHSProg.countBody, writeNoHS, wsEmit, wsSetup, wsHeader, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    setsLoop, setBody, countLoop, EmitSets.countBody, writeLoop, writeBody, emitIf, testCom,
    EmitSets.scanLoop, EmitSets.scanBody, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

/-- The value bound, on the tape `y = x.length :: x`. -/
def Bws (y : List ℕ) : ℕ := 2 ^ (bitSize y + 3)

/-- The cost bound, on the tape. -/
def Kt (y : List ℕ) : ℕ := Kws y.tail

theorem solves : Solves layout wsProg (Tapes (pWSat {α | IsMonotone α}).Domain)
    (fun y => redWS y.tail) Bws Kt := by
  refine ⟨wsProg_ok, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩ v hv
    have := lt_two_pow_bitSize hv
    have : 2 ^ bitSize (x.length :: x) ≤ Bws (x.length :: x) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rintro y ⟨x, hx, rfl⟩
    have hb : 2 ^ (bitSize x + 3) ≤ Bws (x.length :: x) := by
      unfold Bws; rw [bitSize_cons]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨ext, σ', r, hout⟩ := wsProg_run hx hb
    exact ⟨ext, σ', r, by rw [hout]; rfl⟩

/-- The constant of the polynomial bound. -/
def c₄ : ℕ := 20000

theorem polyTime : PolyTimeOn (pWSat {α | IsMonotone α}).Domain redWS := by
  refine polyTimeOn_of_solves (c₀ := c₄) (d := 3) solves ?_ ?_ ?_
  · intro x hx
    have hs := length_le_bitSize x
    have hsz : x.length.size ≤ bitSize x := (Words.size_le_self _).trans hs
    have hB : Bws (x.length :: x) = 2 ^ (x.length.size + bitSize x + 4) := by
      unfold Bws; rw [bitSize_cons]; ring_nf
    rw [hB]
    generalize x.length.size = a at hsz ⊢
    generalize bitSize x = s at hs hsz ⊢
    have h16 : 16 ≤ 2 ^ (a + s + 4) := by
      calc 16 = 2 ^ 4 := rfl
        _ ≤ 2 ^ (a + s + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, ?_⟩
    have hspan : layout.span (2 ^ (a + s + 4)) ≤ 2 ^ (a + s + 7) := by
      simp only [Layout.span, layout, wsVars, List.length_cons, List.length_nil]
      have : 2 ^ (a + s + 7) = 8 * 2 ^ (a + s + 4) := by ring
      omega
    have hle : 2 ^ (a + s + 7) ≤ 2 ^ (c₄ * (s + 1) ^ 3) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have : s + 1 ≤ (s + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      unfold c₄; omega
    have h47 : 2 ^ (a + s + 4) ≤ 2 ^ (a + s + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact max_le (h47.trans hle) (hspan.trans hle)
  · intro x _
    simp only [Kt, Kws, List.tail_cons, Layout.const]
    have h3 : 1 ≤ (bitSize x + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    unfold c₄; omega
  · rintro x ⟨α, -, k, rfl⟩ v hv
    classical
    rw [redWS_word] at hv
    have : v ≤ 1 := by
      split_ifs at hv
      · exact Common.word_le_one hv
      · exact Common.word_le_one hv
    have : 2 ≤ 2 ^ (c₄ * (bitSize (encode α ++ [k]) + 1) ^ 3) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by
          have : 1 ≤ (bitSize (encode α ++ [k]) + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
          unfold c₄; omega)
    omega

/--
---
conclusion: Lax496464.WH_E2_HittingSetW2Complete.pWSat_monotone_le_hittingSet
---
**Weighted monotone CNF satisfiability fpt-reduces to `p-Hitting-Set`** (Flum–Grohe, proof of
Theorem 7.14): the clauses, read as sets of variables, are the sets. The variables are renamed by the
position of their first occurrence among the literals, so the universe is the set of literal
positions; the weight stays `k`. Since the weight of the formula is exact and counts only its own
variables, the reduction writes a fixed no-instance when `k` exceeds the number of variables, and
otherwise a hitting set of size at most `k` pads to one of size `k` inside the variables. An empty
clause becomes an empty set, and the empty formula is `0`-satisfiable only, both as in Hitting Set.
The parameter is at most `k + 1`, and an IMP+ program computes the reduction within
`20000 (|x| + 1)^3` steps.
-/
theorem pWSat_monotone_le_hittingSet : pWSat {α | IsMonotone α} ≤ᶠᵖᵗ HittingSet :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime isReduction paramBounded polyTime

example : type_of% @Lax496464.WH_E2_HittingSetW2Complete.pWSat_monotone_le_hittingSet :=
  pWSat_monotone_le_hittingSet

end Lax496464Proofs.WHierarchy.HittingSet.WSHSFinal
