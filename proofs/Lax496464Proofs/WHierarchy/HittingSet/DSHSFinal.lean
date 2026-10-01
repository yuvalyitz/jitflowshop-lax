import Lax496464Proofs.WHierarchy.HittingSet.DSHSProg
import Lax496464Proofs.WHierarchy.HittingSet.Common
import Lax496464Proofs.WHierarchy.HittingSet.Param
import Lax496464.WH_E3_DominatingSet

/-! # Dominating Set to Hitting Set: the running time, and the reduction

The program `dhProg` computes the closed-neighbourhood map (`dhProg_run`) in polynomial time
(`polyTime`); with the correctness of `DSHSMath` this gives `p-Dominating-Set ≤fpt p-Hitting-Set`
(`dominatingSet_le_hittingSet`). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.DSHSFinal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer Lax759944.BinaryWordEncoding
open Lax496464.HittingSet Lax496464.WH_C2_HittingSet Lax496464.WH_C1_GraphProblems
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax271696.VertexCover Lax271696.GraphEncoding
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.SetsMath
open Lax496464Proofs.WHierarchy.HittingSet.EmitSets Lax496464Proofs.WHierarchy.HittingSet.DSHSMath
open Lax496464Proofs.WHierarchy.HittingSet.DSHSProg
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.Machine.ReadTape (readTape readTape_spec readVars)

/-- The array lengths the program is started with. -/
def extDH (x : List ℕ) (a : String) : ℕ :=
  if a = "a" then x.length else if a = "es_off" then nX x + 1 else
    if a = "es_val" then 2 * mX x else 0

/-- The cost bound of the program. -/
def Kdh (x : List ℕ) : ℕ :=
  (16 * x.length + 7) + 40 + (16 * (nX x + 1) + 6) + (20 * (mX x + mX x) + 6) +
    3 * (48 * bitSize x + 42) + ((Kset (nX x) (2 * mX x) + 4) * nX x + 6)

/-- The facts about a graph word the run needs. -/
theorem word_facts {x g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (hx : x = g ++ [k]) (hg : EncodesGraph g n G) :
    x.length = 4 + nX x + 2 * mX x ∧ x.getD (x.length - 1) 0 = kX x ∧ nX x ∈ x ∧ kX x ∈ x := by
  have hl := hg.length_eq
  have hn := nX_eq hx hg
  have hm := mX_eq hx hg
  have hk := kX_eq hx
  refine ⟨by rw [hn, hm, hx]; simp; omega, by subst hx; simp [kX], ?_, ?_⟩
  · unfold nX
    rw [List.getD_eq_getElem _ _ (by rw [hx]; simp)]
    exact List.getElem_mem _
  · rw [hk, hx]; simp

theorem dhProg_run {x : List ℕ} (hx : x ∈ DominatingSet.Domain) {B : ℕ}
    (hB : 2 ^ (bitSize x + 3) ≤ B) :
    ∃ σ', Run B dhProg (initEnv (extDH x) (x.length :: x)) σ' (Kdh x) ∧ σ'.out = redDH x := by
  obtain ⟨n, G, k, g, hx, hg⟩ := hx
  obtain ⟨hlen, hlast, hnmem, hkmem⟩ := word_facts hx hg
  have hn := nX_eq hx hg
  have hm := mX_eq hx hg
  -- the bounds
  have hs := length_le_bitSize x
  have hxs : ∀ v ∈ x, v < 2 ^ bitSize x := fun v hv => lt_two_pow_bitSize hv
  have hL2 : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
  have hB8 : 2 ^ (bitSize x + 3) = 8 * 2 ^ bitSize x := by ring
  have hxB : ∀ v ∈ x, v < B := fun v hv => by have := hxs v hv; omega
  have hn2 := hxs _ hnmem
  have hk2 := hxs _ hkmem
  have hnS := size_le_bitSize hnmem
  have hkS := size_le_bitSize hkmem
  -- reading
  obtain ⟨σ1, r1, ha1, hr1, -, ho1, hv1, harr1⟩ :=
    (readTape_spec x (initEnv (extDH x) (x.length :: x)) hxB (by omega) rfl
      (by simp [initEnv, extDH])).run (σ := initEnv (extDH x) (x.length :: x)) rfl
  -- the setup
  have h0 : x.getD 0 0 = nX x := rfl
  have h1 : x.getD 1 0 = mX x := rfl
  obtain ⟨σ2, r2, hn2', hM2, hk2', hU2, hm2, hs2, hn12, hT2, ha2, -, ho2⟩ :=
    (dhSetup_spec (B := B) x (by omega) hxB (by omega) (by rw [h0, h1]; omega)).run (σ := σ1)
      ⟨ha1, hr1⟩
  rw [h0] at hn2' hU2 hm2 hn12
  rw [h1] at hM2 hT2
  rw [hlast] at hk2'
  -- the offsets
  obtain ⟨σ3, r3, hoff3, ha3, -, ho3, hv3⟩ :=
    (offCopy_spec (B := B) x (nX x + 1) (by omega) hxB (by omega)).run (σ := σ2)
      ⟨by rw [ha2, ha1], hn12, by rw [ha2, harr1 _ (by decide)]; simp [initEnv, extDH]⟩
  -- the targets
  obtain ⟨σ4, r4, hval4, ha4, -, ho4, hv4⟩ :=
    (valCopy_spec (B := B) x (nX x) (mX x + mX x) (by omega) hxB (by omega)).run (σ := σ3)
      ⟨by rw [ha3 _ (by decide), ha2, ha1], by rw [hv3 _ (by decide), hT2],
        by rw [hv3 _ (by decide), hn2'],
        by rw [ha3 _ (by decide), ha2, harr1 _ (by decide)]; simp [initEnv, extDH]; omega⟩
  -- the header
  obtain ⟨σ5, r5, ho5, ha5, -, hv5⟩ :=
    (header_spec (B := B) (nX x) (kX x) (bitSize x) (by omega) (by omega) hnS hkS).run (σ := σ4)
      ⟨by rw [hv4 _ (by decide), hv3 _ (by decide), hn2'],
        by rw [hv4 _ (by decide), hv3 _ (by decide), hk2']⟩
  -- the sets
  have hoffX : offX x = (List.range (nX x + 1)).map (fun p => x.getD (2 + p) 0) := rfl
  have hvalX : valX x = (List.range (mX x + mX x)).map (fun p => x.getD (3 + nX x + p) 0) := by
    rw [valX, two_mul]
  have hb : Bounds (valX x) (offX x) (nX x) (nX x) (2 * mX x) B := by
    refine ⟨by simp [offX], fun j hj => ?_, fun j hj => ?_, by simp [valX], fun v hv => ?_, ?_⟩
    · rw [offX_getD hx hg (by omega), hm]; exact offset_le_last hg (by omega)
    · rw [offX_getD hx hg (by omega), offX_getD hx hg (by omega)]
      exact hg.offset_mono j (by omega)
    · simp only [valX, List.mem_map, List.mem_range] at hv
      obtain ⟨q, hq, rfl⟩ := hv
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hxB _ (List.getElem_mem _)
    · omega
  have hvar5 : ∀ y, y ≠ "en_v" → y ≠ "en_u" → y ≠ "en_s" → y ≠ "en_i" → y ≠ "dh_i" →
      σ5.vars y = σ2.vars y := by
    intro y h1 h2 h3 h4 h5; rw [hv5 y h1 h2 h3 h4, hv4 y h5, hv3 y h5]
  obtain ⟨σ6, r6, ho6, -, -, -⟩ :=
    (setsLoop_spec (B := B) (valX x) (offX x) true (nX x) (nX x) (2 * mX x) hb).run (σ := σ5)
      ⟨by rw [ha5, hval4, hvalX],
        by rw [ha5, ha4 _ (by decide), hoff3, hoffX],
        by rw [hvar5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hU2],
        by rw [hvar5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hm2],
        by rw [hvar5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hs2]; rfl⟩
  refine ⟨σ6, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq r6))))).mono ?_, ?_⟩
  · unfold Kdh; omega
  · rw [ho6, ho5, ho4, ho3, ho2, ho1, redDH, hsOf, word_ofPred]
    simp [initEnv]

/-! ## Compilation and bounds -/

/-- The scalars of the program. -/
def dhVars : List String :=
  ["rt_n", "rt_i", "rt_v", "dh_n", "dh_M", "dh_k", "dh_n1", "dh_T", "dh_i", "es_U", "es_m",
    "es_self", "es_j", "es_lo", "es_hi", "es_cnt", "es_a", "es_c", "es_p", "en_v", "en_u", "en_s",
    "en_i"]

def layout : Layout := ⟨dhVars, ["a", "es_off", "es_val"], 8⟩

set_option maxHeartbeats 4000000 in
theorem dhProg_ok : Com.Ok layout dhProg := by
  simp [layout, dhVars, dhProg, readTape, Machine.ReadTape.readLoop, Machine.ReadTape.readBody,
    dhSetup, offCopy, offBody, valCopy, valBody, header, EmitNat.emitNat, EmitNat.sizeLoop,
    EmitNat.sizeBody, EmitNat.onesLoop, EmitNat.onesBody, EmitNat.digLoop, EmitNat.digBody,
    setsLoop, setBody, countLoop, countBody, writeLoop, writeBody, emitIf, testCom, scanLoop,
    scanBody, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

theorem arith_dh (s n M : ℕ) (hn : n ≤ s) (hM : 2 * M ≤ s) :
    (16 * s + 7) + 40 + (16 * (n + 1) + 6) + (20 * (M + M) + 6) + 3 * (48 * s + 42) +
      (((48 * (2 * M) + 48 * n + 178) * n + 48 * n + 68 + 4) * n + 6) ≤ 1000 * (s + 1) ^ 3 := by
  have h1 : (48 * (2 * M) + 48 * n + 178) * n ≤ (96 * s + 178) * s :=
    Nat.mul_le_mul (by omega) hn
  have h2 : ((48 * (2 * M) + 48 * n + 178) * n + 48 * n + 68 + 4) * n ≤
      ((96 * s + 178) * s + 48 * s + 72) * s := Nat.mul_le_mul (by omega) hn
  have h3 : ((96 * s + 178) * s + 48 * s + 72) * s + 16 * s + 144 * s + 16 * s + 20 * s + 250 ≤
      1000 * (s + 1) ^ 3 := by
    ring_nf; nlinarith [Nat.zero_le (s ^ 3), Nat.zero_le (s ^ 2)]
  omega

theorem Kdh_le {x : List ℕ} (hx : x ∈ DominatingSet.Domain) :
    Kdh x ≤ 1000 * (bitSize x + 1) ^ 3 := by
  obtain ⟨n, G, k, g, hx', hg⟩ := hx
  obtain ⟨hlen, -, -, -⟩ := word_facts hx' hg
  have hs := length_le_bitSize x
  have := arith_dh (bitSize x) (nX x) (mX x) (by omega) (by omega)
  unfold Kdh Kset
  omega

/-- The value bound, on the tape `y = x.length :: x`. -/
def Bdh (y : List ℕ) : ℕ := 2 ^ (bitSize y + 3)

/-- The cost bound, on the tape. -/
def Kt (y : List ℕ) : ℕ := Kdh y.tail

theorem solves : Solves layout dhProg (Tapes DominatingSet.Domain) (fun y => redDH y.tail) Bdh Kt := by
  refine ⟨dhProg_ok, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩ v hv
    have := lt_two_pow_bitSize hv
    have : 2 ^ bitSize (x.length :: x) ≤ Bdh (x.length :: x) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨extDH x, ?_⟩
    have hb : 2 ^ (bitSize x + 3) ≤ Bdh (x.length :: x) := by
      unfold Bdh; rw [bitSize_cons]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨σ', r, hout⟩ := dhProg_run hx hb
    exact ⟨σ', r, by rw [hout]; rfl⟩

/-- The constant of the polynomial bound. -/
def c₃ : ℕ := 20000

theorem polyTime : PolyTimeOn DominatingSet.Domain redDH := by
  refine polyTimeOn_of_solves (c₀ := c₃) (d := 3) solves ?_ ?_ ?_
  · intro x hx
    have hs := length_le_bitSize x
    have hsz : x.length.size ≤ bitSize x := (Words.size_le_self _).trans hs
    have hB : Bdh (x.length :: x) = 2 ^ (x.length.size + bitSize x + 4) := by
      unfold Bdh; rw [bitSize_cons]; ring_nf
    rw [hB]
    generalize x.length.size = a at hsz ⊢
    generalize bitSize x = s at hs hsz ⊢
    have h16 : 16 ≤ 2 ^ (a + s + 4) := by
      calc 16 = 2 ^ 4 := rfl
        _ ≤ 2 ^ (a + s + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, ?_⟩
    have hspan : layout.span (2 ^ (a + s + 4)) ≤ 2 ^ (a + s + 7) := by
      simp only [Layout.span, layout, dhVars, List.length_cons, List.length_nil]
      have : 2 ^ (a + s + 7) = 8 * 2 ^ (a + s + 4) := by ring
      omega
    have hle : 2 ^ (a + s + 7) ≤ 2 ^ (c₃ * (s + 1) ^ 3) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      have : s + 1 ≤ (s + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
      unfold c₃; omega
    have h46 : 2 ^ (a + s + 4) ≤ 2 ^ (a + s + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact max_le (h46.trans hle) (hspan.trans hle)
  · intro x hx
    have := Kdh_le hx
    simp only [Kt, List.tail_cons, Layout.const]
    have h3 : 1 ≤ (bitSize x + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    unfold c₃; omega
  · rintro x ⟨n, G, k, g, hx, hg⟩ v hv
    rw [redDH] at hv
    have := Common.word_le_one hv
    have : 2 ≤ 2 ^ (c₃ * (bitSize x + 1) ^ 3) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by
          have : 1 ≤ (bitSize x + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
          unfold c₃; omega)
    omega

/--
---
conclusion: Lax496464.WH_E3_DominatingSet.dominatingSet_le_hittingSet
---
**`p-Dominating-Set ≤fpt p-Hitting-Set`**, by closed neighbourhoods. The universe is the vertex set,
set `v` is `N[v] = {v} ∪ N(v)`, and the solution size is unchanged: a set of `k` vertices dominates
the graph exactly when it meets every closed neighbourhood. Each set is written sorted and without
repetitions by testing the candidates `0, …, n-1` in order against the adjacency block of `v`, so
the order and repetitions of the block do not matter. The parameter is unchanged, and an IMP+
program computes the reduction within `20000 (|x| + 1)^3` steps.
-/
theorem dominatingSet_le_hittingSet : DominatingSet ≤ᶠᵖᵗ HittingSet :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime isReduction paramBounded polyTime

example : type_of% @Lax496464.WH_E3_DominatingSet.dominatingSet_le_hittingSet :=
  dominatingSet_le_hittingSet

end Lax496464Proofs.WHierarchy.HittingSet.DSHSFinal
