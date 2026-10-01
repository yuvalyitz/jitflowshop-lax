import Lax496464Proofs.WHierarchy.HittingSet.WDProg
import Lax496464Proofs.WHierarchy.HittingSet.WDMath
import Lax496464Proofs.WHierarchy.HittingSet.Param

/-! # Hitting Set to weighted definability: the running time, and the reduction

The program writes the word `wdOut` of the structure of the compressed instance (`wdOut_eq`,
`wdProg_run`) in polynomial time (`polyTime`); with the correctness of `WDMath` this gives
`p-Hitting-Set ≤fpt p-WD_hs` (`hittingSet_le_pWD`). -/

namespace Lax496464Proofs.WHierarchy.HittingSet.WDFinal

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer Lax759944.BinaryWordEncoding
open Lax496464.HittingSet Lax496464.WH_C2_HittingSet Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions
open Lax496464.WH_B3_LogicProblems Lax496464.WH_E1_HittingSetInW2
open Lax496464Proofs.WHierarchy.HittingSet.Words Lax496464Proofs.WHierarchy.HittingSet.Form
open Lax496464Proofs.WHierarchy.HittingSet.Parse Lax496464Proofs.WHierarchy.HittingSet.Common
open Lax496464Proofs.WHierarchy.HittingSet.Compress Lax496464Proofs.WHierarchy.HittingSet.Firsts
open Lax496464Proofs.WHierarchy.HittingSet.WDProg Lax496464Proofs.WHierarchy.HittingSet.WDMath
open Lax496464Proofs.WHierarchy.HittingSet.ReadNat (V)
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.Logic.StructureCode

/-! ## The arrays the reader leaves -/

theorem list_eq_of_getD {l l' : List ℕ} (hl : l.length = l'.length)
    (h : ∀ p < l.length, l.getD p 0 = l'.getD p 0) : l = l' := by
  refine List.ext_getElem hl fun i h1 h2 => ?_
  have := h i h1
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

theorem mem_eq {P : Instance} {k : ℕ} {σ : Env} (h : Parsed P k σ) :
    σ.arrs "hs_mem" = memL P := by
  obtain ⟨-, -, -, -, -, hml, hmem, -, -⟩ := h
  exact list_eq_of_getD (by rw [hml, length_memL]) fun p hp => hmem p (by rwa [hml] at hp)

theorem own_eq {P : Instance} {k : ℕ} {σ : Env} (h : Parsed P k σ) :
    σ.arrs "hs_own" = ownL P := by
  obtain ⟨-, -, -, -, -, -, -, hwl, hown⟩ := h
  exact list_eq_of_getD (by rw [hwl, length_ownL]) fun p hp => hown p (by rwa [hwl] at hp)

/-! ## The word written -/

theorem length_firsts (l : List ℕ) : (firsts l).length = l.length := by simp [firsts]

theorem firsts_getD (P : Instance) {p : ℕ} (hp : p < total P) :
    (firsts (memL P)).getD p 0 = fst P p := by
  rw [List.getD_eq_getElem _ _ (by rw [length_firsts, length_memL]; exact hp)]
  simp [firsts, fst]

theorem firsts_lt (P : Instance) {v : ℕ} (hv : v ∈ firsts (memL P)) : v < total P := by
  simp only [firsts, List.mem_map, List.mem_range] at hv
  obtain ⟨p, hp, rfl⟩ := hv
  rw [length_memL] at hp
  exact fst_lt hp

theorem ownL_mem_lt (P : Instance) {v : ℕ} (hv : v ∈ ownL P) : v < P.m := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hv
  rw [← List.getD_eq_getElem _ 0 hp]
  exact ownL_lt P (by rwa [length_ownL] at hp)

theorem flatten_map_singleton (l : List ℕ) : (l.map fun i => [i]).flatten = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem wdOut_eq (P : Instance) (k : ℕ) :
    wdOut P k = outList (firsts (memL P)) (ownL P) (NN P k) P.m (total P) (kk P k) := by
  have hinc : ((List.range (total P)).map
      (fun p => [fst P p, NN P k + (ownL P).getD p 0])).flatten =
      incList (firsts (memL P)) (ownL P) (NN P k) (total P) := by
    rw [incList, List.flatMap_def]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    rw [firsts_getD P (List.mem_range.mp hp)]
  simp only [wdOut, wordOf, tuplesWD, outList, blockOf, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.length_map, List.length_range,
    flatten_map_singleton, hinc]
  have : ((List.range P.m).map fun j => [NN P k + j]).flatten = (List.range P.m).map (NN P k + ·) := by
    rw [← flatten_map_singleton ((List.range P.m).map (NN P k + ·)), List.map_map]; rfl
  rw [this]
  simp

/-! ## The run -/

/-- The array lengths the program is started with. -/
def extWD (P : Instance) (a : String) : ℕ := if a = "fp_f" then total P else Param.extOf P a

theorem fresh_initWD (P : Instance) (y : List ℕ) : Fresh P (initEnv (extWD P) y) := by
  refine ⟨by simp [initEnv, extWD, Param.extOf], ?_, by simp [initEnv, extWD, Param.extOf],
    by simp [initEnv, extWD, Param.extOf]⟩
  simp [initEnv, extWD, Param.extOf, List.getD_eq_getElem?_getD]

/-- The cost bound of the program. -/
def Kwd (P : Instance) (k : ℕ) : ℕ :=
  Kread P k + 3 + (20 + ((34 * total P + 24) * total P + 6)) +
    (14 * NN P k + 16 * P.m + 20 * total P + 60) + 20

theorem wdProg_run {B : ℕ} (P : Instance) (k L : ℕ) (hB : 2 ^ ((word P k).length + 3) ≤ B) :
    ∃ σ', Run B wdProg (initEnv (extWD P) (L :: word P k)) σ' (Kwd P k) ∧
      σ'.out = redWD (word P k) := by
  obtain ⟨hmT, hn, hm, hk, -⟩ := dims P k
  have hL2 : (word P k).length < 2 ^ (word P k).length := Nat.lt_two_pow_self
  have hB8 : 2 ^ ((word P k).length + 3) = 8 * 2 ^ (word P k).length := by ring
  have hfits : Fits P k B := fits_of_le P k hB
  obtain ⟨σ1, r1, hP1, hout1, harr1, -⟩ :=
    (readHS_spec (B := B) P k L hfits).run (σ := initEnv (extWD P) (L :: word P k))
      ⟨rfl, fresh_initWD P _⟩
  have hPar := hP1
  obtain ⟨⟨hn1, hm1, hk1⟩, ht1, -, -⟩ := hP1
  have hmem1 := mem_eq hPar
  have hown1 := own_eq hPar
  have hf1 : (σ1.arrs "fp_f").length = total P := by
    rw [harr1 _ (by decide) (by decide) (by decide)]; simp [initEnv, extWD]
  rw [redWD_word]
  by_cases hkn : k ≤ P.n
  · rw [if_pos hkn]
    have hc : (Cond.lt (V "hs_n") (V "hs_k")).evalB B σ1 = some false := by
      rw [evalB_condLt (evalB_var (by rw [hn1]; omega)) (evalB_var (by rw [hk1]; omega)), hn1, hk1]
      simp; omega
    have hlB : ∀ v ∈ memL P, v < B := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hv
      rw [← List.getD_eq_getElem _ 0 hp]
      have := memL_lt P (by rwa [length_memL] at hp); omega
    obtain ⟨σ2, r2, hkk, hNN, hF, harr2, -, hout2, hvar2⟩ :=
      (prep_spec (B := B) (memL P) k P.m hlB (by rw [length_memL]; omega)).run (σ := σ1)
        ⟨hk1, hm1, by rw [ht1, length_memL], hmem1, by rw [hf1, length_memL]⟩
    obtain ⟨σ3, r3, hout3⟩ :=
      (outWD_spec (B := B) (firsts (memL P)) (ownL P) (NN P k) P.m (total P) (kk P k)
        (by rw [length_firsts, length_memL]) (length_ownL P)
        (fun v hv => by have := firsts_lt P hv; omega)
        (fun v hv => by have := ownL_mem_lt P hv; unfold NN kk; omega)
        (by unfold NN kk; omega)).run (σ := σ2)
        ⟨by rw [hNN, length_memL]; rfl, by rw [hvar2 _ (by decide), hm1],
          by rw [hvar2 _ (by decide), ht1], hF, by rw [harr2 _ (by decide), hown1],
          by rw [hkk]; rfl⟩
    refine ⟨σ3, (r1.seq (Run.ite_false hc (r2.seq r3))).mono ?_, ?_⟩
    · have : (34 * (memL P).length + 24) * (memL P).length = (34 * total P + 24) * total P := by
        rw [length_memL]
      simp only [Kwd, size_condLt, size_var]
      omega
    · rw [hout3, hout2, hout1, wdOut_eq]; rfl
  · rw [if_neg hkn]
    have hc : (Cond.lt (V "hs_n") (V "hs_k")).evalB B σ1 = some true := by
      rw [evalB_condLt (evalB_var (by rw [hn1]; omega)) (evalB_var (by rw [hk1]; omega)), hn1, hk1]
      simp; omega
    obtain ⟨σ2, r2, hout2⟩ := (writeNo_spec (B := B) (by omega)).run (σ := σ1) trivial
    refine ⟨σ2, (r1.seq (Run.ite_true hc r2)).mono (by simp only [Kwd, size_condLt, size_var]; omega), ?_⟩
    rw [hout2, hout1]; rfl

/-! ## Compilation and bounds -/

def layout : Layout := ⟨wdVars, wdArrs, 8⟩

set_option maxHeartbeats 2000000 in
theorem wdProg_ok : Com.Ok layout wdProg := by
  refine ⟨Param.readHS_ok layout (fun y hy => by simp [layout, wdVars, hy])
    (fun a ha => by
      simp only [Param.parseArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl <;> simp [layout, wdArrs]) (by simp [layout]), ?_⟩
  simp [layout, wdVars, wdArrs, parseVars, Firsts.prepVars, writeNo, wdMain, prep, prepHead,
    firstsLoop, firstBody, scanLoop, scanBody, outWD, vertLoop, vertBody, edgeLoop, edgeBody,
    incLoop, incBody, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

theorem arith_wd (L : ℕ) :
    (34 * L + 24) * L + 14 * (2 * L) + 36 * L + 200 ≤ 200 * (L + 1) ^ 3 := by
  ring_nf
  nlinarith [Nat.zero_le (L ^ 3), Nat.zero_le (L ^ 2)]

theorem Kwd_le (P : Instance) (k : ℕ) : Kwd P k ≤ 400 * ((word P k).length + 1) ^ 3 := by
  have hr := Kread_le P k
  obtain ⟨h1, -, -, -, -⟩ := dims P k
  generalize (word P k).length = L at hr h1
  have hT : total P ≤ L := by omega
  have hN : NN P k ≤ 2 * L := by unfold NN kk; omega
  have e1 : (34 * total P + 24) * total P ≤ (34 * L + 24) * L := Nat.mul_le_mul (by omega) hT
  have e2 := arith_wd L
  unfold Kwd; omega

/-- The value bound, on the tape `y = x.length :: x`. -/
def Bwd (y : List ℕ) : ℕ := 2 ^ (y.length + 5)

/-- The cost bound, on the tape. -/
def Kt (y : List ℕ) : ℕ := 400 * (y.length + 1) ^ 3

theorem solves : Solves layout wdProg (Tapes HittingSet.Domain) (fun y => redWD y.tail) Bwd Kt := by
  refine ⟨wdProg_ok, ?_, ?_⟩
  · rintro y ⟨x, ⟨P, k, rfl⟩, rfl⟩ v hv
    have := Param.inp_lt P k hv
    have h2 : 2 ^ ((word P k).length + 1) ≤ Bwd ((word P k).length :: word P k) := by
      unfold Bwd; exact Nat.pow_le_pow_right (by norm_num) (by simp)
    omega
  · rintro y ⟨x, ⟨P, k, rfl⟩, rfl⟩
    refine ⟨extWD P, ?_⟩
    obtain ⟨σ', r, hout⟩ := wdProg_run (B := Bwd ((word P k).length :: word P k)) P k
      (word P k).length (by unfold Bwd; exact Nat.pow_le_pow_right (by norm_num) (by simp))
    refine ⟨σ', r.mono ?_, by rw [hout]; rfl⟩
    have := Kwd_le P k
    have h : ((word P k).length + 1) ^ 3 ≤ ((word P k).length + 1 + 1) ^ 3 :=
      Nat.pow_le_pow_left (by omega) 3
    simp only [Kt, List.length_cons]; omega

/-- The entries of the output are below `2 ^ (L + 3)`. -/
theorem out_lt (P : Instance) (k : ℕ) {v : ℕ} (hv : v ∈ redWD (word P k)) :
    v < 2 ^ ((word P k).length + 3) := by
  obtain ⟨hmT, hn, hm, hk, -⟩ := dims P k
  have hL2 : (word P k).length < 2 ^ (word P k).length := Nat.lt_two_pow_self
  have hB8 : 2 ^ ((word P k).length + 3) = 8 * 2 ^ (word P k).length := by ring
  rw [redWD_word] at hv
  split_ifs at hv
  · rw [wdOut_eq] at hv
    have := outList_le (firsts (memL P)) (ownL P) (NN P k) P.m (total P) (kk P k)
      (3 * (word P k).length + 3)
      (fun v hv => by have := firsts_lt P hv; omega)
      (fun v hv => by have := ownL_mem_lt P hv; unfold NN kk; omega)
      (by unfold NN kk; omega) (by omega) (by unfold kk; omega) (by omega)
      (by rw [length_firsts, length_memL]) (length_ownL P) v hv
    omega
  · have : v ≤ 3 := by simp [noWD] at hv; omega
    omega

/-! ## Polynomial time -/

/-- The constant of the polynomial bound. -/
def c₁ : ℕ := 100000

theorem pow_le_c₁ (s a : ℕ) (h : a ≤ 9 * (s + 1)) : 2 ^ a ≤ 2 ^ (c₁ * (s + 1) ^ 3) := by
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have : s + 1 ≤ (s + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold c₁; omega

theorem polyTime : PolyTimeOn HittingSet.Domain redWD := by
  refine polyTimeOn_of_solves (c₀ := c₁) (d := 3) solves ?_ ?_ ?_
  · rintro x ⟨P, k, rfl⟩
    have hlen := length_le_bitSize (word P k)
    generalize bitSize (word P k) = s at hlen ⊢
    have hB : Bwd ((word P k).length :: word P k) = 2 ^ ((word P k).length + 6) := by simp [Bwd]
    rw [hB]
    generalize (word P k).length = L at hlen ⊢
    have h32 : 32 ≤ 2 ^ (L + 6) := by
      calc 32 = 2 ^ 5 := rfl
        _ ≤ 2 ^ (L + 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨by omega, ?_⟩
    have hspan : layout.span (2 ^ (L + 6)) ≤ 2 ^ (L + 9) := by
      simp only [Layout.span, layout, wdVars, wdArrs, parseVars, Firsts.prepVars,
        List.length_cons, List.length_nil, List.length_append]
      have : 2 ^ (L + 9) = 8 * 2 ^ (L + 6) := by ring
      omega
    have hle : 2 ^ (L + 9) ≤ 2 ^ (c₁ * (s + 1) ^ 3) := pow_le_c₁ s _ (by omega)
    have h69 : 2 ^ (L + 6) ≤ 2 ^ (L + 9) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact max_le (h69.trans hle) (hspan.trans hle)
  · rintro x ⟨P, k, rfl⟩
    have hlen := length_le_bitSize (word P k)
    simp only [Kt, List.length_cons, Layout.const]
    generalize bitSize (word P k) = s at hlen ⊢
    generalize (word P k).length = L at hlen ⊢
    have h1 : (L + 1 + 1) ^ 3 ≤ (2 * (s + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h2 : (2 * (s + 1)) ^ 3 = 8 * (s + 1) ^ 3 := by ring
    have h3 : 1 ≤ (s + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
    unfold c₁
    omega
  · rintro x ⟨P, k, rfl⟩ v hv
    have hlen := length_le_bitSize (word P k)
    exact lt_of_lt_of_le (out_lt P k hv) (pow_le_c₁ _ _ (by omega))

/--
---
conclusion: Lax496464.WH_E1_HittingSetInW2.hittingSet_le_pWD
---
**`p-Hitting-Set ≤fpt p-WD_hs`.** On the word of `(P, k)` the reduction writes, when `k ≤ n`, the
structure of the compressed instance (universe: the first occurrences of the members plus `min k m`
spare elements, then one element per set; `VERT`, `EDGE` and the incidence relation `I`) with weight
`min k m`, and a fixed no-instance when `k > n`; the witnesses of `hs(X)` of that weight are the
hitting sets of that size, and compression keeps the answer. The new parameter is at most `k + 1`,
and an IMP+ program computes the reduction within `100000 (|x| + 1)^3` steps.
-/
theorem hittingSet_le_pWD : HittingSet ≤ᶠᵖᵗ pWD hsFormula 1 :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime isReduction paramBounded polyTime

example : type_of% @Lax496464.WH_E1_HittingSetInW2.hittingSet_le_pWD := hittingSet_le_pWD

end Lax496464Proofs.WHierarchy.HittingSet.WDFinal
