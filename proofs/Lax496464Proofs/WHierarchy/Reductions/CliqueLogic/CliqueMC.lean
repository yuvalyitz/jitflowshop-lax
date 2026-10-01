import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgCommon
import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgFormula

/-!
# `p-Clique ≤fpt p-MC(Σ_1)`

The program `progMC` reads the word and `k`; for `k = 0` it writes the fixed yes-instance, for
`k > n` the fixed no-instance, and otherwise the word of the graph structure followed by the code
of `clique_k`. Since `k ≤ n` in the last case, it runs in time `O(|x|³)`, so the reduction is
computable in polynomial time; with the construction and the parameter bound of `MCMath` it is an
fpt-reduction.
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.CliqueMC

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer
open Lax271696.VertexCover
open Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.ReadTape
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgPass
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgEmit
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgFormula
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgCommon
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.MCMath

set_option maxHeartbeats 4000000 in
theorem progMC_ok : Com.Ok layout progMC := by
  simp [layout, progVars, progMC, readTape, readLoop, readBody, headCom, branchMC, writeList,
    writeExprs, graphCom, countPass, countLoop, countRow, countBody, emitPass, emitRow, emitBody,
    emitIf, adjTest, adjPrep, adjLoop, adjBody, adjStep, formulaCom, quantLoop, quantBody,
    pairLoop, pairRow, itemIf, itemCom, bump, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

theorem Kform_mono {k n : ℕ} (h : k ≤ n) : Kform k ≤ Kform n := by
  unfold Kform
  have := Nat.mul_le_mul (show k + 1 ≤ n + 1 by omega) (show k + 1 ≤ n + 1 by omega)
  nlinarith

/-- The main branch: the graph, then the formula. -/
theorem mainBranch_spec {x : List ℕ} (hx : Good x) :
    Spec (Bv x) (fun σ => Ctx x σ ∧ σ.vars "g_k" = kOf x ∧ kOf x ≤ nV x) (.seq graphCom formulaCom)
      (fun σ σ' => σ'.out = σ.out ++ (graphWord x ++ (cliqueSent (kOf x)).encode))
      (Kgraph x + Kform (nV x)) := by
  intro σ ⟨hc, hk, hkn⟩
  have hB := fits_Bv x
  have hk8 : kOf x + 8 < Bv x := by have := n_lt hx hB; omega
  obtain ⟨σ1, hr1, ho1, hkv1, -, -⟩ := graphCom_value hx hB σ hc
  have hk1 : σ1.vars "g_k" = kOf x := by rw [hkv1 "g_k" (by decide), hk]
  obtain ⟨σ2, hr2, ho2, -⟩ := formulaCom_spec hk8 σ1 hk1
  refine ⟨σ2, (hr1.seq hr2).mono (Nat.add_le_add_left (Kform_mono hkn) _), ?_⟩
  show σ2.out = σ.out ++ (graphWord x ++ (cliqueSent (kOf x)).encode)
  rw [ho2, ho1, List.append_assoc]

/-- The cost of `progMC`. -/
def Kmc (x : List ℕ) : ℕ := 16 * x.length + 7 + (20 + (Kgraph x + Kform (nV x) + 100))

set_option maxHeartbeats 2000000 in
theorem tail_spec {x : List ℕ} (hx : Good x) (hne : x ≠ []) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.out = [])
      (.seq headCom branchMC)
      (fun _ σ' => σ'.out = redMC x) (20 + (Kgraph x + Kform (nV x) + 100)) := by
  have hB := fits_Bv x
  have hk := kOf_lt hne hB
  have hn := n_lt hx hB
  simp only [branchMC, writeList, writeExprs, List.map]
  run_vcg [headCom_spec hne hB, mainBranch_spec hx]
  all_goals (try exact ⟨‹_›, ‹_›⟩)
  all_goals
    obtain ⟨⟨hn1, hk1⟩, ⟨hkv1, hka1, -⟩, ho1⟩ :=
      ‹(_ ∧ _) ∧ Keep headVars σ _ ∧ _›
  all_goals (try (simp_all [redMC, yesWord_eq, noWord_eq]; done))
  all_goals
    refine ⟨⟨by rw [hka1]; assumption, hn1⟩, hk1, ?_⟩
    rename_i hc1 hc2
    rw [hn1, hk1] at hc2
    omega

theorem progMC_run {x : List ℕ} (hx : Good x) (hne : x ≠ []) :
    ∃ σ', Run (Bv x) progMC
      (initEnv (fun a => if a = "a" then x.length else 0) (x.length :: x)) σ' (Kmc x) ∧
      σ'.out = redMC x := by
  have hB := fits_Bv x
  have hl := hB.len_lt
  set σ0 := initEnv (fun a => if a = "a" then x.length else 0) (x.length :: x) with hσ0
  have h1 := readTape_spec x σ0 hB.entries (by omega) rfl (by simp [σ0, initEnv])
  have h := Spec.seq h1 (tail_spec hx hne) (fun σ σ' _ h => ⟨h.1, h.2.1, by rw [h.2.2.2.1]; rfl⟩)
    (fun _ _ _ _ _ h => h)
  exact h σ0 rfl

/-- The value bound, as a function of the tape. -/
def Btape (y : List ℕ) : ℕ := Bv y.tail

/-- The cost, as a function of the tape. -/
def Ktape (y : List ℕ) : ℕ := Kmc y.tail

theorem solves :
    Solves layout progMC (Tapes Clique.Domain) (fun y => redMC y.tail) Btape Ktape := by
  refine ⟨progMC_ok, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩ v hv
    have hB := fits_Bv x
    simp only [Btape, List.tail_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · have := hB.len_lt; omega
    · exact hB.entries v hv
  · rintro y ⟨x, ⟨n, G, k, h⟩, rfl⟩
    obtain ⟨hx, hne⟩ := good_of_param h
    obtain ⟨σ', hr, ho⟩ := progMC_run hx hne
    exact ⟨_, σ', hr, ho⟩

/-! ### The time bound -/

theorem Kmc_le {x : List ℕ} (hx : Good x) : 10 * Kmc x + 1 ≤ 8000 * (bitSize x + 1) ^ 3 := by
  have h1 := Kgraph_le hx
  have hn := nV_le hx
  have hL := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
  have h2 : (x.length + 1) ^ 3 ≤ (bitSize x + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : x.length + 1 ≤ (x.length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h4 : Kform (nV x) ≤ 100 * (x.length + 1) ^ 3 := by
    unfold Kform
    have e : (x.length + 1) ^ 3 = (x.length + 1) * (x.length + 1) * (x.length + 1) := by ring
    have h5 : (nV x + 1) * (nV x + 1) ≤ (x.length + 1) * (x.length + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h6 : 1 ≤ x.length + 1 := by omega
    rw [e]; nlinarith
  unfold Kmc
  omega

theorem le_of_mem_graphWord {x : List ℕ} {v : ℕ} (hv : v ∈ graphWord x) :
    v ≤ nV x * nV x + 2 := by
  rw [graphWord_eq] at hv
  have hM := length_pairs_le x
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_flatten] at hv
  rcases hv with rfl | rfl | rfl | rfl | ⟨t, ht, hvt⟩
  · omega
  · omega
  · nlinarith
  · omega
  · obtain ⟨u, w, hu, hw, -, rfl⟩ := mem_pairs.mp ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hvt
    rcases hvt with rfl | rfl <;> nlinarith

/-- Every entry of the code of `clique_k` is at most `k + 6`. -/
theorem le_of_mem_cliqueSent {k v : ℕ} (hv : v ∈ (cliqueSent k).encode) : v ≤ k + 6 := by
  rw [encode_cliqueSent] at hv
  simp only [quantEnc, pairsEnc, List.mem_append, List.mem_flatMap, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (⟨i, hi, rfl | rfl⟩ | ⟨i, hi, j, hj, hvj⟩) | (rfl | rfl | rfl)
  · omega
  · omega
  · split at hvj
    · simp only [itemEnc, List.mem_cons, List.not_mem_nil, or_false] at hvj
      rcases hvj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · simp at hvj
  · omega
  · omega
  · omega

theorem out_lt {x : List ℕ} (hx : Good x) {v : ℕ} (hv : v ∈ redMC x) :
    v < 2 ^ (8000 * (bitSize x + 1) ^ 3) := by
  have hBv := Bv_add_le x 8000 (by norm_num)
  have hsq := sq_lt hx (fits_Bv x)
  unfold redMC at hv
  split_ifs at hv with h0 h1
  · rw [yesWord_eq] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [noWord_eq] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · rw [List.mem_append] at hv
    rcases hv with hv | hv
    · have := le_of_mem_graphWord hv; omega
    · have := le_of_mem_cliqueSent hv
      have : nV x * 1 ≤ nV x * nV x ∨ nV x = 0 := by
        rcases Nat.eq_zero_or_pos (nV x) with h | h
        · exact Or.inr h
        · exact Or.inl (Nat.mul_le_mul_left _ h)
      omega

/-- Step 3: the reduction is computable in polynomial time. -/
theorem polyTimeOn : PolyTimeOn Clique.Domain redMC := by
  refine polyTimeOn_of_solves (c₀ := 8000) (d := 3) solves (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx v hv => ?_)
  · obtain ⟨n, G, k, h⟩ := hx
    refine ⟨?_, ?_⟩
    · simp only [Btape, List.tail_cons, Bv]; omega
    · simp only [Btape, List.tail_cons]; exact span_le x 8000 (by norm_num)
  · obtain ⟨n, G, k, h⟩ := hx
    simp only [Ktape, List.tail_cons, Layout.const]
    exact Kmc_le (good_of_param h).1
  · obtain ⟨n, G, k, h⟩ := hx
    exact out_lt (good_of_param h).1 hv

/--
---
conclusion: Lax496464.WH_D02_CliqueInA1.clique_le_pMC
---
**`p-Clique ≤fpt p-MC(Σ_1)`.** `(G, k) ↦ (G, clique_k)` with
`clique_k = ∃x_0 … ∃x_{k-1} ⋀_{i<j<k} (¬ x_i = x_j ∧ E x_i x_j)` (the conjunction closed by
`x_0 = x_0`), for `1 ≤ k ≤ n`; `k = 0` goes to a fixed yes-instance and `k > n` to a fixed
no-instance. The new parameter is at most `10 (k + 1)²`, and the map is computed by an IMP+ program
in `O(|x|³)` steps.
-/
theorem clique_le_pMC :
    Clique ≤ᶠᵖᵗ Lax496464.WH_B3_LogicProblems.pMC {φ | IsSigma 1 φ} :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime isReduction paramBounded polyTimeOn

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.CliqueMC
