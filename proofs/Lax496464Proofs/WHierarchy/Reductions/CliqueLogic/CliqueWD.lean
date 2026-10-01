import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgCommon
import Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.WDMath

/-!
# `p-Clique ≤fpt p-WD_clique`

The program `progWD` reads the word, then writes the word of the graph structure followed by `k`.
It runs in time `O(|x|³)` with values below `(|x| + 2)² + max x + 9`, so the reduction is
computable in polynomial time; with the construction and the parameter bound of `WDMath` it is an
fpt-reduction.
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.CliqueWD

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer
open Lax271696.VertexCover
open Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems
open Lax496464.WH_D01_CliqueInW1
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.ReadTape
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.GraphStructure
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgAdj
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgPass
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgEmit
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgCommon
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.MCMath
open Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.WDMath

set_option maxHeartbeats 4000000 in
theorem progWD_ok : Com.Ok layout progWD := by
  simp [layout, progVars, progWD, readTape, readLoop, readBody, headCom, graphCom, countPass,
    countLoop, countRow, countBody, emitPass, emitRow, emitBody, emitIf, adjTest, adjPrep,
    adjLoop, adjBody, adjStep, bump, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

/-- The cost of `progWD`. -/
def Kwd (x : List ℕ) : ℕ := 16 * x.length + 7 + (20 + (Kgraph x + 3))

set_option maxHeartbeats 1000000 in
theorem tail_spec {x : List ℕ} (hx : Good x) (hne : x ≠ []) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.out = [])
      (.seq headCom (.seq graphCom (.write (.var "g_k"))))
      (fun _ σ' => σ'.out = redWD x) (20 + (Kgraph x + 3)) := by
  have hB := fits_Bv x
  have hk := kOf_lt hne hB
  run_vcg [headCom_spec hne hB, graphCom_value hx hB]
  all_goals (try exact ⟨‹_›, ‹_›⟩)
  all_goals
    obtain ⟨⟨hn1, hk1⟩, ⟨hkv1, hka1, -⟩, ho1⟩ :=
      ‹(_ ∧ _) ∧ Keep headVars σ _ ∧ _›
  all_goals (try exact ⟨by rw [hka1]; exact ‹σ.arrs "a" = x›, hn1⟩)
  all_goals
    obtain ⟨ho2, hkv2, -, -⟩ := ‹_ ∧ Keep passVars _ _›
    have ek := hkv2 "g_k" (by decide)
    simp_all [redWD, kOf]

theorem progWD_run {x : List ℕ} (hx : Good x) (hne : x ≠ []) :
    ∃ σ', Run (Bv x) progWD
      (initEnv (fun a => if a = "a" then x.length else 0) (x.length :: x)) σ' (Kwd x) ∧
      σ'.out = redWD x := by
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
def Ktape (y : List ℕ) : ℕ := Kwd y.tail

theorem solves :
    Solves layout progWD (Tapes Clique.Domain) (fun y => redWD y.tail) Btape Ktape := by
  refine ⟨progWD_ok, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩ v hv
    have hB := fits_Bv x
    simp only [Btape, List.tail_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · have := hB.len_lt; omega
    · exact hB.entries v hv
  · rintro y ⟨x, ⟨n, G, k, h⟩, rfl⟩
    obtain ⟨hx, hne⟩ := good_of_param h
    obtain ⟨σ', hr, ho⟩ := progWD_run hx hne
    exact ⟨_, σ', hr, ho⟩

/-! ### The time bound -/

theorem Kwd_le {x : List ℕ} (hx : Good x) : 10 * Kwd x + 1 ≤ 4000 * (bitSize x + 1) ^ 3 := by
  have h1 := Kgraph_le hx
  have hL := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
  have h2 : (x.length + 1) ^ 3 ≤ (bitSize x + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h3 : x.length + 1 ≤ (x.length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold Kwd
  omega

/-- Every entry of the graph word is at most `n² + 2`. -/
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

theorem out_lt {x : List ℕ} (hx : Good x) {v : ℕ} (hv : v ∈ redWD x) :
    v < 2 ^ (4000 * (bitSize x + 1) ^ 3) := by
  have hBv := Bv_add_le x 4000 (by norm_num)
  have hsq := sq_lt hx (fits_Bv x)
  rw [redWD, List.mem_append] at hv
  rcases hv with hv | hv
  · have := le_of_mem_graphWord hv; omega
  · simp only [List.mem_singleton] at hv
    subst hv
    have := kOf_le_Mmax x
    unfold kOf at this
    unfold Bv at hBv; omega

/-- Step 3: the reduction is computable in polynomial time. -/
theorem polyTimeOn : PolyTimeOn Clique.Domain redWD := by
  refine polyTimeOn_of_solves (c₀ := 4000) (d := 3) solves (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx v hv => ?_)
  · obtain ⟨n, G, k, h⟩ := hx
    refine ⟨?_, ?_⟩
    · simp only [Btape, List.tail_cons, Bv]; omega
    · simp only [Btape, List.tail_cons]; exact span_le x 4000 (by norm_num)
  · obtain ⟨n, G, k, h⟩ := hx
    simp only [Ktape, List.tail_cons, Layout.const]
    exact Kwd_le (good_of_param h).1
  · obtain ⟨n, G, k, h⟩ := hx
    exact out_lt (good_of_param h).1 hv

/--
---
conclusion: Lax496464.WH_D01_CliqueInW1.clique_le_pWD
---
**`p-Clique ≤fpt p-WD_clique`.** A graph becomes the structure with universe its vertices and one
binary relation, its edges (listed from the adjacency matrix, so without repetition), and `k`
stays `k`. The witnesses of `clique(X)` of weight `k` are the `k`-cliques, the parameter is
unchanged, and the map is computed by an IMP+ program in `O(|x|³)` steps.
-/
theorem clique_le_pWD : Clique ≤ᶠᵖᵗ Lax496464.WH_B3_LogicProblems.pWD cliqueFormula 1 :=
  Lax496464.WH_A5_Bridges.fptReduces_of_polyTime isReduction paramBounded polyTimeOn

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.CliqueWD
