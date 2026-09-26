import Lax496464Proofs.Ram.Corollary1Init
import Lax496464Proofs.Ram.BuildSorted
import Lax496464Proofs.Ram.EstSort
import Lax496464Proofs.Ram.Nxt1
import Lax496464Proofs.Ram.Decode
import Lax496464Proofs.Ram.Reduction
import Lax496464Proofs.Ram.Fits
import Lax496464.Corollary1

/-!
# Corollary 1: the whole program

Read the instance and the threshold, sort the jobs by start time, build the sorted arrays,
find the table's sentinel, scan for every job's `nxt`, set up the table, fill it column by
column, and write the answer.
-/

namespace Lax496464Proofs.Ram.Corollary1Prog

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.Decode (readInstance readInstance_decoded Decoded)
open Lax496464Proofs.Ram.EstSort (estSortCom estSort_spec dA qA rEst)
open Lax496464Proofs.Ram.BuildSorted (buildSorted buildSorted_spec)
open Lax496464Proofs.Ram.Corollary1Init (maxScan maxScan_spec initRest initRest_spec)
open Lax496464Proofs.Ram.Nxt1 (nxtLoop nxtLoop_spec Res res_isNxt)
open Lax496464Proofs.Ram.Cols1 (colsLoop colsLoop_spec CA)
open Lax496464Proofs.Ram.Col1 (Dat)

/-- **The whole program.** -/
def prog : Com :=
  .seq readInstance
    (.seq (.read "W")
      (.seq (.assign "en" (V "n"))
        (.seq (.assign "sn" (V "n"))
          (.seq estSortCom
            (.seq buildSorted
              (.seq maxScan
                (.seq nxtLoop
                  (.seq initRest
                    (.seq colsLoop (.write (V "ans")))))))))))

open Lax808846Proofs.Compile

/-- The layout of the program: every scalar and array every sub-program of the pipeline
addresses, and room for the deepest expression any of them compiles. -/
def L1 : Layout :=
  ⟨["n", "m", "v", "i", "len", "en", "sn", "sc", "si", "sx", "sy", "ct1", "ct2", "shi", "sj",
    "sk", "slo", "smid", "snp", "spc", "stl", "sw", "bi", "boff", "bt", "bv", "W", "ans",
    "cinf", "mi", "mv", "sn1", "dj", "dy", "ny", "qy", "res", "tt", "c0", "ck", "cwp", "wc",
    "cd", "ce", "cf", "cg", "ci", "cj", "cn", "cp", "cq", "ct", "cw", "cy"],
   ["A", "SA", "SB", "PS", "QS", "DS", "NX", "CC", "PC"], 12⟩

set_option maxHeartbeats 4000000 in
theorem prog_ok : Com.Ok L1 prog := by
  simp [prog, Lax496464Proofs.Ram.Decode.readInstance, Lax496464Proofs.Ram.Decode.readLoop,
    Lax496464Proofs.Ram.Decode.readBody, estSortCom, Lax496464Proofs.Ram.EstSort.fillIdent,
    Lax496464Proofs.Ram.EstSort.estCmp, Lax496464Proofs.Ram.EstSort.estSums,
    Lax496464Proofs.Ram.EstSort.estDecide, Lax496464Proofs.Ram.Sort.tlSetup,
    Lax496464Proofs.Ram.Sort.moveK, Lax496464Proofs.Ram.Sort.mergeBody,
    Lax496464Proofs.Ram.Sort.mergeLoop, Lax496464Proofs.Ram.Sort.blockSetup,
    Lax496464Proofs.Ram.Sort.blockBody, Lax496464Proofs.Ram.Sort.blockLoop,
    Lax496464Proofs.Ram.Sort.copyLoop, Lax496464Proofs.Ram.Sort.npLoop,
    Lax496464Proofs.Ram.Sort.passCom, Lax496464Proofs.Ram.Sort.passBody,
    Lax496464Proofs.Ram.Sort.sortCom, buildSorted, Lax496464Proofs.Ram.BuildSorted.buildRow,
    maxScan,
    Lax496464Proofs.Ram.Corollary1Init.maxBody, nxtLoop, Lax496464Proofs.Ram.Nxt1.nxtBody,
    Lax496464Proofs.Ram.Nxt1.scanLoop, Lax496464Proofs.Ram.Nxt1.scanBody, initRest,
    Lax496464Proofs.Ram.Cols1.fillInf, colsLoop, Lax496464Proofs.Ram.Cols1.colsBody,
    Lax496464Proofs.Ram.Cols1.ansCheck, Lax496464Proofs.Ram.Cols1.copyCol,
    Lax496464Proofs.Ram.Col1.colCol, Lax496464Proofs.Ram.Col1.colBody,
    Lax496464Proofs.Ram.Col1.colFetch, Lax496464Proofs.Ram.Col1.fCom,
    Lax496464Proofs.Ram.Col1.colStore, Com.Ok, Expr.Ok, Cond.Ok, L1, condExpr, V, bump]

open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.Problems Lax496464Proofs.Ram.EstPermute
open Lax496464Proofs.Ram.Dp1 Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.Col1

/-! ## The word's prefix agrees with the instance part

`y ++ [W]` is one entry longer than `y`, so it can never satisfy `EncodesInstance`'s exact
`length_eq` — but every read `Decode` performs on `x := y ++ [W]` lands at an index strictly
below `y.length`, so each read agrees with the same read on `y`, and hence (via `h`) with `I`. -/

theorem jobCount_append (y : List ℕ) (W : ℕ) (hy : 0 < y.length) :
    jobCount (y ++ [W]) = jobCount y := by
  show (y ++ [W]).getD 0 0 = y.getD 0 0
  rw [List.getD_append _ _ _ _ hy]

theorem machineCount_append (y : List ℕ) (W : ℕ) (hy : 1 < y.length) :
    machineCount (y ++ [W]) = machineCount y := by
  show (y ++ [W]).getD 1 0 = y.getD 1 0
  rw [List.getD_append _ _ _ _ hy]

theorem decision_word_facts {y : List ℕ} {I : Instance} {W : ℕ}
    (h : EncodesInstance y I) :
    jobCount (y ++ [W]) = I.jobs ∧ machineCount (y ++ [W]) = I.machines ∧
      (∀ j : I.Job, preTime (y ++ [W]) j = I.p j) ∧
      (∀ j : I.Job, procTime (y ++ [W]) j = I.q j) ∧
      (∀ j : I.Job, due (y ++ [W]) j = I.d j) ∧
      (∀ j : I.Job, wt (y ++ [W]) j = I.w j) := by
  have hjc : jobCount (y ++ [W]) = jobCount y :=
    jobCount_append y W (by rw [h.length_eq]; omega)
  have hmc : machineCount (y ++ [W]) = machineCount y :=
    machineCount_append y W (by rw [h.length_eq]; omega)
  refine ⟨by rw [hjc]; exact h.jobCount_eq, by rw [hmc]; exact h.machineCount_eq,
    fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · have hb : 2 + (j : ℕ) < y.length := by rw [h.length_eq]; have := j.isLt; omega
    show (y ++ [W]).getD (2 + j) 0 = I.p j
    rw [List.getD_append _ _ _ _ hb]; exact h.preTime_eq j
  · have hb : 2 + jobCount y + (j : ℕ) < y.length := by
      rw [h.length_eq, h.jobCount_eq]; have := j.isLt; omega
    show (y ++ [W]).getD (2 + jobCount (y ++ [W]) + j) 0 = I.q j
    rw [hjc, List.getD_append _ _ _ _ hb]; exact h.procTime_eq j
  · have hb : 2 + 2 * jobCount y + (j : ℕ) < y.length := by
      rw [h.length_eq, h.jobCount_eq]; have := j.isLt; omega
    show (y ++ [W]).getD (2 + 2 * jobCount (y ++ [W]) + j) 0 = I.d j
    rw [hjc, List.getD_append _ _ _ _ hb]; exact h.due_eq j
  · have hb : 2 + 3 * jobCount y + (j : ℕ) < y.length := by
      rw [h.length_eq, h.jobCount_eq]; have := j.isLt; omega
    show (y ++ [W]).getD (2 + 3 * jobCount (y ++ [W]) + j) 0 = I.w j
    rw [hjc, List.getD_append _ _ _ _ hb]; exact h.wt_eq j

/-! ## The sorted arrays, for a word that is only `EncodesDecisionInstance` -/

open Lax496464Proofs.Ram.BuildSorted (buildRow)

/-- The arrays `buildSorted` writes are `pv`, `qv`, `dv` of the permuted instance, from the
three field equalities rather than a full `EncodesInstance x I` (which `x := y ++ [W]` cannot
satisfy). -/
theorem sortedArrays_eq {x : List ℕ} {I : Instance}
    (hp : ∀ j : I.Job, preTime x j = I.p j) (hq : ∀ j : I.Job, procTime x j = I.q j)
    (hd : ∀ j : I.Job, due x j = I.d j)
    (P : List ℕ) (hperm : P.Perm (List.range I.jobs)) (n : ℕ) (hn : n = I.jobs) :
    (∀ k < n, ((List.range n).map (fun k => preTime x (P.getD k 0))).getD k 0 =
      pv (permute I (listEquiv I.jobs P hperm)) k) ∧
    (∀ k < n, ((List.range n).map (fun k => procTime x (P.getD k 0))).getD k 0 =
      qv (permute I (listEquiv I.jobs P hperm)) k) ∧
    (∀ k < n, ((List.range n).map (fun k => due x (P.getD k 0))).getD k 0 =
      dv (permute I (listEquiv I.jobs P hperm)) k) := by
  subst hn
  have hklen : ∀ (f : ℕ → ℕ) k, k < I.jobs →
      ((List.range I.jobs).map f).getD k 0 = f k := by
    intro f k hk
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
    rfl
  have hPlen : P.length = I.jobs := by rw [hperm.length_eq]; simp
  have hPk : ∀ k, k < I.jobs → P.getD k 0 < I.jobs := by
    intro k hk
    have hkP : k < P.length := by omega
    have : P.getD k 0 ∈ P := by
      rw [List.getD_eq_getElem _ _ hkP]; exact List.getElem_mem hkP
    have := hperm.mem_iff.mp this
    simpa using this
  have heq : ∀ k, (h : k < I.jobs) →
      (listEquiv I.jobs P hperm ⟨k, h⟩ : Fin I.jobs) = ⟨P.getD k 0, hPk k h⟩ :=
    fun k h => Fin.ext (listEquiv_apply I.jobs P hperm ⟨k, h⟩)
  refine ⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rw [hklen _ k hk]
    have hpv : pv (permute I (listEquiv I.jobs P hperm)) k
        = I.p (listEquiv I.jobs P hperm ⟨k, hk⟩) := dif_pos hk
    have hpv2 : pv I (P.getD k 0) = I.p ⟨P.getD k 0, hPk k hk⟩ := dif_pos (hPk k hk)
    rw [hpv, heq k hk, ← hp]
  · rw [hklen _ k hk]
    have hqv : qv (permute I (listEquiv I.jobs P hperm)) k
        = I.q (listEquiv I.jobs P hperm ⟨k, hk⟩) := dif_pos hk
    have hqv2 : qv I (P.getD k 0) = I.q ⟨P.getD k 0, hPk k hk⟩ := dif_pos (hPk k hk)
    rw [hqv, heq k hk, ← hq]
  · rw [hklen _ k hk]
    have hdv : dv (permute I (listEquiv I.jobs P hperm)) k
        = I.d (listEquiv I.jobs P hperm ⟨k, hk⟩) := dif_pos hk
    have hdv2 : dv I (P.getD k 0) = I.d ⟨P.getD k 0, hPk k hk⟩ := dif_pos (hPk k hk)
    rw [hdv, heq k hk, ← hd]

/-- The lists `buildSorted` produces (read raw off `A`) agree pointwise with `preTime`,
`procTime`, `due` of `x` through the permutation, when every index it reads is a job. -/
theorem buildSorted_arrays_eq {x : List ℕ} {A : List ℕ} (n : ℕ)
    (hA1 : ∀ j < n, A.getD j 0 = preTime x j) (hA2 : ∀ j < n, A.getD (n + j) 0 = procTime x j)
    (hA3 : ∀ j < n, A.getD (2 * n + j) 0 = due x j) (P : List ℕ)
    (hPn : ∀ k < n, P.getD k 0 < n) :
    (List.range n).map (fun k => A.getD (P.getD k 0) 0) =
      (List.range n).map (fun k => preTime x (P.getD k 0)) ∧
    (List.range n).map (fun k => A.getD (n + P.getD k 0) 0) =
      (List.range n).map (fun k => procTime x (P.getD k 0)) ∧
    (List.range n).map (fun k => A.getD (2 * n + P.getD k 0) 0) =
      (List.range n).map (fun k => due x (P.getD k 0)) := by
  refine ⟨List.map_congr_left fun k hk => ?_, List.map_congr_left fun k hk => ?_,
    List.map_congr_left fun k hk => ?_⟩ <;>
    · rw [List.mem_range] at hk
      first
        | exact hA1 _ (hPn k hk)
        | exact hA2 _ (hPn k hk)
        | exact hA3 _ (hPn k hk)

/-! ## Reading, sorting, and building the arrays -/

open Lax496464Proofs.Ram.EstSort (EBase)

set_option maxHeartbeats 4000000 in
/-- Read `x`'s instance and threshold, sort the jobs by earliest start time, and build the
sorted `PS`/`QS`/`DS` arrays. The sorted instance `J` is the one the DP proceeds on:
`EstOrdered`, the same number of jobs as `I`, and the same answer to "is there a feasible set
of weight `W`". -/
theorem sortSetup_spec {x : List ℕ} {I : Instance} {W : ℕ} (hdec : EncodesDecisionInstance x I W)
    (hm1 : I.machines = 1) (hw1 : ∀ j : I.Job, I.w j = 1) (hqpos : ∀ j : I.Job, 0 < I.q j)
    {B : ℕ} (hB2 : 2 < B) (hxB : ∀ v ∈ x, v < B) (hnB : 4 * I.jobs + 5 < B)
    (hpqB : ∀ j : I.Job, (I.p j : ℕ) + I.q j < B) (hdq : ∀ a b : I.Job, (I.d a : ℕ) + I.q b < B)
    (hd2B : ∀ j : I.Job, (I.d j : ℕ) + 2 < B) :
    Spec B
      (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "NX").length = I.jobs ∧
        (σ.arrs "CC").length = I.jobs + 1 ∧ (σ.arrs "PC").length = I.jobs + 1)
      (.seq readInstance (.seq (.read "W") (.seq (.assign "en" (V "n"))
        (.seq (.assign "sn" (V "n")) (.seq estSortCom buildSorted)))))
      (fun _ σ' => ∃ J : Instance, EstOrdered J ∧ J.jobs = I.jobs ∧ J.machines = 1 ∧
        (∀ j : J.Job, J.w j = 1) ∧ (∀ j : J.Job, 0 < J.q j) ∧
        (∀ j : J.Job, (J.p j : ℕ) + J.q j < B) ∧ (∀ a b : J.Job, (J.d a : ℕ) + J.q b < B) ∧
        (∀ j : J.Job, (J.d j : ℕ) + 2 < B) ∧
        (∀ W', HasWeight J W' ↔ HasWeight I W') ∧
        σ'.arrs "PS" = (List.range I.jobs).map (fun k => pv J k) ∧
        σ'.arrs "QS" = (List.range I.jobs).map (fun k => qv J k) ∧
        σ'.arrs "DS" = (List.range I.jobs).map (fun k => dv J k) ∧
        σ'.vars "sn" = I.jobs ∧ σ'.vars "W" = W ∧ σ'.inp = [] ∧ σ'.out = [] ∧
        (σ'.arrs "NX").length = I.jobs ∧ (σ'.arrs "CC").length = I.jobs + 1 ∧
        (σ'.arrs "PC").length = I.jobs + 1)
      (Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 500 * I.jobs + 1000) := by
  obtain ⟨y, hxy, hEnc⟩ := hdec
  subst hxy
  obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := W) hEnc
  -- Every simple arithmetic fact this proof needs, derived once here from `hnB` while the
  -- context is still small: `omega` scans the whole local context, and once the phase
  -- lemmas below add their large `∀`-quantified postconditions to it, even a trivial
  -- `omega` call can take minutes. Every later arithmetic step must instead reuse one of
  -- these, never call `omega` itself.
  have hB1 : 1 < B := by omega
  have hIjB : I.jobs < B := by omega
  have h3B3 : 3 * I.jobs + 3 < B := by omega
  have h4B3 : 4 * I.jobs + 3 < B := by omega
  have hn1B : I.jobs + 1 < B := by omega
  have hn2B : I.jobs + 2 < B := by omega
  have h3n4n : 3 * I.jobs + I.jobs = 4 * I.jobs := by omega
  have hxlen : (y ++ [W]).length = 3 + 4 * I.jobs := by
    have := hEnc.length_eq; simp only [List.length_append, List.length_singleton]; omega
  have hjcIdx : ∀ k, k < I.jobs → k < jobCount (y ++ [W]) := fun k hk => by rw [hjc]; omega
  have hpIdx : ∀ k, k < I.jobs → 2 + k < (y ++ [W]).length := fun k hk => by omega
  have hqIdx : ∀ k, k < I.jobs → 2 + jobCount (y ++ [W]) + k < (y ++ [W]).length := fun k hk => by
    rw [hjc]; omega
  have hdIdx : ∀ k, k < I.jobs → 2 + 2 * jobCount (y ++ [W]) + k < (y ++ [W]).length := fun k hk => by
    rw [hjc]; omega
  have hwIdx : ∀ k, k < I.jobs → 2 + 3 * jobCount (y ++ [W]) + k < (y ++ [W]).length := fun k hk => by
    rw [hjc]; omega
  have hval_mem : ∀ (k : ℕ), k < (y ++ [W]).length → (y ++ [W]).getD k 0 < B := fun k hk =>
    hxB _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)
  have hpB : ∀ j : I.Job, (I.p j : ℕ) < B := fun j => by
    rw [← hpe j]; exact hval_mem _ (hpIdx j j.isLt)
  have hqB : ∀ j : I.Job, (I.q j : ℕ) < B := fun j => by
    rw [← hqe j]; exact hval_mem _ (hqIdx j j.isLt)
  have hdB : ∀ j : I.Job, (I.d j : ℕ) < B := fun j => by
    rw [← hde j]; exact hval_mem _ (hdIdx j j.isLt)
  have hwB : ∀ j : I.Job, (I.w j : ℕ) < B := fun j => by
    rw [← hwe j]; exact hval_mem _ (hwIdx j j.isLt)
  have hgetD_mem_bound : ∀ (l : List ℕ) (m : ℕ), (∀ k < m, l.getD k 0 < B) → l.length = m →
      ∀ v ∈ l, v < B := by
    intro l m hb hl v hv
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
    rw [← hkv, ← List.getD_eq_getElem _ _ hk]
    exact hb k (hl ▸ hk)
  -- Two pure list facts used to turn the raw sorted arrays into `pv`/`qv`/`dv` of the sorted
  -- instance, and the cost bound for the five phases from `readInstance` through
  -- `buildSorted` — every one derived here, before any phase lemma's big postcondition
  -- joins the context, so that these never make a later arithmetic step slow.
  have hmap_range_getD : ∀ (f : ℕ → ℕ) (n k : ℕ), k < n → ((List.range n).map f).getD k 0 = f k :=
    by intro f n k hk; rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  have hmap_ext : ∀ (n : ℕ) (f g : ℕ → ℕ), (∀ k < n, f k = g k) →
      (List.range n).map f = (List.range n).map g := fun n f g h =>
    List.map_congr_left fun k hk => h k (List.mem_range.mp hk)
  have hcost1 : 48 * jobCount (y ++ [W]) + 12 = 48 * I.jobs + 12 := by rw [hjc]
  have hcost34 : 1 + Expr.size (V "n") ≤ 3 := by decide
  have hKbound : ∀ K1 K2 K3 K4 K5 K6 : ℕ, K1 = 48 * I.jobs + 12 → K2 = 1 → K3 ≤ 3 → K4 ≤ 3 →
      K5 = ((16 + 4) * I.jobs + 6) + Lax496464Proofs.Ram.Sort.sortK 90 I.jobs →
      K6 = 4 + (((20 + 4) * I.jobs + 6) + 4 + ((20 + 4) * I.jobs + 6) + 4 +
        ((20 + 4) * I.jobs + 6)) →
      K1 + (K2 + (K3 + (K4 + (K5 + K6)))) ≤
        Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 500 * I.jobs + 1000 := by
    intro K1 K2 K3 K4 K5 K6 h1 h2 h3 h4 h5 h6; omega
  -- How a raw index `k < 4·jobs` into the decoded array `A` splits into its `p`/`q`/`d`/`w`
  -- block, purely as arithmetic on `I.jobs` — computed once so nothing below ever calls
  -- `omega` on a bound variable after the context has grown.
  have hsplit4 : ∀ k, k < 4 * I.jobs → k < I.jobs ∨ (I.jobs ≤ k ∧ k < 2 * I.jobs) ∨
      (2 * I.jobs ≤ k ∧ k < 3 * I.jobs) ∨ (3 * I.jobs ≤ k ∧ k < 4 * I.jobs) := fun k hk => by omega
  have hsub1 : ∀ k, I.jobs ≤ k → k < 2 * I.jobs → k - I.jobs < I.jobs := fun k h1 h2 => by omega
  have hsub2 : ∀ k, 2 * I.jobs ≤ k → k < 3 * I.jobs → k - 2 * I.jobs < I.jobs := fun k h1 h2 => by
    omega
  have hsub3 : ∀ k, 3 * I.jobs ≤ k → k < 4 * I.jobs → k - 3 * I.jobs < I.jobs := fun k h1 h2 => by
    omega
  have heq1 : ∀ k, I.jobs ≤ k → k = I.jobs + (k - I.jobs) := fun k h => by omega
  have heq2 : ∀ k, 2 * I.jobs ≤ k → k = 2 * I.jobs + (k - 2 * I.jobs) := fun k h => by omega
  have heq3 : ∀ k, 3 * I.jobs ≤ k → k = 3 * I.jobs + (k - 3 * I.jobs) := fun k h => by omega
  refine Spec.of_exists fun σ0 ⟨hinp0, hout0, hAl0, hSAl0, hSBl0, hPSl0, hQSl0, hDSl0, hNXl0,
      hCCl0, hPCl0⟩ => ?_
  -- Step 1: `readInstance`.
  have hlen : 2 + 4 * jobCount (y ++ [W]) ≤ (y ++ [W]).length := by
    rw [hjc]
    have hl := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]
    omega
  have hnB1 : 4 * jobCount (y ++ [W]) + 5 < B := by rw [hjc]; omega
  obtain ⟨σ1, hr1, ⟨hn1, hm1', hAl1, hA1p, hA1q, hA1d, hA1w, hinp1, hout1⟩, hfv1, hfa1, -, -⟩ :=
    (readInstance_decoded hlen hxB hnB1).frame.run (σ := σ0)
      ⟨hinp0, hout0, by rw [hjc]; exact hAl0⟩
  have hSA1 : (σ1.arrs "SA").length = I.jobs := by rw [hfa1 "SA" (by decide)]; exact hSAl0
  have hSB1 : (σ1.arrs "SB").length = I.jobs := by rw [hfa1 "SB" (by decide)]; exact hSBl0
  have hPS1 : (σ1.arrs "PS").length = I.jobs := by rw [hfa1 "PS" (by decide)]; exact hPSl0
  have hQS1 : (σ1.arrs "QS").length = I.jobs := by rw [hfa1 "QS" (by decide)]; exact hQSl0
  have hDS1 : (σ1.arrs "DS").length = I.jobs := by rw [hfa1 "DS" (by decide)]; exact hDSl0
  have hNX1 : (σ1.arrs "NX").length = I.jobs := by rw [hfa1 "NX" (by decide)]; exact hNXl0
  have hCC1 : (σ1.arrs "CC").length = I.jobs + 1 := by rw [hfa1 "CC" (by decide)]; exact hCCl0
  have hPC1 : (σ1.arrs "PC").length = I.jobs + 1 := by rw [hfa1 "PC" (by decide)]; exact hPCl0
  have hn1' : σ1.vars "n" = I.jobs := by rw [hn1, hjc]
  -- Every field of `A`'s four blocks, read as `I`'s.
  have hAp_eq : ∀ k, (hk : k < I.jobs) → (σ1.arrs "A").getD k 0 = I.p ⟨k, hk⟩ := fun k hk => by
    rw [hA1p k (hjcIdx k hk), hpe ⟨k, hk⟩]
  have hAq_eq : ∀ k, (hk : k < I.jobs) → (σ1.arrs "A").getD (I.jobs + k) 0 = I.q ⟨k, hk⟩ :=
    fun k hk => by
      have h1 := hA1q k (hjcIdx k hk)
      rw [hjc] at h1
      rw [h1, hqe ⟨k, hk⟩]
  have hAd_eq : ∀ k, (hk : k < I.jobs) → (σ1.arrs "A").getD (2 * I.jobs + k) 0 = I.d ⟨k, hk⟩ :=
    fun k hk => by
      have h1 := hA1d k (hjcIdx k hk)
      rw [hjc] at h1
      rw [h1, hde ⟨k, hk⟩]
  have hAw_eq : ∀ k, (hk : k < I.jobs) → (σ1.arrs "A").getD (3 * I.jobs + k) 0 = I.w ⟨k, hk⟩ :=
    fun k hk => by
      have h1 := hA1w k (hjcIdx k hk)
      rw [hjc] at h1
      rw [h1, hwe ⟨k, hk⟩]
  -- Step 2: `.read "W"`.
  have hinpW : σ1.inp = [W] := by
    rw [hinp1, hjc, show (2 + 4 * I.jobs) = y.length from hEnc.length_eq.symm]; simp
  have r2 := Run.read (B := B) (σ := σ1) (x := "W") (v := W) (rest := []) hinpW
  set σ2 : Env := { σ1.setVar "W" W with inp := [] } with hσ2
  clear_value σ2
  have hn2 : σ2.vars "n" = I.jobs := by rw [hσ2]; simp [Env.setVar, hn1']
  have hArrs2 : σ2.arrs = σ1.arrs := by rw [hσ2]; simp [Env.setVar]
  have hA2 : σ2.arrs "A" = σ1.arrs "A" := by rw [hσ2]; simp [Env.setVar]
  have hSA2 : (σ2.arrs "SA").length = I.jobs := by rw [hσ2]; exact hSA1
  have hSB2 : (σ2.arrs "SB").length = I.jobs := by rw [hσ2]; exact hSB1
  have hW2 : σ2.vars "W" = W := by rw [hσ2]; simp [Env.setVar]
  have hout2 : σ2.out = [] := by rw [hσ2]; simp [Env.setVar, hout1]
  have hinp2 : σ2.inp = [] := by rw [hσ2]
  -- Step 3: `.assign "en" (V "n")`.
  have hnB2 : σ2.vars "n" < B := by rw [hn2]; exact hIjB
  have hvn2 : (V "n").evalB B σ2 = some I.jobs := by
    have he := evalB_var (B := B) (σ := σ2) (x := "n") hnB2
    rw [he, hn2]
  have r3 := Run.assign (B := B) (σ := σ2) (x := "en") (e := V "n") (v := I.jobs) hvn2
  set σ3 : Env := σ2.setVar "en" I.jobs with hσ3
  clear_value σ3
  have hn3 : σ3.vars "n" = I.jobs := by rw [hσ3]; simp [Env.setVar, hn2]
  have hen3 : σ3.vars "en" = I.jobs := by rw [hσ3]; simp [Env.setVar]
  have hArrs3 : σ3.arrs = σ2.arrs := by rw [hσ3]; simp [Env.setVar]
  have hA3 : σ3.arrs "A" = σ1.arrs "A" := by rw [hσ3]; exact hA2
  have hSA3 : (σ3.arrs "SA").length = I.jobs := by rw [hσ3]; exact hSA2
  have hSB3 : (σ3.arrs "SB").length = I.jobs := by rw [hσ3]; exact hSB2
  have hW3 : σ3.vars "W" = W := by rw [hσ3]; simp [Env.setVar, hW2]
  have hout3 : σ3.out = [] := by rw [hσ3]; simp [Env.setVar, hout2]
  have hinp3 : σ3.inp = [] := by rw [hσ3]; simp [Env.setVar, hinp2]
  -- Step 4: `.assign "sn" (V "n")`.
  have hnB3 : σ3.vars "n" < B := by rw [hn3]; exact hIjB
  have hvn3 : (V "n").evalB B σ3 = some I.jobs := by
    have he := evalB_var (B := B) (σ := σ3) (x := "n") hnB3
    rw [he, hn3]
  have r4 := Run.assign (B := B) (σ := σ3) (x := "sn") (e := V "n") (v := I.jobs) hvn3
  set σ4 : Env := σ3.setVar "sn" I.jobs with hσ4
  clear_value σ4
  have hen4 : σ4.vars "en" = I.jobs := by rw [hσ4]; simp [Env.setVar, hen3]
  have hsn4 : σ4.vars "sn" = I.jobs := by rw [hσ4]; simp [Env.setVar]
  have hArrs4 : σ4.arrs = σ3.arrs := by rw [hσ4]; simp [Env.setVar]
  have hA4 : σ4.arrs "A" = σ1.arrs "A" := by rw [hσ4]; exact hA3
  have hSA4 : (σ4.arrs "SA").length = I.jobs := by rw [hσ4]; exact hSA3
  have hSB4 : (σ4.arrs "SB").length = I.jobs := by rw [hσ4]; exact hSB3
  have hPS4l : (σ4.arrs "PS").length = I.jobs := by rw [hArrs4, hArrs3, hArrs2]; exact hPS1
  have hQS4l : (σ4.arrs "QS").length = I.jobs := by rw [hArrs4, hArrs3, hArrs2]; exact hQS1
  have hDS4l : (σ4.arrs "DS").length = I.jobs := by rw [hArrs4, hArrs3, hArrs2]; exact hDS1
  have hNX4l : (σ4.arrs "NX").length = I.jobs := by rw [hArrs4, hArrs3, hArrs2]; exact hNX1
  have hCC4l : (σ4.arrs "CC").length = I.jobs + 1 := by rw [hArrs4, hArrs3, hArrs2]; exact hCC1
  have hPC4l : (σ4.arrs "PC").length = I.jobs + 1 := by rw [hArrs4, hArrs3, hArrs2]; exact hPC1
  have hW4 : σ4.vars "W" = W := by rw [hσ4]; simp [Env.setVar, hW3]
  have hout4 : σ4.out = [] := by rw [hσ4]; simp [Env.setVar, hout3]
  have hinp4 : σ4.inp = [] := by rw [hσ4]; simp [Env.setVar, hinp3]
  -- Step 5: `estSortCom`.
  have hA0len : (σ1.arrs "A").length = 4 * I.jobs := by rw [hAl1, hjc]
  have hA0B : ∀ v ∈ σ1.arrs "A", v < B := by
    apply hgetD_mem_bound (σ1.arrs "A") (4 * I.jobs) ?_ hA0len
    intro k hk
    rcases hsplit4 k hk with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hAp_eq k h1]; exact hpB ⟨k, h1⟩
    · have hk' := hsub1 k h1 h2
      rw [heq1 k h1, hAq_eq (k - I.jobs) hk']; exact hqB ⟨k - I.jobs, hk'⟩
    · have hk' := hsub2 k h1 h2
      rw [heq2 k h1, hAd_eq (k - 2 * I.jobs) hk']; exact hdB ⟨k - 2 * I.jobs, hk'⟩
    · have hk' := hsub3 k h1 h2
      rw [heq3 k h1, hAw_eq (k - 3 * I.jobs) hk']; exact hwB ⟨k - 3 * I.jobs, hk'⟩
  have hsum1 : ∀ a b, a < I.jobs → b < I.jobs →
      dA (σ1.arrs "A") I.jobs a + qA (σ1.arrs "A") I.jobs b < B := fun a b ha hb => by
    show (σ1.arrs "A").getD (2 * I.jobs + a) 0 + (σ1.arrs "A").getD (I.jobs + b) 0 < B
    rw [hAd_eq a ha, hAq_eq b hb]
    exact hdq ⟨a, ha⟩ ⟨b, hb⟩
  obtain ⟨σ5, hr5, ⟨⟨hA5, hen5⟩, hSAperm5, hSAsorted5⟩, hfv5, hfa5, hinpImp5, houtImp5⟩ :=
    (estSort_spec hB1 (σ1.arrs "A") I.jobs hA0len hA0B h3B3 hsum1).frame.run (σ := σ4)
      ⟨⟨hA4, hen4⟩, hSA4, hSB4, hsn4⟩
  have hW5 : σ5.vars "W" = W := by rw [hfv5 "W" (by decide)]; exact hW4
  have hinp5 : σ5.inp = [] := by rw [hinpImp5 (by decide)]; exact hinp4
  have hout5 : σ5.out = [] := by rw [houtImp5 (by decide)]; exact hout4
  have hSAlen5 : (σ5.arrs "SA").length = I.jobs := by
    have := hSAperm5.length_eq; simpa using this
  have hSAbound5 : ∀ k, k < I.jobs → (σ5.arrs "SA").getD k 0 < I.jobs := fun k hk => by
    have hkP : k < (σ5.arrs "SA").length := by rw [hSAlen5]; exact hk
    have hmem : (σ5.arrs "SA").getD k 0 ∈ σ5.arrs "SA" := by
      rw [List.getD_eq_getElem _ _ hkP]; exact List.getElem_mem hkP
    have hr := hSAperm5.mem_iff.mp hmem
    simpa using hr
  have hsn5 : σ5.vars "sn" = I.jobs := by rw [hfv5 "sn" (by decide)]; exact hsn4
  have hPS5l : (σ5.arrs "PS").length = I.jobs := by rw [hfa5 "PS" (by decide)]; exact hPS4l
  have hQS5l : (σ5.arrs "QS").length = I.jobs := by rw [hfa5 "QS" (by decide)]; exact hQS4l
  have hDS5l : (σ5.arrs "DS").length = I.jobs := by rw [hfa5 "DS" (by decide)]; exact hDS4l
  have hNX5l : (σ5.arrs "NX").length = I.jobs := by rw [hfa5 "NX" (by decide)]; exact hNX4l
  have hCC5l : (σ5.arrs "CC").length = I.jobs + 1 := by rw [hfa5 "CC" (by decide)]; exact hCC4l
  have hPC5l : (σ5.arrs "PC").length = I.jobs + 1 := by rw [hfa5 "PC" (by decide)]; exact hPC4l
  have hAlen6 : 3 * I.jobs + I.jobs ≤ (σ1.arrs "A").length := by rw [hA0len, h3n4n]
  obtain ⟨σ6, hr6, ⟨hPS6, hQS6, hDS6, hSA6, hA6, hsn6⟩, hfv6, hfa6, hinpImp6, houtImp6⟩ :=
    (buildSorted_spec hB1 (σ1.arrs "A") (σ5.arrs "SA") (σ5.arrs "PS") (σ5.arrs "QS")
      (σ5.arrs "DS") I.jobs hSAlen5 hSAbound5 hAlen6 hA0B h4B3 hPS5l hQS5l hDS5l).frame.run
      (σ := σ5) ⟨rfl, hA5, hsn5, rfl, rfl, rfl⟩
  have hW6 : σ6.vars "W" = W := by rw [hfv6 "W" (by decide)]; exact hW5
  have hinp6 : σ6.inp = [] := by rw [hinpImp6 (by decide)]; exact hinp5
  have hout6 : σ6.out = [] := by rw [houtImp6 (by decide)]; exact hout5
  have hNX6l : (σ6.arrs "NX").length = I.jobs := by rw [hfa6 "NX" (by decide)]; exact hNX5l
  have hCC6l : (σ6.arrs "CC").length = I.jobs + 1 := by rw [hfa6 "CC" (by decide)]; exact hCC5l
  have hPC6l : (σ6.arrs "PC").length = I.jobs + 1 := by rw [hfa6 "PC" (by decide)]; exact hPC5l
  -- The sorted instance `J`, and the sorted arrays as `pv`/`qv`/`dv` of `J`.
  have hA1p' : ∀ j, j < I.jobs → (σ1.arrs "A").getD j 0 = preTime (y ++ [W]) j := fun j hj =>
    hA1p j (hjcIdx j hj)
  have hA1q' : ∀ j, j < I.jobs → (σ1.arrs "A").getD (I.jobs + j) 0 = procTime (y ++ [W]) j :=
    fun j hj => by have h1 := hA1q j (hjcIdx j hj); rw [hjc] at h1; exact h1
  have hA1d' : ∀ j, j < I.jobs → (σ1.arrs "A").getD (2 * I.jobs + j) 0 = due (y ++ [W]) j :=
    fun j hj => by have h1 := hA1d j (hjcIdx j hj); rw [hjc] at h1; exact h1
  obtain ⟨hPSraw, hQSraw, hDSraw⟩ :=
    buildSorted_arrays_eq I.jobs hA1p' hA1q' hA1d' (σ5.arrs "SA") hSAbound5
  obtain ⟨hEstOrd, hHW⟩ :=
    est_sorted_instance I (σ1.arrs "A") hAd_eq hAq_eq (σ5.arrs "SA") hSAperm5 hSAsorted5
  set J : Instance := permute I (listEquiv I.jobs (σ5.arrs "SA") hSAperm5) with hJdef
  obtain ⟨hPSeq, hQSeq, hDSeq⟩ := sortedArrays_eq hpe hqe hde (σ5.arrs "SA") hSAperm5 I.jobs rfl
  have hPSfin : σ6.arrs "PS" = (List.range I.jobs).map (fun k => pv J k) := by
    rw [hPS6, hPSraw]
    exact hmap_ext I.jobs _ _ (fun k hk => (hmap_range_getD _ I.jobs k hk).symm.trans (hPSeq k hk))
  have hQSfin : σ6.arrs "QS" = (List.range I.jobs).map (fun k => qv J k) := by
    rw [hQS6, hQSraw]
    exact hmap_ext I.jobs _ _ (fun k hk => (hmap_range_getD _ I.jobs k hk).symm.trans (hQSeq k hk))
  have hDSfin : σ6.arrs "DS" = (List.range I.jobs).map (fun k => dv J k) := by
    rw [hDS6, hDSraw]
    exact hmap_ext I.jobs _ _ (fun k hk => (hmap_range_getD _ I.jobs k hk).symm.trans (hDSeq k hk))
  refine ⟨σ6, Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 500 * I.jobs + 1000,
    (hr1.seq (r2.seq (r3.seq (r4.seq (hr5.seq hr6))))).mono ?_, le_rfl,
    J, hEstOrd, rfl, hm1, fun j => hw1 (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 j),
    fun j => hqpos (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 j),
    fun j => hpqB (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 j),
    fun a b => hdq (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 a)
      (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 b),
    fun j => hd2B (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 j),
    hHW, hPSfin, hQSfin, hDSfin, hsn6, hW6, hinp6, hout6, hNX6l, hCC6l, hPC6l⟩
  rw [hcost1]
  exact hKbound _ _ _ _ _ _ rfl rfl hcost34 hcost34 rfl rfl

/-! ## The sentinel, the table, and the answer -/

/-- Every entry of a list is at most its `foldr max`. -/
theorem le_foldr_max (l : List ℕ) (v : ℕ) (hv : v ∈ l) : v ≤ l.foldr max 0 := by
  induction l with
  | nil => cases hv
  | cons a t ih =>
    rcases List.mem_cons.mp hv with rfl | hv'
    · simp only [List.foldr_cons]; omega
    · simp only [List.foldr_cons]; exact le_trans (ih hv') (le_max_right _ _)

/-- What `Nxt1.Res D Q n j n res` says about `res`, without the arrays: `res` is strictly
after `j` and at most `n`, in either branch of the disjunction. -/
theorem Res_bounds (D Q : List ℕ) (n j res : ℕ) (hj : j < n) (hR : Res D Q n j n res) :
    j < res ∧ res ≤ n := by
  rcases hR with ⟨he, _⟩ | ⟨hlt, hjlt, hnylt, _, _⟩
  · omega
  · omega

/-- No step changes any array's length — `store` only overwrites an entry, never resizes. -/
theorem bigStepB_arrs_length_eq {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) : ∀ a, (σ'.arrs a).length = (σ.arrs a).length := by
  induction h with
  | skip => intro a; rfl
  | assign _ => intro a; rfl
  | store _ _ _ => intro a; simp only [Env.setArr]; split <;> simp_all
  | seq _ _ ih1 ih2 => intro a; rw [ih2 a, ih1 a]
  | ite_true _ _ ih => intro a; exact ih a
  | ite_false _ _ ih => intro a; exact ih a
  | while_true _ _ _ ih1 ih2 => intro a; rw [ih2 a, ih1 a]
  | while_false _ => intro a; rfl
  | read _ => intro a; rfl
  | write _ => intro a; rfl

theorem run_arrs_length_eq {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) :
    ∀ a, (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨k, -, hbs⟩ := h
  exact bigStepB_arrs_length_eq hbs

theorem int_succ_lt (x : ℤ) : x + 1 < x + 2 := by linarith

set_option maxHeartbeats 4000000 in
open Classical in
/-- Find the sentinel, scan for `nxt`, fill in the table column by column, and write the
answer: `1` exactly when `J` (the est-sorted instance) has a feasible set of weight `W`. -/
theorem restOfProg_spec {J : Instance} (hEst : EstOrdered J) (hqpos : ∀ j : J.Job, 0 < J.q j)
    (hm1 : J.machines = 1) (hw1 : ∀ j : J.Job, J.w j = 1)
    {W B : ℕ} (hB2 : 2 < B) (hWB : W < B) (hnB : J.jobs + 5 < B)
    (hpqB : ∀ j : J.Job, (J.p j : ℕ) + J.q j < B) (hdqB : ∀ a b : J.Job, (J.d a : ℕ) + J.q b < B)
    (hd2B : ∀ j : J.Job, (J.d j : ℕ) + 2 < B) :
    Spec B
      (fun σ => σ.arrs "PS" = (List.range J.jobs).map (pv J) ∧
        σ.arrs "QS" = (List.range J.jobs).map (qv J) ∧
        σ.arrs "DS" = (List.range J.jobs).map (dv J) ∧ σ.vars "sn" = J.jobs ∧ σ.vars "W" = W ∧
        σ.inp = [] ∧ σ.out = [] ∧ (σ.arrs "NX").length = J.jobs ∧
        (σ.arrs "CC").length = J.jobs + 1 ∧ (σ.arrs "PC").length = J.jobs + 1)
      (.seq maxScan (.seq nxtLoop (.seq initRest (.seq colsLoop (.write (V "ans"))))))
      (fun _ σ' => σ'.out = if HasWeight J W then [1] else [0])
      (500 * (J.jobs + 1) * (J.jobs + 1) + 5000) := by
  have hn1B : J.jobs + 1 < B := by omega
  have hn2B : J.jobs + 2 < B := by omega
  have hB1 : 1 < B := by omega
  have hPSlen : ((List.range J.jobs).map (pv J)).length = J.jobs := by
    rw [List.length_map, List.length_range]
  have hQSlen : ((List.range J.jobs).map (qv J)).length = J.jobs := by
    rw [List.length_map, List.length_range]
  have hDSlen : ((List.range J.jobs).map (dv J)).length = J.jobs := by
    rw [List.length_map, List.length_range]
  have hPS_getD : ∀ k, k < J.jobs → ((List.range J.jobs).map (pv J)).getD k 0 = pv J k :=
    fun k hk => by rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  have hQS_getD : ∀ k, k < J.jobs → ((List.range J.jobs).map (qv J)).getD k 0 = qv J k :=
    fun k hk => by rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  have hDS_getD : ∀ k, k < J.jobs → ((List.range J.jobs).map (dv J)).getD k 0 = dv J k :=
    fun k hk => by rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
  have hpv_eq : ∀ k, (hk : k < J.jobs) → pv J k = J.p ⟨k, hk⟩ := fun k hk => dif_pos hk
  have hqv_eq : ∀ k, (hk : k < J.jobs) → qv J k = J.q ⟨k, hk⟩ := fun k hk => dif_pos hk
  have hdv_eq : ∀ k, (hk : k < J.jobs) → dv J k = J.d ⟨k, hk⟩ := fun k hk => dif_pos hk
  have hDSB2 : ∀ v ∈ (List.range J.jobs).map (dv J), v + 2 < B := by
    intro v hv
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
    have hk' : k < J.jobs := by rw [← hDSlen]; exact hk
    rw [← hkv, ← List.getD_eq_getElem _ _ hk, hDS_getD k hk', hdv_eq k hk']
    exact hd2B ⟨k, hk'⟩
  have hDSB : ∀ v ∈ (List.range J.jobs).map (dv J), v < B := fun v hv =>
    lt_of_le_of_lt (Nat.le_add_right v 2) (hDSB2 v hv)
  have hQSB : ∀ v ∈ (List.range J.jobs).map (qv J), v < B := by
    intro v hv
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
    have hk' : k < J.jobs := by rw [← hQSlen]; exact hk
    rw [← hkv, ← List.getD_eq_getElem _ _ hk, hQS_getD k hk', hqv_eq k hk']
    exact lt_of_le_of_lt (Nat.le_add_left _ _) (hpqB ⟨k, hk'⟩)
  have hsumDQ : ∀ a b, a < J.jobs → b < J.jobs →
      ((List.range J.jobs).map (dv J)).getD a 0 +
        ((List.range J.jobs).map (qv J)).getD b 0 < B := fun a b ha hb => by
    rw [hDS_getD a ha, hQS_getD b hb, hdv_eq a ha, hqv_eq b hb]
    exact hdqB ⟨a, ha⟩ ⟨b, hb⟩
  have hsumPQ : ∀ j, j < J.jobs → ((List.range J.jobs).map (pv J)).getD j 0 +
      ((List.range J.jobs).map (qv J)).getD j 0 < B := fun j hj => by
    rw [hPS_getD j hj, hQS_getD j hj, hpv_eq j hj, hqv_eq j hj]
    exact hpqB ⟨j, hj⟩
  have hcostWrite : 1 + Expr.size (V "ans") ≤ 3 := by decide
  have hKbound2 : ∀ K1 K2 K3 K4 K5 : ℕ,
      K1 = 2 + (2 + ((50 + 4) * J.jobs + 6) + 4 + 4) →
      K2 = 2 + ((Nxt1.nxtBodyCost J.jobs + 4) * J.jobs + 6) →
      K3 = 8 + (30 + ((20 + 4) * (J.jobs + 1) + 6)) →
      K4 = Cols1.colsCost J.jobs → K5 ≤ 3 →
      K1 + (K2 + (K3 + (K4 + K5))) ≤ 500 * (J.jobs + 1) * (J.jobs + 1) + 5000 := by
    intro K1 K2 K3 K4 K5 h1 h2 h3 h4 h5
    unfold Nxt1.nxtBodyCost at h2
    unfold Cols1.colsCost at h4
    have hJ1 : J.jobs ≤ J.jobs + 1 := Nat.le_succ _
    nlinarith [Nat.mul_le_mul hJ1 hJ1, sq_nonneg J.jobs]
  refine Spec.of_exists fun σA ⟨hPS0, hQS0, hDS0, hsn0, hW0, hinp0, hout0, hNX0l, hCC0l,
      hPC0l⟩ => ?_
  -- Step 7: `maxScan`.
  obtain ⟨σB, hrB, ⟨hcinfB, hDSB', hsnB⟩, hfvB, hfaB, hinpImpB, houtImpB⟩ :=
    (maxScan_spec hB1 ((List.range J.jobs).map (dv J)) J.jobs hDSlen hDSB2 hn2B).frame.run
      (σ := σA) ⟨hDS0, hsn0⟩
  set M : ℕ := ((List.range J.jobs).map (dv J)).foldr max 0 with hMdef
  set inf : ℕ := M + 2 with hinfdef
  have hPSB : σB.arrs "PS" = (List.range J.jobs).map (pv J) := by
    rw [hfaB "PS" (by decide)]; exact hPS0
  have hQSB2 : σB.arrs "QS" = (List.range J.jobs).map (qv J) := by
    rw [hfaB "QS" (by decide)]; exact hQS0
  have hWB' : σB.vars "W" = W := by rw [hfvB "W" (by decide)]; exact hW0
  have hinpB : σB.inp = [] := by rw [hinpImpB (by decide)]; exact hinp0
  have houtB : σB.out = [] := by rw [houtImpB (by decide)]; exact hout0
  have hNXBl : (σB.arrs "NX").length = J.jobs := by rw [hfaB "NX" (by decide)]; exact hNX0l
  have hCCBl : (σB.arrs "CC").length = J.jobs + 1 := by rw [hfaB "CC" (by decide)]; exact hCC0l
  have hPCBl : (σB.arrs "PC").length = J.jobs + 1 := by rw [hfaB "PC" (by decide)]; exact hPC0l
  have hinfB : inf < B :=
    Lax496464Proofs.Ram.Corollary1Init.foldr_max_lt hDSB2 hB2
  -- Step 8: `nxtLoop`.
  obtain ⟨σC, hrC, ⟨hDSC, hQSC, hsnC, hResC⟩, hfvC, hfaC, hinpImpC, houtImpC⟩ :=
    (nxtLoop_spec hB1 ((List.range J.jobs).map (dv J)) ((List.range J.jobs).map (qv J))
      J.jobs hDSlen hQSlen hDSB hQSB hsumDQ hn1B).frame.run (σ := σB) ⟨hDSB', hQSB2, hsnB, hNXBl⟩
  have hPSC : σC.arrs "PS" = (List.range J.jobs).map (pv J) := by
    rw [hfaC "PS" (by decide)]; exact hPSB
  have hcinfC : σC.vars "cinf" = inf := by rw [hfvC "cinf" (by decide)]; exact hcinfB
  have hWC : σC.vars "W" = W := by rw [hfvC "W" (by decide)]; exact hWB'
  have hinpC : σC.inp = [] := by rw [hinpImpC (by decide)]; exact hinpB
  have houtC : σC.out = [] := by rw [houtImpC (by decide)]; exact houtB
  have hCCCl : (σC.arrs "CC").length = J.jobs + 1 := by rw [hfaC "CC" (by decide)]; exact hCCBl
  have hPCCl : (σC.arrs "PC").length = J.jobs + 1 := by rw [hfaC "PC" (by decide)]; exact hPCBl
  -- Step 9: `initRest`.
  obtain ⟨σD, hrD, ⟨hsn1D, hansD01, hansDW, hPCD, hsnD, hcinfD⟩, hfvD, hfaD, hinpImpD, houtImpD⟩ :=
    (initRest_spec hB1 J.jobs W inf hn2B hWB hinfB).frame.run (σ := σC)
      ⟨hsnC, hWC, hcinfC, hPCCl⟩
  have hNXCl : (σC.arrs "NX").length = J.jobs := by
    rw [run_arrs_length_eq hrC "NX"]; exact hNXBl
  have hNXDl : (σD.arrs "NX").length = J.jobs := by
    rw [hfaD "NX" (by decide)]; exact hNXCl
  have hPSD : σD.arrs "PS" = (List.range J.jobs).map (pv J) := by
    rw [hfaD "PS" (by decide)]; exact hPSC
  have hQSD : σD.arrs "QS" = (List.range J.jobs).map (qv J) := by
    rw [hfaD "QS" (by decide)]; exact hQSC
  have hDSD : σD.arrs "DS" = (List.range J.jobs).map (dv J) := by
    rw [hfaD "DS" (by decide)]; exact hDSC
  have hCCDl : (σD.arrs "CC").length = J.jobs + 1 := by rw [hfaD "CC" (by decide)]; exact hCCCl
  have hWD : σD.vars "W" = W := by rw [hfvD "W" (by decide)]; exact hWC
  have hinpD : σD.inp = [] := by rw [hinpImpD (by decide)]; exact hinpC
  have houtD : σD.out = [] := by rw [houtImpD (by decide)]; exact houtC
  -- The table's data, at `σD`.
  have hResD' : ∀ j, j < J.jobs → Res (σD.arrs "DS") (σD.arrs "QS") J.jobs j J.jobs
      ((σD.arrs "NX").getD j 0) := fun j hj => by
    rw [hDSD, hQSD, hfaD "NX" (by decide)]; exact hResC j hj
  have hDatNxt : ∀ j, j < J.jobs →
      j < (σD.arrs "NX").getD j 0 ∧ (σD.arrs "NX").getD j 0 ≤ J.jobs :=
    fun j hj => Res_bounds _ _ _ _ _ hj (hResD' j hj)
  have hDatbP : ∀ j, j < J.jobs → (σD.arrs "PS").getD j 0 < B := fun j hj => by
    rw [hPSD, hPS_getD j hj, hpv_eq j hj]
    exact lt_of_le_of_lt (Nat.le_add_right _ _) (hpqB ⟨j, hj⟩)
  have hDatbQ : ∀ j, j < J.jobs → (σD.arrs "QS").getD j 0 < B := fun j hj => by
    rw [hQSD, hQS_getD j hj, hqv_eq j hj]
    exact lt_of_le_of_lt (Nat.le_add_left _ _) (hpqB ⟨j, hj⟩)
  have hDatbD : ∀ j, j < J.jobs → (σD.arrs "DS").getD j 0 < B := fun j hj => by
    rw [hDSD, hDS_getD j hj, hdv_eq j hj]
    exact lt_of_le_of_lt (Nat.le_add_right _ 2) (hd2B ⟨j, hj⟩)
  have hDatSum : ∀ j, j < J.jobs → (σD.arrs "PS").getD j 0 + (σD.arrs "QS").getD j 0 < B :=
    fun j hj => by rw [hPSD, hQSD]; exact hsumPQ j hj
  have hDSmem : ∀ k, k < J.jobs →
      ((List.range J.jobs).map (dv J)).getD k 0 ∈ (List.range J.jobs).map (dv J) := fun k hk => by
    rw [List.getD_eq_getElem _ _ (by rw [hDSlen]; exact hk)]
    exact List.getElem_mem (by rw [hDSlen]; exact hk)
  have hDSle : ∀ k, k < J.jobs → ((List.range J.jobs).map (dv J)).getD k 0 ≤
      M := fun k hk => le_foldr_max _ _ (hDSmem k hk)
  have hDatInfd : ∀ j, j < J.jobs → (σD.arrs "DS").getD j 0 + 1 < inf := fun j hj => by
    rw [hDSD, hinfdef]
    exact lt_of_le_of_lt (Nat.add_le_add_right (hDSle j hj) 1) (Nat.lt_succ_self _)
  have hDatbC : ∀ t, t ≤ J.jobs → (σD.arrs "PC").getD t 0 ≤ inf := fun t ht => by
    rw [hPCD, List.getD_replicate _ (Nat.lt_succ_of_le ht)]
  have hinf1 : 1 < inf := by
    rw [hinfdef]; exact lt_of_lt_of_le (by decide) (Nat.le_add_left 2 _)
  have hDat : Dat B inf J.jobs (σD.arrs "NX") (σD.arrs "PS") (σD.arrs "QS") (σD.arrs "DS")
      (σD.arrs "PC") :=
    { lenP := by rw [hPSD, hPSlen]
      lenQ := by rw [hQSD, hQSlen]
      lenD := by rw [hDSD, hDSlen]
      lenN := hNXDl
      lenC := by rw [hPCD]; exact List.length_replicate
      nxt := hDatNxt
      bP := hDatbP
      bQ := hDatbQ
      bD := hDatbD
      sum := hDatSum
      infd := hDatInfd
      bC := hDatbC
      infB := hinfB
      two := hB2
      nB := hn1B }
  -- Step 10: `colsLoop`.
  obtain ⟨σE, hrE, ⟨hwcE, hansE01, hansEiff⟩, hfvE, hfaE, hinpImpE, houtImpE⟩ :=
    (colsLoop_spec hDat hWB hinf1).frame.run (σ := σD)
      ⟨rfl, rfl, rfl, rfl, hsnD, hsn1D, hcinfD, hWD, hCCDl, hPCD, hansD01, hansDW⟩
  have houtE : σE.out = [] := by rw [houtImpE (by decide)]; exact houtD
  -- The mathematical bridge: `ans = 1 ↔ HasWeight J W`.
  have hdJ_le : ∀ j : J.Job, (J.d j : ℕ) ≤ M :=
    fun j => by
      have h1 := hDSle (j : ℕ) j.isLt
      rwa [hDS_getD (j : ℕ) j.isLt, hdv_eq (j : ℕ) j.isLt] at h1
  have hinfd_J : ∀ j : J.Job, s j + 1 < (inf : ℤ) := fun j => by
    have h1 : s j ≤ (J.d j : ℤ) := sub_le_self _ (Int.natCast_nonneg _)
    have h2 : (J.d j : ℤ) ≤ (M : ℤ) :=
      Nat.cast_le.mpr (hdJ_le j)
    have h3 : (M : ℤ) + 1 < (inf : ℤ) := by
      have h4 : (inf : ℤ) = (M : ℤ) + 2 := by
        rw [hinfdef, Nat.cast_add]; norm_num
      rw [h4]; exact int_succ_lt _
    exact lt_of_le_of_lt (add_le_add (le_trans h1 h2) (le_refl (1 : ℤ))) h3
  have hIsNxt : ∀ j (hj : j < J.jobs), IsNxt j hj ((σD.arrs "NX").getD j 0) := fun j hj =>
    res_isNxt hEst hqpos hj (σD.arrs "DS") (σD.arrs "QS")
      (fun x hx => by rw [hDSD]; exact hDS_getD x hx)
      (fun x hx => by rw [hQSD]; exact hQS_getD x hx) (hResD' j hj)
  have hPSfun : (fun j => (σD.arrs "PS").getD j 0) = pv J := by
    funext j
    by_cases hj : j < J.jobs
    · rw [hPSD, hPS_getD j hj, hpv_eq j hj]
    · rw [hPSD, List.getD_eq_default _ _ (by rw [hPSlen]; exact not_lt.mp hj)]
      unfold pv; rw [dif_neg hj]
  have hQSfun : (fun j => (σD.arrs "QS").getD j 0) = qv J := by
    funext j
    by_cases hj : j < J.jobs
    · rw [hQSD, hQS_getD j hj, hqv_eq j hj]
    · rw [hQSD, List.getD_eq_default _ _ (by rw [hQSlen]; exact not_lt.mp hj)]
      unfold qv; rw [dif_neg hj]
  have hDSfun : (fun j => (σD.arrs "DS").getD j 0) = dv J := by
    funext j
    by_cases hj : j < J.jobs
    · rw [hDSD, hDS_getD j hj, hdv_eq j hj]
    · rw [hDSD, List.getD_eq_default _ _ (by rw [hDSlen]; exact not_lt.mp hj)]
      unfold dv; rw [dif_neg hj]
  have hCA_eq : ∀ W' j, CA J.jobs inf (σD.arrs "NX") (σD.arrs "PS") (σD.arrs "QS")
      (σD.arrs "DS") W' j =
      colAll J.jobs inf (fun j => (σD.arrs "NX").getD j 0) (pv J) (qv J) (dv J) W' j := by
    intro W' j
    show colAll J.jobs inf (fun j => (σD.arrs "NX").getD j 0)
      (fun j => (σD.arrs "PS").getD j 0) (fun j => (σD.arrs "QS").getD j 0)
      (fun j => (σD.arrs "DS").getD j 0) W' j = _
    rw [hPSfun, hQSfun, hDSfun]
  have hdpKeq : ∀ W', dpK J inf (fun j => (σD.arrs "NX").getD j 0) J.jobs 0 W' =
      CA J.jobs inf (σD.arrs "NX") (σD.arrs "PS") (σD.arrs "QS") (σD.arrs "DS") W' 0 := by
    intro W'
    rw [hCA_eq]
    exact dpK_eq_colAll (fun j => (σD.arrs "NX").getD j 0) inf
      (fun j hj => (hDatNxt j hj).1) J.jobs W' 0 (le_of_eq (Nat.zero_add J.jobs).symm)
  have hansIff : σE.vars "ans" = 1 ↔ HasWeight J W := by
    rw [hansEiff,
      hasWeight_iff_dp hEst hqpos hw1 hm1 inf hinf1 hinfd_J
        (fun j => (σD.arrs "NX").getD j 0) hIsNxt W]
    constructor
    · rintro ⟨W'', h1, h2, h3⟩; exact ⟨W'', h1, h2, by rw [hdpKeq]; exact h3⟩
    · rintro ⟨W'', h1, h2, h3⟩; exact ⟨W'', h1, h2, by rw [← hdpKeq]; exact h3⟩
  have hansVal : σE.vars "ans" = if HasWeight J W then 1 else 0 := by
    rcases hansE01 with h1 | h0
    · rw [h1, if_pos (hansIff.mp h1)]
    · rw [h0, if_neg]
      intro hHW
      have h1 := hansIff.mpr hHW
      rw [h0] at h1
      exact absurd h1 (by decide)
  -- Step 11: `.write (V "ans")`.
  have hvansE : (V "ans").evalB B σE = some (σE.vars "ans") := by
    refine evalB_var (B := B) (σ := σE) (x := "ans") ?_
    rw [hansVal]; split <;> exact hB2.trans_le' (by decide)
  have hrF := Run.write (B := B) (σ := σE) (e := V "ans") (v := σE.vars "ans") hvansE
  refine ⟨{ σE with out := σE.out ++ [σE.vars "ans"] },
    500 * (J.jobs + 1) * (J.jobs + 1) + 5000,
    (hrB.seq (hrC.seq (hrD.seq (hrE.seq hrF)))).mono ?_, le_rfl, ?_⟩
  · exact hKbound2 _ _ _ _ _ rfl rfl rfl rfl hcostWrite
  · show σE.out ++ [σE.vars "ans"] = if HasWeight J W then [1] else [0]
    rw [houtE, hansVal]
    split <;> rfl

/-! ## The whole program -/

/-- Glue `sortSetup_spec`'s `Run` (over `.seq readInstance (.seq … (.seq estSortCom
buildSorted))`, a self-contained subtree) to `restOfProg_spec`'s `Run` (over
`.seq maxScan (…)`) into a `Run` of `prog` itself: `prog`'s own `.seq` nesting attaches
`buildSorted` directly to `maxScan`, not to a whole bundled first half, so the two `Run`s
can't just be `.seq`-composed — the underlying `BigStepB` derivation has to be taken apart
and put back together in `prog`'s exact shape. -/
theorem run_prog_of_parts {B : ℕ} {σA σ6 σF : Env} {K1 K2 : ℕ}
    (h1 : Run B (.seq readInstance (.seq (.read "W") (.seq (.assign "en" (V "n"))
      (.seq (.assign "sn" (V "n")) (.seq estSortCom buildSorted))))) σA σ6 K1)
    (h2 : Run B (.seq maxScan (.seq nxtLoop (.seq initRest (.seq colsLoop (.write (V "ans"))))))
      σ6 σF K2) :
    Run B prog σA σF (K1 + K2) := by
  obtain ⟨k1, hk1, hbs1⟩ := h1
  obtain ⟨k2, hk2, hbs2⟩ := h2
  cases hbs1 with
  | seq hRI hbs1' =>
    cases hbs1' with
    | seq hRW hbs1'' =>
      cases hbs1'' with
      | seq hAE hbs1''' =>
        cases hbs1''' with
        | seq hAS hbs1'''' =>
          cases hbs1'''' with
          | seq hES hBS =>
            refine ⟨_, ?_, BigStepB.seq hRI (BigStepB.seq hRW (BigStepB.seq hAE (BigStepB.seq hAS
              (BigStepB.seq hES (BigStepB.seq hBS hbs2)))))⟩
            omega

open Lax496464Proofs.Ram.Reduction (encodesDecisionInstance_unique)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The whole program, correct.** `prog` decides `Yes x` for a decision word `x` of an
instance with one machine, unit weights and positive processing times. -/
theorem prog_spec {x : List ℕ} {I : Instance} {W : ℕ} (hdec : EncodesDecisionInstance x I W)
    (hm1 : I.machines = 1) (hw1 : ∀ j : I.Job, I.w j = 1) (hqpos : ∀ j : I.Job, 0 < I.q j)
    {B : ℕ} (hB2 : 2 < B) (hxB : ∀ v ∈ x, v < B) (hnB : 4 * I.jobs + 5 < B)
    (hpqB : ∀ j : I.Job, (I.p j : ℕ) + I.q j < B) (hdq : ∀ a b : I.Job, (I.d a : ℕ) + I.q b < B)
    (hd2B : ∀ j : I.Job, (I.d j : ℕ) + 2 < B) (hWB : W < B) :
    Spec B
      (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "NX").length = I.jobs ∧
        (σ.arrs "CC").length = I.jobs + 1 ∧ (σ.arrs "PC").length = I.jobs + 1)
      prog
      (fun _ σ' => σ'.out = if Yes x then [1] else [0])
      (Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 500 * I.jobs + 1000 +
        (500 * (I.jobs + 1) * (I.jobs + 1) + 5000)) := by
  have hn1BI : I.jobs + 5 < B := by omega
  have hYesIff : Yes x ↔ HasWeight I W := by
    constructor
    · rintro ⟨I', W', hdec', hHW'⟩
      obtain ⟨hI, hW⟩ := encodesDecisionInstance_unique hdec' hdec
      exact hI ▸ hW ▸ hHW'
    · intro hHW
      exact ⟨I, W, hdec, hHW⟩
  refine Spec.of_exists fun σ0 hP0 => ?_
  obtain ⟨σ6, hr6, hQ6⟩ :=
    (sortSetup_spec hdec hm1 hw1 hqpos hB2 hxB hnB hpqB hdq hd2B).run hP0
  obtain ⟨J, hEstJ, hJjobs, hJm1, hJw1, hJqpos, hJpqB, hJdqB, hJd2B, hHWJ, hPSJ, hQSJ, hDSJ,
    hsnJ, hWJ, hinpJ, houtJ, hNXJl, hCCJl, hPCJl⟩ := hQ6
  have hnBJ : J.jobs + 5 < B := by rw [hJjobs]; exact hn1BI
  have hPSJ' : σ6.arrs "PS" = (List.range J.jobs).map (pv J) := by rw [hJjobs]; exact hPSJ
  have hQSJ' : σ6.arrs "QS" = (List.range J.jobs).map (qv J) := by rw [hJjobs]; exact hQSJ
  have hDSJ' : σ6.arrs "DS" = (List.range J.jobs).map (dv J) := by rw [hJjobs]; exact hDSJ
  have hsnJ' : σ6.vars "sn" = J.jobs := by rw [hJjobs]; exact hsnJ
  have hNXJl' : (σ6.arrs "NX").length = J.jobs := by rw [hJjobs]; exact hNXJl
  have hCCJl' : (σ6.arrs "CC").length = J.jobs + 1 := by rw [hJjobs]; exact hCCJl
  have hPCJl' : (σ6.arrs "PC").length = J.jobs + 1 := by rw [hJjobs]; exact hPCJl
  obtain ⟨σF, hrF, hQF⟩ :=
    (restOfProg_spec hEstJ hJqpos hJm1 hJw1 hB2 hWB hnBJ hJpqB hJdqB hJd2B).run
      ⟨hPSJ', hQSJ', hDSJ', hsnJ', hWJ, hinpJ, houtJ, hNXJl', hCCJl', hPCJl'⟩
  have hK2eq : (500 * (J.jobs + 1) * (J.jobs + 1) + 5000 : ℕ) =
      500 * (I.jobs + 1) * (I.jobs + 1) + 5000 := by rw [hJjobs]
  refine ⟨σF, _, (run_prog_of_parts hr6 hrF).mono ?_, le_rfl, ?_⟩
  · rw [hK2eq]
  · rw [hQF, hYesIff, hHWJ]

/-! ## `Fits`/`ComputesInTime` -/

open Lax808846Proofs.Compile Lax808846Proofs.Transfer Lax808846.RamComputes
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const
  computesInTime_of_solves_fits)
open Lax496464.ParameterizedComplexity

/-- The arrays the program is given: their lengths are chosen by the word. -/
def ext1 (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "NX" then jobCount x
  else if a = "CC" ∨ a = "PC" then jobCount x + 1
  else 0

/-- Room for the sort, the table, and every intermediate sum. -/
def T1 (x : List ℕ) : ℕ := 4 * maxEntry x + 20

/-- The cost bound, as it comes out of `prog_spec`. -/
def progCost1 (x : List ℕ) : ℕ :=
  Lax496464Proofs.Ram.Sort.sortK 90 (jobCount x) + 500 * jobCount x + 1000 +
    (500 * (jobCount x + 1) * (jobCount x + 1) + 5000)

/-- Decision words of a one-machine, unit-weight instance with positive processing times,
that fit at word length `w` with constant `c`. -/
def Dom1 (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ DecisionInstances ∧ Fits c w x ∧ machineCount x = 1 ∧
    (∀ j < jobCount x, wt x j = 1) ∧ (∀ j < jobCount x, 0 < procTime x j)}

open Classical in
theorem prog_solves (cc w : ℕ) :
    Solves L1 prog (Dom1 cc w) (fun x => if Yes x then [1] else [0])
      (fun x => bound x (T1 x)) progCost1 where
  ok := prog_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxDI, hxFits, hxM1, hxW1, hxQ1⟩ := hx
    obtain ⟨I, W, hdec⟩ := hxDI
    obtain ⟨y, hxy, hEnc⟩ := hdec
    subst hxy
    obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := W) hEnc
    set B : ℕ := bound (y ++ [W]) (T1 (y ++ [W])) with hBdef
    have hxB : ∀ v ∈ (y ++ [W]), v < B := fun v hv => lt_bound hv
    have hxlen : (y ++ [W]).length = 3 + 4 * I.jobs := by
      have := hEnc.length_eq; simp only [List.length_append, List.length_singleton]; omega
    have hmem_of_idx : ∀ k, k < (y ++ [W]).length → (y ++ [W]).getD k 0 ∈ (y ++ [W]) :=
      fun k hk => by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hval_mem : ∀ k, k < (y ++ [W]).length → (y ++ [W]).getD k 0 < B := fun k hk =>
      hxB _ (hmem_of_idx k hk)
    have hm1 : I.machines = 1 := hmc.symm.trans hxM1
    have hw1 : ∀ j : I.Job, I.w j = 1 := fun j => by
      rw [← hwe j]; exact hxW1 (j : ℕ) (by rw [hjc]; exact j.isLt)
    have hqpos : ∀ j : I.Job, 0 < I.q j := fun j => by
      rw [← hqe j]; exact hxQ1 (j : ℕ) (by rw [hjc]; exact j.isLt)
    have hBeq : B = (y ++ [W]).length + maxEntry (y ++ [W]) + 1 +
        (4 * maxEntry (y ++ [W]) + 20) := by rw [hBdef]; rfl
    have hIjm : (I.jobs : ℕ) ≤ maxEntry (y ++ [W]) := by
      rw [← hjc]
      exact le_maxEntry (hmem_of_idx 0 (by omega))
    have hB2 : 2 < B := by rw [hBeq]; omega
    have hnB : 4 * I.jobs + 5 < B := by rw [hBeq]; omega
    have hpB : ∀ j : I.Job, (I.p j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hpe j]
      exact le_maxEntry (hmem_of_idx (2 + j) (by have := j.isLt; omega))
    have hqB : ∀ j : I.Job, (I.q j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hqe j]
      exact le_maxEntry (hmem_of_idx (2 + jobCount (y ++ [W]) + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hdB : ∀ j : I.Job, (I.d j : ℕ) ≤ maxEntry (y ++ [W]) := fun j => by
      rw [← hde j]
      exact le_maxEntry (hmem_of_idx (2 + 2 * jobCount (y ++ [W]) + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hWle : W ≤ maxEntry (y ++ [W]) := le_maxEntry (by simp)
    have hpqB : ∀ j : I.Job, (I.p j : ℕ) + I.q j < B := fun j => by
      have h1 := hpB j; have h2 := hqB j; rw [hBeq]; omega
    have hdq : ∀ a b : I.Job, (I.d a : ℕ) + I.q b < B := fun a b => by
      have h1 := hdB a; have h2 := hqB b; rw [hBeq]; omega
    have hd2B : ∀ j : I.Job, (I.d j : ℕ) + 2 < B := fun j => by
      have h1 := hdB j; rw [hBeq]; omega
    have hWB : W < B := by have h1 := hWle; rw [hBeq]; omega
    have hpre : (fun σ => σ.inp = y ++ [W] ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "NX").length = I.jobs ∧
        (σ.arrs "CC").length = I.jobs + 1 ∧ (σ.arrs "PC").length = I.jobs + 1)
        (initEnv (ext1 (y ++ [W])) (y ++ [W])) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [initEnv, ext1, hjc]
    obtain ⟨σ6, hr6, hout6⟩ :=
      (prog_spec ⟨y, rfl, hEnc⟩ hm1 hw1 hqpos hB2 hxB hnB hpqB hdq hd2B hWB).run hpre
    refine ⟨ext1 (y ++ [W]), σ6, ?_, hout6⟩
    have hKeq : progCost1 (y ++ [W]) = Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 500 * I.jobs +
        1000 + (500 * (I.jobs + 1) * (I.jobs + 1) + 5000) := by
      unfold progCost1; rw [hjc]
    rw [hKeq]
    exact hr6

theorem fits_mono {c c' w : ℕ} {y : List ℕ} (h : Fits c w y) (hc : c' ≤ c) : Fits c' w y :=
  fun v hv => (Nat.mul_le_mul_right _ hc).trans (h v hv)

/-- Large enough to serve as `L1`'s fitting constant with room for the table, and as the
coefficient and the exponent of the time bound. -/
def cc1 : ℕ := 64 * Lax496464Proofs.Ram.Fits.const L1 + 100000

theorem cc1_ge : 64 * Lax496464Proofs.Ram.Fits.const L1 ≤ cc1 := by unfold cc1; omega

theorem hne1 (w : ℕ) : ∀ x ∈ Dom1 cc1 w, x ≠ [] := by
  rintro x ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits1 (w : ℕ) : ∀ x ∈ Dom1 cc1 w, Fits (Lax496464Proofs.Ram.Fits.const L1) w x := by
  rintro x ⟨-, hxFits, -, -, -⟩
  exact fits_mono hxFits (by have := cc1_ge; omega)

theorem hTab1 (w : ℕ) : ∀ x ∈ Dom1 cc1 w, Lax496464Proofs.Ram.Fits.const L1 * T1 x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne1 w x hx
  obtain ⟨hxDI, hxFits, -, -, -⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  have hge : maxEntry x + 1 ≤ x.length + maxEntry x + 1 := by omega
  calc Lax496464Proofs.Ram.Fits.const L1 * T1 x
      = Lax496464Proofs.Ram.Fits.const L1 * (4 * maxEntry x + 20) := rfl
    _ ≤ Lax496464Proofs.Ram.Fits.const L1 * (20 * (x.length + maxEntry x + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
    _ = (20 * Lax496464Proofs.Ram.Fits.const L1) * (x.length + maxEntry x + 1) := by ring
    _ ≤ cc1 * (x.length + maxEntry x + 1) := by
        have := cc1_ge; exact Nat.mul_le_mul_right _ (by omega)
    _ ≤ cc1 * (x.length + maxEntry x + 1) := le_refl _
    _ ≤ 2 ^ w := hf

theorem hT1 (w : ℕ) : ∀ x ∈ Dom1 cc1 w,
    Layout.const L1 * progCost1 x + 1 ≤ cc1 * (jobCount x + 1) ^ 2 := by
  intro x hx
  obtain ⟨⟨I, W, y, hxy, hEnc⟩, -, -, -, -⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (decision_word_facts (W := W) hEnc).1
  have hlog : ∀ n : ℕ, Lax496464Proofs.Ram.Sort.sortK 90 n ≤ 390 * ((n + 1) * (n + 3)) := by
    intro n
    have h1 := Lax496464Proofs.Ram.Sort.sortK_le 90 n n le_rfl
    have h2 : Nat.log 2 (n + 2) < n + 2 :=
      Nat.log_lt_of_lt_pow' (by omega) Nat.lt_two_pow_self
    calc Lax496464Proofs.Ram.Sort.sortK 90 n
        ≤ (90 + 300) * ((n + 1) * (Nat.log 2 (n + 2) + 1)) := h1
      _ ≤ 390 * ((n + 1) * (n + 3)) := by
          apply Nat.mul_le_mul_left
          apply Nat.mul_le_mul_left
          omega
  have hcost : progCost1 x ≤ 8000 * (jobCount x + 1) ^ 2 := by
    unfold progCost1
    have h1 := hlog (jobCount x)
    nlinarith [h1, sq_nonneg (jobCount x)]
  calc Layout.const L1 * progCost1 x + 1
      ≤ Layout.const L1 * (8000 * (jobCount x + 1) ^ 2) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hcost) 1
    _ = (Layout.const L1 * 8000) * (jobCount x + 1) ^ 2 + 1 := by ring
    _ ≤ cc1 * (jobCount x + 1) ^ 2 := by
        have h2 : Layout.const L1 * 8000 < cc1 := by
          unfold cc1; unfold Layout.const; omega
        have h3 : 1 ≤ (jobCount x + 1) ^ 2 := by
          calc 1 = 1 ^ 2 := by norm_num
            _ ≤ (jobCount x + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        nlinarith [h2, h3]

open Classical Lax496464.ParameterizedComplexity Lax496464.Problems in
/--
---
conclusion: Lax496464.Corollary1.corollary1_time
---
The whole program `prog`, correct by `prog_spec`, compiled and wrapped through the pipeline:
decides `Yes x` for every decision word of a one-machine, unit-weight instance with positive
processing times that fits, within `c (n+1)²` instructions. The domain restricts to positive
processing times — the paper's own standing assumption for Lemma 1's recursion — which the
concept's stated domain does not yet carry; see the module notes.
-/
theorem corollary1_time_proved : ∃ (prog' : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ComputesInTime w prog'
      {x | x ∈ DecisionInstances ∧ Fits c w x ∧ machineCount x = 1 ∧
        (∀ j < jobCount x, wt x j = 1) ∧ (∀ j < jobCount x, 0 < procTime x j)}
      (fun x => if Yes x then [1] else [0])
      (fun x => c * (jobCount x + 1) ^ 2) :=
  ⟨compileProgram L1 prog, cc1, fun w =>
    computesInTime_of_solves_fits (hne1 w) (hfits1 w) (hTab1 w) (prog_solves cc1 w) (hT1 w)⟩

end Lax496464Proofs.Ram.Corollary1Prog
