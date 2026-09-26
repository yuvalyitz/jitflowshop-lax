import Lax496464Proofs.Ram.Corollary1Prog

/-!
# Theorem 4's machine, part 6: reading and sorting

`Corollary1Prog.sortSetup_spec` for any number of machines, and exporting that the sorted
instance keeps the common preprocessing time.
-/

namespace Lax496464Proofs.Ram.T4Front

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464Proofs.Ram.Decode (readInstance readInstance_decoded Decoded)
open Lax496464Proofs.Ram.EstSort (estSortCom estSort_spec dA qA rEst)
open Lax496464Proofs.Ram.BuildSorted (buildSorted buildSorted_spec)
open Lax496464Proofs.Ram.Corollary1Prog
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464.EstOrder Lax496464.Problems Lax496464Proofs.Ram.EstPermute
open Lax496464Proofs.Ram.Dp1 Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.Col1
open Lax496464Proofs.Ram.EstSort (EBase)

set_option maxHeartbeats 4000000 in
/-- Read `x`'s instance and threshold, sort the jobs by earliest start time, and build the
sorted `PS`/`QS`/`DS` arrays. The sorted instance `J` is the one the DP proceeds on:
`EstOrdered`, the same number of jobs as `I`, and the same answer to "is there a feasible set
of weight `W`". -/
theorem sortSetup4_spec {x : List ℕ} {I : Instance} {W : ℕ} (hdec : EncodesDecisionInstance x I W)
    {p : ℕ} (hpu : ∀ j : I.Job, I.p j = p) (hw1 : ∀ j : I.Job, I.w j = 1) (hqpos : ∀ j : I.Job, 0 < I.q j)
    {B : ℕ} (hB2 : 2 < B) (hxB : ∀ v ∈ x, v < B) (hnB : 4 * I.jobs + 5 < B)
    (hpqB : ∀ j : I.Job, (I.p j : ℕ) + I.q j < B) (hdq : ∀ a b : I.Job, (I.d a : ℕ) + I.q b < B)
    (hd2B : ∀ j : I.Job, (I.d j : ℕ) + 2 < B)
    (hdd : ∀ a b : I.Job, (I.d a : ℕ) + I.d b + 3 < B)
    (hdq2 : ∀ a b : I.Job, (I.d a : ℕ) + I.q b + 2 < B) :
    Spec B
      (fun σ => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "NX").length = I.jobs ∧
        (σ.arrs "CC").length = I.jobs + 1 ∧ (σ.arrs "PC").length = I.jobs + 1)
      (.seq readInstance (.seq (.read "W") (.seq (.assign "en" (V "n"))
        (.seq (.assign "sn" (V "n")) (.seq estSortCom buildSorted)))))
      (fun _ σ' => ∃ J : Instance, EstOrdered J ∧ J.jobs = I.jobs ∧ J.machines = I.machines ∧ (∀ j : J.Job, J.p j = p) ∧
        (∀ j : J.Job, J.w j = 1) ∧ (∀ j : J.Job, 0 < J.q j) ∧
        (∀ j : J.Job, (J.p j : ℕ) + J.q j < B) ∧ (∀ a b : J.Job, (J.d a : ℕ) + J.q b < B) ∧
        (∀ j : J.Job, (J.d j : ℕ) + 2 < B) ∧
        (∀ a b : J.Job, (J.d a : ℕ) + J.d b + 3 < B) ∧
        (∀ a b : J.Job, (J.d a : ℕ) + J.q b + 2 < B) ∧
        (∀ W', HasWeight J W' ↔ HasWeight I W') ∧
        σ'.arrs "PS" = (List.range I.jobs).map (fun k => pv J k) ∧
        σ'.arrs "QS" = (List.range I.jobs).map (fun k => qv J k) ∧
        σ'.arrs "DS" = (List.range I.jobs).map (fun k => dv J k) ∧
        σ'.vars "n" = I.jobs ∧ σ'.vars "m" = I.machines ∧
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
  have hn4 : σ4.vars "n" = I.jobs := by rw [hσ4]; simp [Env.setVar, hn3]
  have hm4 : σ4.vars "m" = I.machines := by
    rw [hσ4, hσ3, hσ2]; simp [Env.setVar, hm1', hmc]
  have hn6 : σ6.vars "n" = I.jobs := by
    rw [hfv6 "n" (by decide), hfv5 "n" (by decide)]; exact hn4
  have hm6 : σ6.vars "m" = I.machines := by
    rw [hfv6 "m" (by decide), hfv5 "m" (by decide)]; exact hm4
  refine ⟨σ6, Lax496464Proofs.Ram.Sort.sortK 90 I.jobs + 500 * I.jobs + 1000,
    (hr1.seq (r2.seq (r3.seq (r4.seq (hr5.seq hr6))))).mono ?_, le_rfl,
    J, hEstOrd, rfl, rfl, fun j => hpu (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 j),
    fun j => hw1 (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 j),
    fun j => hqpos (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 j),
    fun j => hpqB (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 j),
    fun a b => hdq (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 a)
      (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 b),
    fun j => hd2B (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 j),
    fun a b => hdd (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 a)
      (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 b),
    fun a b => hdq2 (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 a)
      (listEquiv I.jobs (σ5.arrs "SA") hSAperm5 b),
    hHW, hPSfin, hQSfin, hDSfin, hn6, hm6, hsn6, hW6, hinp6, hout6, hNX6l, hCC6l, hPC6l⟩
  rw [hcost1]
  exact hKbound _ _ _ _ _ _ rfl rfl hcost34 hcost34 rfl rfl


end Lax496464Proofs.Ram.T4Front
