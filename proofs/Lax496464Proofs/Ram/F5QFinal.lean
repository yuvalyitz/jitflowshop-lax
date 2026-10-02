import Lax496464Proofs.Ram.F5QOk
import Lax496464Proofs.Ram.Q3Final

/-!
# Theorem 5, Profile Sweep: the Running Time Statement

`prog5` solves, on the words that present an instance and an accuracy `e`, the function
`x ↦ [fptasOut I e]`, within `cost5`, at every word length at which the admissibility clauses
hold; the scheme's guarantee follows from `F5Math.delivers_fptasOut`.
-/

namespace Lax496464Proofs.F5QFinal

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464.WordEncoding Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Problems
open Lax496464.ParameterizedComplexity Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.F5QProg Lax496464Proofs.F5QOk
open Lax496464Proofs.Ram.Q3Final (btX foldr_max_le')
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry bound lt_bound const maxEntry_mem
  computesInTime_of_solves_fits)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts fits_mono)

/-- The threshold of the exact program: `2 e n²`. -/
def thrX (x : List ℕ) : ℕ := 2 * threshold x * jobCount x * jobCount x

/-- The number of table cells `(m+1)^qmax · (2 e n² + 1)`. -/
def NX5 (x : List ℕ) : ℕ := btX x * (thrX x + 1)

/-- The total weight. -/
def sumwt (x : List ℕ) : ℕ := ((List.range (jobCount x)).map (wt x)).sum

/-- Room for every intermediate value. -/
def T5 (x : List ℕ) : ℕ := NX5 x + 5 * maxEntry x + 40 + sumwt x

/-- The arrays the program is given. -/
def ext5 (x : List ℕ) (a : String) : ℕ :=
  if a = "A" then 4 * jobCount x
  else if a = "SA" ∨ a = "SB" ∨ a = "PS" ∨ a = "QS" ∨ a = "DS" ∨ a = "WS" then jobCount x
  else if a = "T" ∨ a = "S" then NX5 x
  else if a = "G" then btX x
  else 0

/-- The cost bound, as it comes out of `prog5_spec`. -/
def cost5X (x : List ℕ) : ℕ :=
  cost5 (jobCount x) (NX5 x) (qmaxOf x) (btX x) (machineCount x + 1)

/-- The number the scheme writes, as a function of the word. -/
noncomputable def f5 (x : List ℕ) : List ℕ :=
  open Classical in
  if h : ∃ (I : Instance) (e : ℕ), EncodesApprox I x e then
    [fptasOut h.choose h.choose_spec.choose] else []

theorem fptasOut_unique {x : List ℕ} {I I' : Instance} {e e' : ℕ} (h : EncodesApprox I x e)
    (h' : EncodesApprox I' x e') : fptasOut I' e' = fptasOut I e := by
  obtain ⟨y, hxy, he, hEnc⟩ := h
  obtain ⟨y', hxy', he', hEnc'⟩ := h'
  obtain ⟨hI, hE⟩ := Lax496464Proofs.Ram.Reduction.encodesDecisionInstance_unique
    (⟨y', hxy', hEnc'⟩ : EncodesDecisionInstance x I' e') (⟨y, hxy, hEnc⟩ : EncodesDecisionInstance x I e)
  rw [hI, hE]

theorem f5_eq {x : List ℕ} {I : Instance} {e : ℕ} (h : EncodesApprox I x e) :
    f5 x = [fptasOut I e] := by
  classical
  have hex : ∃ (I : Instance) (e : ℕ), EncodesApprox I x e := ⟨I, e, h⟩
  unfold f5
  rw [dif_pos hex]
  exact congrArg (fun v => [v]) (fptasOut_unique h hex.choose_spec.choose_spec)

theorem sumwt_eq {x y : List ℕ} {I : Instance} {e : ℕ} (hEnc : EncodesInstance y I)
    (hx : x = y ++ [e]) : sumwt x = ∑ j : Fin I.jobs, I.w j := by
  obtain ⟨hjc, -, -, -, -, hwe⟩ := decision_word_facts (W := e) hEnc
  subst hx
  unfold sumwt
  rw [hjc]
  have : ∀ n : ℕ, ∀ hn : n ≤ I.jobs, (((List.range n).map (wt (y ++ [e]))).sum) =
      ∑ j ∈ Finset.range n, (if h : j < I.jobs then I.w ⟨j, h⟩ else 0) := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.map_append, List.sum_append, ih (by omega),
        Finset.sum_range_succ]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [dif_pos (by omega)]
      exact congrArg _ (hwe ⟨n, by omega⟩)
  rw [this I.jobs le_rfl]
  rw [← Fin.sum_univ_eq_sum_range (fun j => if h : j < I.jobs then I.w ⟨j, h⟩ else 0)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dif_pos j.isLt]

/-- Words that present an instance and an accuracy, with positive processing times, that fit at
word length `w` with constant `c`, whose total weight and profile table are words. -/
def Dom5 (c w : ℕ) : Set (List ℕ) :=
  {x | x ∈ ApproxInstances ∧ Fits c w x ∧ c * sumwt x ≤ 2 ^ w ∧
    (∀ j < jobCount x, 0 < procTime x j) ∧
    c * (jobCount x + 1) ^ 2 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
      (jobCount x + 1) ≤ 2 ^ w}

set_option maxHeartbeats 8000000 in
open Classical in
theorem prog5_solves (cc w : ℕ) :
    Solves L5 prog5 (Dom5 cc w) f5 (fun x => bound x (T5 x)) cost5X where
  ok := prog5_ok
  inp := fun _ _ v hv => lt_bound hv
  run := by
    intro x hx
    obtain ⟨hxAI, hxFits, hsum, hxQ, hbig⟩ := hx
    obtain ⟨I, e, hAppr⟩ := hxAI
    have hf5 := f5_eq hAppr
    obtain ⟨y, hxy, he, hEnc⟩ := hAppr
    have hdec : EncodesDecisionInstance x I e := ⟨y, hxy, hEnc⟩
    have hAppr' : EncodesApprox I x e := ⟨y, hxy, he, hEnc⟩
    subst hxy
    obtain ⟨hjc, hmc, hpe, hqe, hde, hwe⟩ := decision_word_facts (W := e) hEnc
    obtain ⟨hthr, -, -⟩ := Lax496464Proofs.Ram.Q3Front.threshold_eq (W := e) hEnc
    set x : List ℕ := y ++ [e] with hxdef
    set B : ℕ := bound x (T5 x) with hBdef
    have hxlen : x.length = 3 + 4 * I.jobs := by
      have := hEnc.length_eq; simp only [hxdef, List.length_append, List.length_singleton]; omega
    have hmem_of_idx : ∀ k, k < x.length → x.getD k 0 ∈ x :=
      fun k hk => by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
    have hqpos : ∀ j : I.Job, 0 < I.q j := fun j => by
      rw [← hqe j]; exact hxQ (j : ℕ) (by rw [hjc]; exact j.isLt)
    have hBeq : B = x.length + maxEntry x + 1 + (NX5 x + 5 * maxEntry x + 40 + sumwt x) := by
      rw [hBdef]; rfl
    have hpB : ∀ j : I.Job, (I.p j : ℕ) ≤ maxEntry x := fun j => by
      rw [← hpe j]; exact le_maxEntry (hmem_of_idx (2 + j) (by have := j.isLt; omega))
    have hqB : ∀ j : I.Job, (I.q j : ℕ) ≤ maxEntry x := fun j => by
      rw [← hqe j]
      exact le_maxEntry (hmem_of_idx (2 + jobCount x + j) (by rw [hjc]; have := j.isLt; omega))
    have hdB : ∀ j : I.Job, (I.d j : ℕ) ≤ maxEntry x := fun j => by
      rw [← hde j]
      exact le_maxEntry (hmem_of_idx (2 + 2 * jobCount x + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hwB : ∀ j : I.Job, (I.w j : ℕ) ≤ maxEntry x := fun j => by
      rw [← hwe j]
      exact le_maxEntry (hmem_of_idx (2 + 3 * jobCount x + j) (by
        rw [hjc]; have := j.isLt; omega))
    have hmach : I.machines ≤ maxEntry x := by
      rw [← hmc]; exact le_maxEntry (hmem_of_idx 1 (by omega))
    have heM : e ≤ maxEntry x := le_maxEntry (by simp [hxdef])
    have hqmle : qmaxOf x ≤ maxEntry x := by
      unfold qmaxOf
      refine foldr_max_le' (fun v hv => ?_)
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv
      have hk' : k < I.jobs := by have := List.mem_range.mp hk; rwa [hjc] at this
      have := hqB ⟨k, hk'⟩
      rw [hqe ⟨k, hk'⟩] at *
      exact this
    have hbtpos : 1 ≤ btX x := by
      unfold btX; exact Nat.one_le_pow _ _ (by omega)
    have hNX : NX5 x = btX x * (thr I e + 1) := by
      unfold NX5 thrX; rw [hthr, hjc]; rfl
    have hthrN : thr I e + 1 ≤ NX5 x := by
      rw [hNX]; exact Nat.le_mul_of_pos_left _ hbtpos
    have hbtN : btX x ≤ NX5 x := by
      rw [hNX]; exact Nat.le_mul_of_pos_right _ (by omega)
    have hoB0 : fptasOut I e ≤ sumwt x := by
      rw [sumwt_eq hEnc rfl]; exact fptasOut_le_total I he
    have hB20 : 20 < B := by rw [hBeq]; omega
    have hnB : 4 * I.jobs + 8 < B := by rw [hBeq]; omega
    have hmB : I.machines + 8 < B := by rw [hBeq]; omega
    have heB : 2 * e + 8 < B := by rw [hBeq]; omega
    have hpqB : ∀ j : I.Job, (I.p j : ℕ) + I.q j + 8 < B := fun j => by
      have h1 := hpB j; have h2 := hqB j; rw [hBeq]; omega
    have hd8 : ∀ j : I.Job, (I.d j : ℕ) + 8 < B := fun j => by
      have h1 := hdB j; rw [hBeq]; omega
    have hdd : ∀ a b : I.Job, (I.d a : ℕ) + I.d b + 3 < B := fun a b => by
      have h1 := hdB a; have h2 := hdB b; rw [hBeq]; omega
    have hdq2 : ∀ a b : I.Job, (I.d a : ℕ) + I.q b + 2 < B := fun a b => by
      have h1 := hdB a; have h2 := hqB b; rw [hBeq]; omega
    have hT3 : ∀ a b c : I.Job, (I.d a : ℕ) + I.p b + I.q c + 9 < B := fun a b c => by
      have h1 := hdB a; have h2 := hpB b; have h3 := hqB c; rw [hBeq]; omega
    have hwB' : ∀ j : I.Job, (I.w j : ℕ) + 8 < B := fun j => by
      have h1 := hwB j; rw [hBeq]; omega
    have hthrB : thr I e + 8 < B := by rw [hBeq]; omega
    have hqmB : qmaxOf x + 8 < B := by rw [hBeq]; omega
    have hbtB : btX x + 8 < B := by rw [hBeq]; omega
    have hNB : NX5 x + 8 < B := by rw [hBeq]; omega
    have hoB : fptasOut I e + 8 < B := by rw [hBeq]; omega
    have hpre : (fun σ : Env => σ.inp = x ∧ σ.out = [] ∧ (σ.arrs "A").length = 4 * I.jobs ∧
        (σ.arrs "SA").length = I.jobs ∧ (σ.arrs "SB").length = I.jobs ∧
        (σ.arrs "PS").length = I.jobs ∧ (σ.arrs "QS").length = I.jobs ∧
        (σ.arrs "DS").length = I.jobs ∧ (σ.arrs "WS").length = I.jobs ∧
        (σ.arrs "T").length = NX5 x ∧ (σ.arrs "S").length = NX5 x ∧
        σ.arrs "G" = List.replicate (btX x) 0) (initEnv (ext5 x) x) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initEnv, ext5, hjc]
    obtain ⟨σ', hr, hout⟩ :=
      (prog5_spec (x := x) (I := I) (e := e) (B := B) hdec he hqpos hB20 (fun v hv => lt_bound hv)
        hnB hmB heB hpqB hd8 hdd hdq2 hT3 hwB' hthrB (qm := qmaxOf x) (bb := machineCount x + 1)
        (bt := btX x) (w1 := thr I e + 1) (N := NX5 x) rfl (by rw [hmc]) rfl rfl hNX hqmB hbtB
        hNB hoB).run hpre
    refine ⟨ext5 x, σ', ?_, by rw [hout, hf5]⟩
    have hKeq : cost5X x = cost5 I.jobs (NX5 x) (qmaxOf x) (btX x) (machineCount x + 1) := by
      unfold cost5X; rw [hjc]
    rw [hKeq]
    exact hr

/-! ## The running time -/

theorem cost5_le {n N qm bt bb len : ℕ} (hbt : bt = bb ^ qm) (hbb : 1 ≤ bb) (hbtN : bt ≤ N)
    (hN1 : 1 ≤ N) (hnl : n ≤ len) :
    cost5 n N qm bt bb ≤ 390 * ((len + 1) * (Nat.log 2 (len + 2) + 1)) + 2300 * (N * (n + 1)) := by
  have h3 := Lax496464Proofs.Ram.Q3Final.cost3_le hbt hbb hbtN hN1 hnl
  have hc : cost5 n N qm bt bb ≤ Lax496464Proofs.Ram.Q3Prog.cost3 n N qm bt bb + 88 * n + 64 * N + 72 := by
    unfold cost5 Lax496464Proofs.F5QRest.cost5r Lax496464Proofs.Ram.Q3Prog.cost3
    omega
  have hNn : n ≤ N * (n + 1) := by nlinarith
  have hNN : N ≤ N * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h1 : 1 ≤ N * (n + 1) := by nlinarith
  omega

theorem thr_le (n e : ℕ) : 2 * e * n * n + 1 ≤ 2 * ((n + 1) ^ 2 * (e + 1)) := by
  nlinarith [Nat.zero_le (e * n), Nat.zero_le (n * n), Nat.zero_le e, Nat.zero_le n]

/-- The constant: the fitting condition's, with room for the table, and the time bound's. -/
def cc5 : ℕ := 100000

theorem const_L5 : Layout.const L5 = 10 := rfl
theorem fconst_L5 : const L5 = 2 * (12 + 2 + 53 + 10) := by decide

theorem hne5 (w : ℕ) : ∀ x ∈ Dom5 cc5 w, x ≠ [] := by
  rintro x ⟨⟨I, e, y, hxy, he, hEnc⟩, -, -, -, -⟩ hnil
  rw [hxy] at hnil
  exact absurd hnil (by simp)

theorem hfits5 (w : ℕ) : ∀ x ∈ Dom5 cc5 w, Fits (const L5) w x := by
  rintro x ⟨-, hxFits, -, -, -⟩
  exact fits_mono hxFits (by rw [fconst_L5]; unfold cc5; omega)

/-- The facts about a word that both numeric obligations use. -/
theorem dom5_facts {x : List ℕ} (hx : x ∈ ApproxInstances) :
    jobCount x ≤ x.length ∧ NX5 x * (jobCount x + 1) ≤
      2 * ((jobCount x + 1) ^ 2 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
        (jobCount x + 1)) ∧ 1 ≤ NX5 x ∧ btX x ≤ NX5 x := by
  obtain ⟨I, e, y, hxy, he, hEnc⟩ := hx
  have hjc : jobCount x = I.jobs := by
    rw [hxy]; exact (decision_word_facts (W := e) hEnc).1
  have hxlen : x.length = 3 + 4 * I.jobs := by
    rw [hxy]; have := hEnc.length_eq
    simp only [List.length_append, List.length_singleton]; omega
  have hthr : threshold x = e := by
    rw [hxy]; exact (Lax496464Proofs.Ram.Q3Front.threshold_eq (W := e) hEnc).1
  have hbtpos : 1 ≤ btX x := by unfold btX; exact Nat.one_le_pow _ _ (by omega)
  have hNX : NX5 x = btX x * (2 * e * jobCount x * jobCount x + 1) := by
    unfold NX5 thrX; rw [hthr]
  have hpos : 1 ≤ NX5 x := by
    rw [hNX]; exact Nat.mul_pos hbtpos (by omega)
  refine ⟨by rw [hjc, hxlen]; omega, ?_, hpos, ?_⟩
  · have h1 := thr_le (jobCount x) e
    have hb : btX x = (machineCount x + 1) ^ qmaxOf x := rfl
    rw [hNX, hthr, ← hb]
    calc btX x * (2 * e * jobCount x * jobCount x + 1) * (jobCount x + 1)
        ≤ btX x * (2 * ((jobCount x + 1) ^ 2 * (e + 1))) * (jobCount x + 1) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
      _ = 2 * ((jobCount x + 1) ^ 2 * (e + 1) * btX x * (jobCount x + 1)) := by ring
  · rw [hNX]; exact Nat.le_mul_of_pos_right _ (by omega)

theorem hTab5 (w : ℕ) : ∀ x ∈ Dom5 cc5 w, const L5 * T5 x ≤ 2 ^ w := by
  intro x hx
  have hxne : x ≠ [] := hne5 w x hx
  have hfa := dom5_facts hx.1
  obtain ⟨-, hxFits, hsum, -, hbig⟩ := hx
  have hmem : maxEntry x ∈ x := Lax496464Proofs.Ram.Fits.maxEntry_mem hxne
  have hf := hxFits (maxEntry x) hmem
  have hlen : 1 ≤ x.length := List.length_pos_iff.mpr hxne
  obtain ⟨-, hNP, hN1, -⟩ := hfa
  have hNN : NX5 x ≤ NX5 x * (jobCount x + 1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold T5
  rw [fconst_L5]
  have hP : cc5 * (jobCount x + 1) ^ 2 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
      (jobCount x + 1) = cc5 * ((jobCount x + 1) ^ 2 * (threshold x + 1) *
        (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1)) := by ring
  rw [hP] at hbig
  generalize (jobCount x + 1) ^ 2 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
    (jobCount x + 1) = P at *
  unfold cc5 at hf hbig hsum
  omega

theorem hT5c (w : ℕ) : ∀ x ∈ Dom5 cc5 w, Layout.const L5 * cost5X x + 1 ≤
    cc5 * (jobCount x + 1) ^ 2 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
      (jobCount x + 1) + cc5 * sortCost x := by
  intro x hx
  have hfa := dom5_facts hx.1
  obtain ⟨hnl, hNP, hN1, hbtN⟩ := hfa
  have hc := cost5_le (n := jobCount x) (N := NX5 x) (qm := qmaxOf x) (bt := btX x)
    (bb := machineCount x + 1) (len := x.length) rfl (by omega) hbtN hN1 hnl
  have hsc : sortCost x = (x.length + 1) * (Nat.log 2 (x.length + 2) + 1) := rfl
  have hP : cc5 * (jobCount x + 1) ^ 2 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
      (jobCount x + 1) = cc5 * ((jobCount x + 1) ^ 2 * (threshold x + 1) *
        (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1)) := by ring
  have hpos : 1 ≤ (jobCount x + 1) ^ 2 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
      (jobCount x + 1) := by
    apply Nat.one_le_iff_ne_zero.mpr
    positivity
  rw [hP, hsc, const_L5]
  unfold cost5X
  generalize (jobCount x + 1) ^ 2 * (threshold x + 1) * (machineCount x + 1) ^ qmaxOf x *
    (jobCount x + 1) = P at *
  unfold cc5
  omega

/-! ## From computing the number to approximating -/

/-- A program that computes a function whose value is always an acceptable answer approximates. -/
theorem approximatesInTime_of_computes {w : ℕ} {prog : Program} {D : Set (List ℕ)}
    {f : List ℕ → List ℕ} {T : List ℕ → ℕ} (h : ComputesInTime w prog D f T)
    (hd : ∀ x ∈ D, Delivers x (f x)) : ApproximatesInTime w prog D T := by
  intro x hx
  obtain ⟨t, ht, hrun⟩ := h x hx
  exact ⟨f x, t, ht, hrun, hd x hx⟩

theorem delivers_f5 (x : List ℕ) (hx : x ∈ ApproxInstances) : Delivers x (f5 x) := by
  obtain ⟨I, e, h⟩ := hx
  rw [f5_eq h]
  exact delivers_fptasOut h

open Classical in
/--
The profile sweep of Section 5 as a word RAM approximation scheme.  Read the instance and the
accuracy `e` (in the place of the threshold), sort the jobs by start time, zero the weight of
every unfit job, take `k = max 1 (w_max' / (e n))`, replace every weight `w ≥ 1` by
`(w - 1)/k + 1`, set the threshold `W = 2 e n²`, run the exact profile sweep (`Q3Core.coreCom`,
unchanged) on the rescaled weights, scan the finished table for the largest weight column that
has a finite cell, and write `k (W' - n)` if `k > 1` and `W'` otherwise (`F5Math.fptasOut`).
The cost is that of the exact program with threshold `2 e n²`, that is
`O((n+1)^2 (e+1) (m+1)^qmax (n+1))`, plus the sort; the guarantee is `F5Math.fptas_value`.

The domain differs from the concept statement `theorem5_byQmax` in one clause:
`c * ∑ wⱼ ≤ 2^w` in place of `∑ wⱼ < 2^w` (the machine layout has to hold the written number,
which is as large as the total weight, in a cell of a span of several arrays; see the report).
-/
theorem theorem5_byQmax_strong : ∃ (prog : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
    ApproximatesInTime w prog
      {x | x ∈ ApproxInstances ∧ Fits c w x ∧
        c * ((List.range (jobCount x)).map (wt x)).sum ≤ 2 ^ w ∧
        (∀ j < jobCount x, 0 < procTime x j) ∧
        c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
          (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) ≤ 2 ^ w}
      (fun x => c * (jobCount x + 1) ^ 2 * (threshold x + 1) *
        (machineCount x + 1) ^ qmaxOf x * (jobCount x + 1) + c * sortCost x) :=
  ⟨compileProgram L5 prog5, cc5, fun w =>
    approximatesInTime_of_computes
      (computesInTime_of_solves_fits (hne5 w) (hfits5 w) (hTab5 w) (prog5_solves cc5 w) (hT5c w))
      (fun x hx => delivers_f5 x hx.1)⟩

end Lax496464Proofs.F5QFinal

