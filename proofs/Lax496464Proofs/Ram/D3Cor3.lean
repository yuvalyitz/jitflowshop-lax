import Lax496464Proofs.Ram.D3Dual

/-!
# Corollary 3, Pure Layer: the Dual Table with Equal Preprocessing Times

With `p_j = p` for all `j`, the instant a partial solution has spent is `u * p` where `u` is the
number of jobs selected so far, so the rows of the dual table are `u = 0 … n` and row `u` stands for
the instant `u * p`:

    `dcap J W X (u * p)` — the (capped) largest weight attainable from the instant `u p`.

The recursion is `D3Dual.dcap_rec` at `t = u p`, `p_j = p`, the second call being at `(u+1) p`,
i.e. row `u + 1`.  On the cells reachable from `(firstM, 0)` — `GoodU`: all thresholds `≥ j0 ≥ u` —
the guard `u + 1 ≤ n` is redundant: a selected job has index `≥ u`, so `u + 1 ≤ n`.
-/

namespace Lax496464Proofs.Ram.D3Cor3

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan Lax496464Proofs.Ram.D2Valid
open Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab Lax496464Proofs.Ram.D3Dual
open Lax496464Proofs.Ram.Dp1 (IsNxt)

variable {J : Instance}

/-- **One cell** at row `u` from `v₁ = D[X₁, u]` and `v₂ = D[X₂, u + 1]`; `n` is the number of jobs
(so the last row is `n`), `p` the common preprocessing time.  The guard is `(u+1) p + q ≤ d`
(`(u+1) p ≤ s_j`) and `u + 1 ≤ n` (redundant on good cells). -/
def dStepU (W n p q d w u v1 v2 : ℕ) : ℕ :=
  max v1 (if (u + 1) * p + q ≤ d ∧ u + 1 ≤ n then min W (w + v2) else 0)

/-- A cell `(X, u)` is **good**: every threshold is at least some `j0 ≥ u` (`u` jobs, with
strictly increasing indices, have been decided). -/
def GoodU (J : Instance) (X : Finset J.Job) (u : ℕ) : Prop :=
  ∃ j0 : ℕ, (∀ x ∈ X, j0 ≤ (x : ℕ)) ∧ u ≤ j0

theorem goodU_zero (X : Finset J.Job) : GoodU J X 0 := ⟨0, fun _x _ => Nat.zero_le _, le_rfl⟩

theorem goodU_X1 {X : Finset J.Job} {j : J.Job} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x) {u : ℕ}
    (hg : GoodU J X u) : GoodU J (X1 J X j) u := by
  obtain ⟨j0, hj0, hu⟩ := hg
  exact ⟨j + 1, fun x hx => X1_gt hjmin x hx, by have := hj0 j hjX; omega⟩

theorem goodU_X2 (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {X : Finset J.Job}
    {j : J.Job} (hjX : j ∈ X) (hjmin : ∀ x ∈ X, j ≤ x) {u : ℕ} (hg : GoodU J X u) :
    GoodU J (X2 J X j) (u + 1) := by
  obtain ⟨j0, hj0, hu⟩ := hg
  exact ⟨j + 1, fun x hx => X2_gt hest hq hjmin x hx, by have := hj0 j hjX; omega⟩

/-- On a good cell with a threshold, the next row exists: `u + 1 ≤ n`. -/
theorem goodU_step_le {X : Finset J.Job} {j : J.Job} (hjX : j ∈ X) {u : ℕ} (hg : GoodU J X u) :
    u + 1 ≤ J.jobs := by
  obtain ⟨j0, hj0, hu⟩ := hg
  have := hj0 j hjX
  have := j.isLt
  omega

/-- **The cell recursion, equal preprocessing times.** -/
theorem dcellU (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {p : ℕ}
    (hp : ∀ j : J.Job, J.p j = p) {W : ℕ} {X : Finset J.Job} {j : J.Job} (hjX : j ∈ X)
    (hjmin : ∀ x ∈ X, j ≤ x) {u : ℕ} (hg : GoodU J X u) {v1 v2 : ℕ}
    (h1 : v1 = dcap J W (X1 J X j) (u * p))
    (h2 : (u + 1) * p + J.q j ≤ J.d j → v2 = dcap J W (X2 J X j) ((u + 1) * p)) :
    dStepU W J.jobs p (J.q j) (J.d j) (J.w j) u v1 v2 = dcap J W X (u * p) := by
  have hR := goodU_step_le hjX hg
  have hmul : (u + 1) * p = u * p + p := Nat.succ_mul u p
  rw [dcap_rec hest hq W hjX hjmin (u * p), hp j]
  unfold dStepU
  by_cases hgd : (u + 1) * p + J.q j ≤ J.d j
  · have hgd' : u * p + p + J.q j ≤ J.d j := by rw [← hmul]; exact hgd
    rw [if_pos hgd', if_pos ⟨hgd, hR⟩, h1, h2 hgd, hmul]
  · have hgd' : ¬ (u * p + p + J.q j ≤ J.d j) := by rw [← hmul]; exact hgd
    rw [if_neg hgd', if_neg (fun h => hgd h.1), h1]

/-- The same for `X` given as a sorted list and `X₁`, `X₂` as the machine's scans produce them. -/
theorem dcellU_list (hest : EstOrdered J) (hq : ∀ j : J.Job, 0 < J.q j) {p : ℕ}
    (hp : ∀ j : J.Job, J.p j = p) {W : ℕ} {j : ℕ} {Zs : List ℕ} (hjn : j < J.jobs)
    (hjZ : ∀ z ∈ Zs, j < z) {u : ℕ} (hg : GoodU J (ofList J (j :: Zs)) u)
    {y0 cur1 k1 cur2 k2 : ℕ} (hnx : IsNxt j hjn y0)
    (hr1 : ScanOK J.jobs Zs (j + 1) (cur1, k1)) (hr2 : ScanOK J.jobs Zs y0 (cur2, k2))
    (hjy : j < y0) {v1 v2 : ℕ}
    (h1 : v1 = dcap J W (ofList J (newL J.jobs Zs cur1 k1)) (u * p))
    (h2 : (u + 1) * p + J.q ⟨j, hjn⟩ ≤ J.d ⟨j, hjn⟩ →
      v2 = dcap J W (ofList J (newL J.jobs Zs cur2 k2)) ((u + 1) * p)) :
    dStepU W J.jobs p (J.q ⟨j, hjn⟩) (J.d ⟨j, hjn⟩) (J.w ⟨j, hjn⟩) u v1 v2 =
      dcap J W (ofList J (j :: Zs)) (u * p) := by
  have hjX : (⟨j, hjn⟩ : J.Job) ∈ ofList J (j :: Zs) := by
    rw [mem_ofList]; simp
  have hjmin : ∀ x ∈ ofList J (j :: Zs), (⟨j, hjn⟩ : J.Job) ≤ x := by
    intro x hx
    rw [mem_ofList] at hx
    rcases List.mem_cons.mp hx with h | h
    · exact Fin.mk_le_mk.mpr (by omega)
    · exact Fin.mk_le_mk.mpr (hjZ _ h).le
  refine dcellU hest hq hp hjX hjmin hg ?_ ?_
  · rw [X1_ofList hjn hjZ hr1]; exact h1
  · intro hgd; rw [X2_ofList hjn hjZ hest hnx hr2 hjy]; exact h2 hgd

/-! ## The table invariant (mirrors `D3Dual.DTabOK`; rows `u ≤ n`, block width `n + 1`) -/

/-- Entries of the numbers `≥ thr` are right on good cells; those below `thr` are zero.
Row `u` of number `c` is at `c * (n + 1) + u` and stands for the instant `u * p`. -/
def UTabOK (J : Instance) (n m W p N thr : ℕ) (T : List ℕ) : Prop :=
  T.length = N * (n + 1) ∧
  (∀ Zs, SL n m Zs → thr ≤ codeL n m Zs → ∀ u ≤ n, GoodU J (ofList J Zs) u →
    T.getD (codeL n m Zs * (n + 1) + u) 0 = dcap J W (ofList J Zs) (u * p)) ∧
  (∀ i, i < N * (n + 1) → i / (n + 1) < thr → T.getD i 0 = 0)

theorem utab_step {J : Instance} {n m W p N c : ℕ} {T T' : List ℕ} (hN : N = (n + 1) ^ m)
    (hT : UTabOK J n m W p N (c + 1) T) (hlen : T'.length = N * (n + 1))
    (hout : ∀ i, i < N * (n + 1) → i / (n + 1) ≠ c → T'.getD i 0 = T.getD i 0)
    (hblock : ∀ Zs, SL n m Zs → codeL n m Zs = c → ∀ u ≤ n, GoodU J (ofList J Zs) u →
      T'.getD (c * (n + 1) + u) 0 = dcap J W (ofList J Zs) (u * p)) :
    UTabOK J n m W p N c T' := by
  obtain ⟨hl, hrep, hzero⟩ := hT
  refine ⟨hlen, ?_, ?_⟩
  · intro Zs hsl hc u hu hgood
    by_cases hcc : codeL n m Zs = c
    · rw [hcc]; exact hblock Zs hsl hcc u hu hgood
    · have hgt : c + 1 ≤ codeL n m Zs := by omega
      have hlt : codeL n m Zs * (n + 1) + u < N * (n + 1) := by
        have h1 := hsl.codeL_lt
        rw [← hN] at h1
        nlinarith
      have hdiv := div_block (codeL n m Zs) n u hu
      rw [hout _ hlt (by rw [hdiv]; exact hcc)]
      exact hrep Zs hsl hgt u hu hgood
  · intro i hi hic
    have hne : i / (n + 1) ≠ c := by omega
    rw [hout i hi hne]
    exact hzero i hi (by omega)

theorem utab_step_empty {J : Instance} {n m W p N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hc : c = N - 1) (hT : UTabOK J n m W p N (c + 1) T) :
    UTabOK J n m W p N c T := by
  refine utab_step hN hT hT.1 (fun i _ _ => rfl) ?_
  intro Zs hsl hcode u hu _
  have hZs : Zs = [] := eq_nil_of_code_top hsl (by rw [hcode, hc, hN])
  subst hZs
  rw [ofList_nil, dcap_empty]
  have hlt : c * (n + 1) + u < N * (n + 1) := by
    have h1 : c < N := by
      have := hsl.codeL_lt
      rw [← hN, hcode] at this
      exact this
    nlinarith
  exact hT.2.2 _ hlt (by rw [div_block c n u hu]; omega)

theorem utab_step_invalid {J : Instance} {n m W p N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hnc : ¬ IsCode n m c) (hT : UTabOK J n m W p N (c + 1) T) :
    UTabOK J n m W p N c T := by
  refine utab_step hN hT hT.1 (fun i _ _ => rfl) ?_
  intro Zs hsl hcode
  exact absurd ⟨Zs, hsl, hcode⟩ hnc

/-- **The answer read from the finished table**: the entry of the `m`-smallest-thresholds block at
row `0` is `W`. -/
theorem hasWeight_iff_utab (hest : EstOrdered J) {W p N : ℕ} {T : List ℕ}
    (hT : UTabOK J J.jobs J.machines W p N 0 T) :
    HasWeight J W ↔ T.getD (codeL J.jobs J.machines (List.range (min J.machines J.jobs)) *
      (J.jobs + 1)) 0 = W := by
  have h := hT.2.1 _ (sl_range J.jobs J.machines) (Nat.zero_le _) 0 (Nat.zero_le _)
    (by rw [← firstM_eq_ofList]; exact goodU_zero _)
  rw [Nat.add_zero, Nat.zero_mul] at h
  rw [h, ← firstM_eq_ofList, hasWeight_iff_dcap hest]

/-! ## Counting the rows -/

end Lax496464Proofs.Ram.D3Cor3
