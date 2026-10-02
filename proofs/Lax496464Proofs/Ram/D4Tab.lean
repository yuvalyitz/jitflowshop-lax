import Lax496464Proofs.Ram.D2StepPure
import Lax496464Proofs.Ram.D3Dual
import Lax496464Proofs.Ram.D4Row

/-!
# Corollary 2, Pure Layer: the Dual Table Invariant and One Block

`DInv` is `D3Dual.DTabOK` (entries of the numbers `≥ thr` are right on good cells, those below are
zero) together with "every entry is at most the threshold `W`", which is what keeps every value
the machine reads or writes inside the word.  `dblock` is `D2StepPure.block_rep` for the dual cell.
-/

namespace Lax496464Proofs.Ram.D4Tab

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan Lax496464Proofs.Ram.D2Valid
open Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab Lax496464Proofs.Ram.D3Dual
open Lax496464Proofs.Ram.D2StepPure (newcode_gt)
open Lax496464Proofs.Ram.Dp1 (IsNxt nxt_gt)

/-- The table invariant of the dual loop: right on good cells, and every entry `≤ W`. -/
def DInv (J : Instance) (n m W R N thr : ℕ) (T : List ℕ) : Prop :=
  DTabOK J n m W R N thr T ∧ ∀ i, T.getD i 0 ≤ W

theorem dinv_init (J : Instance) (n m W R : ℕ) :
    DInv J n m W R ((n + 1) ^ m) ((n + 1) ^ m)
      (List.replicate ((n + 1) ^ m * (R + 1)) 0) := by
  refine ⟨⟨by simp, ?_, ?_⟩, ?_⟩
  · intro Zs hsl h
    have := hsl.codeL_lt
    omega
  · intro i hi _
    simp [hi]
  · intro i
    by_cases hi : i < (n + 1) ^ m * (R + 1)
    · simp [hi]
    · simp [List.getD_eq_getElem?_getD, hi]

theorem dinv_step_empty {J : Instance} {n m W R N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hc : c = N - 1) (hT : DInv J n m W R N (c + 1) T) : DInv J n m W R N c T :=
  ⟨dtab_step_empty hN hc hT.1, hT.2⟩

theorem dinv_step_invalid {J : Instance} {n m W R N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hnc : ¬ IsCode n m c) (hT : DInv J n m W R N (c + 1) T) : DInv J n m W R N c T :=
  ⟨dtab_step_invalid hN hnc hT.1, hT.2⟩

theorem dinv_step {J : Instance} {n m W R N c : ℕ} {T T' : List ℕ} (hN : N = (n + 1) ^ m)
    (hT : DInv J n m W R N (c + 1) T) (hlen : T'.length = N * (R + 1))
    (hout : ∀ i, i < N * (R + 1) → i / (R + 1) ≠ c → T'.getD i 0 = T.getD i 0)
    (hblock : ∀ Zs, SL n m Zs → codeL n m Zs = c → ∀ t ≤ R, GoodF J R (ofList J Zs) t →
      T'.getD (c * (R + 1) + t) 0 = dcap J W (ofList J Zs) t)
    (hle : ∀ i, i < N * (R + 1) → i / (R + 1) = c → T'.getD i 0 ≤ W) :
    DInv J n m W R N c T' := by
  refine ⟨dtab_step hN hT.1 hlen hout hblock, fun i => ?_⟩
  by_cases hi : i < N * (R + 1)
  · by_cases hic : i / (R + 1) = c
    · exact hle i hi hic
    · rw [hout i hi hic]; exact hT.2 i
  · rw [List.getD_eq_getElem?_getD]
    have : T'.length ≤ i := by rw [hlen]; omega
    rw [List.getElem?_eq_none this]; simp

/-- **The block of the number `c = code (j :: Zs)`**: if its cells were computed by `dStep` from
the cells `(c₁, t)` and `(c₂, t + p_j)` of a table that is right on the numbers above `c`, they are
right on the good cells. -/
theorem dblock {J : Instance} {n m W R N c j : ℕ} {Zs : List ℕ} {T T' : List ℕ}
    (hn : J.jobs = n) (hm : 1 ≤ m)
    (hest : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i)
    (hT : DTabOK J n m W R N (c + 1) T)
    (hsl : SL n m (j :: Zs)) (hcode : codeL n m (j :: Zs) = c)
    (hjn : j < J.jobs) {y0 : ℕ} (hnx : IsNxt j hjn y0)
    {cur1 k1 cur2 k2 : ℕ}
    (hs1 : scanF n (lstOf n (m - 1) Zs) (j + 1) = (cur1, k1))
    (hs2 : scanF n (lstOf n (m - 1) Zs) y0 = (cur2, k2))
    (hcells : ∀ r, r ≤ R → T'.getD (c * (R + 1) + r) 0 =
      dStep W R (J.p ⟨j, hjn⟩) (J.q ⟨j, hjn⟩) (J.d ⟨j, hjn⟩) (J.w ⟨j, hjn⟩) r
        (T.getD (codeL n m (newL n Zs cur1 k1) * (R + 1) + r) 0)
        (T.getD (codeL n m (newL n Zs cur2 k2) * (R + 1) + (r + J.p ⟨j, hjn⟩)) 0)) :
    ∀ t ≤ R, GoodF J R (ofList J (j :: Zs)) t →
      T'.getD (c * (R + 1) + t) 0 = dcap J W (ofList J (j :: Zs)) t := by
  subst hn
  have hTsl : SL J.jobs (m - 1) Zs := sl_tail hsl
  have hjZ : ∀ z ∈ Zs, j < z := by
    intro z hz
    have := List.sortedLT_iff_pairwise.mp hsl.sorted
    exact (List.pairwise_cons.mp this).1 z hz
  have hok1 : ScanOK J.jobs Zs (j + 1) (cur1, k1) := by
    have := scanF_ok J.jobs Zs (m - 1 - Zs.length) (j + 1) (List.sortedLT_iff_pairwise.mp hTsl.sorted)
      hTsl.lt (by omega)
    rw [show lstOf J.jobs (m - 1) Zs = Zs ++ List.replicate (m - 1 - Zs.length) J.jobs from rfl] at hs1
    rw [hs1] at this; exact this
  have hy0n : y0 ≤ J.jobs := by
    rcases hnx.1 with ⟨hy, -⟩ | rfl
    · exact hy.le
    · exact le_rfl
  have hjy : j < y0 := nxt_gt hest hq hjn hnx
  have hok2 : ScanOK J.jobs Zs y0 (cur2, k2) := by
    have := scanF_ok J.jobs Zs (m - 1 - Zs.length) y0 (List.sortedLT_iff_pairwise.mp hTsl.sorted)
      hTsl.lt hy0n
    rw [show lstOf J.jobs (m - 1) Zs = Zs ++ List.replicate (m - 1 - Zs.length) J.jobs from rfl] at hs2
    rw [hs2] at this; exact this
  have hsl1 := newL_sl hm hTsl hok1
  have hsl2 := newL_sl hm hTsl hok2
  have hc1 : c < codeL J.jobs m (newL J.jobs Zs cur1 k1) :=
    newcode_gt hm hsl hcode (by omega) (by omega) hs1
  have hc2 : c < codeL J.jobs m (newL J.jobs Zs cur2 k2) :=
    newcode_gt hm hsl hcode hjy hy0n hs2
  intro t ht hg
  rw [hcells t ht]
  have hjX : (⟨j, hjn⟩ : J.Job) ∈ ofList J (j :: Zs) := by rw [mem_ofList]; simp
  have hjmin : ∀ x ∈ ofList J (j :: Zs), (⟨j, hjn⟩ : J.Job) ≤ x := by
    intro x hx
    rw [mem_ofList] at hx
    rcases List.mem_cons.mp hx with h | h
    · exact Fin.mk_le_mk.mpr (by omega)
    · exact Fin.mk_le_mk.mpr (hjZ _ h).le
  have hX1 : X1 J (ofList J (j :: Zs)) ⟨j, hjn⟩ = ofList J (newL J.jobs Zs cur1 k1) :=
    X1_ofList (J := J) hjn hjZ (cur := cur1) (k := k1) hok1
  have hX2 : X2 J (ofList J (j :: Zs)) ⟨j, hjn⟩ = ofList J (newL J.jobs Zs cur2 k2) :=
    X2_ofList (J := J) hjn hjZ hest hnx (cur := cur2) (k := k2) hok2 hjy
  have hg1 : GoodF J R (ofList J (newL J.jobs Zs cur1 k1)) t := by
    rw [← hX1]; exact goodF_X1 hjX hjmin hg
  have hgt := goodF_step_le hjX hg
  have hg2 : GoodF J R (ofList J (newL J.jobs Zs cur2 k2)) (t + J.p ⟨j, hjn⟩) := by
    rw [← hX2]; exact goodF_X2 hest hq hjX hjmin hg
  refine dcell_list hest hq hjn hjZ hg hnx hok1 hok2 hjy ?_ ?_
  · exact hT.2.1 _ hsl1 (by omega) t ht hg1
  · intro _
    exact hT.2.1 _ hsl2 (by omega) (t + J.p ⟨j, hjn⟩) hgt hg2

end Lax496464Proofs.Ram.D4Tab
