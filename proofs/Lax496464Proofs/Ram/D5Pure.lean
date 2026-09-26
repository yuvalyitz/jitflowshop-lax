import Lax496464Proofs.Ram.D3Cor3
import Lax496464Proofs.Ram.D2StepPure

/-!
# Corollary 3's machine, part 2: the table invariant and what one block establishes

`UTab` is `D3Cor3.UTabOK` together with the bound `≤ W` on every entry (the machine adds
`w_j + T[..]` and must not overflow, also on cells that are not good).  `ublock` is
`D2StepPure.block_rep'` for the dual table.
-/

namespace Lax496464Proofs.Ram.D5Pure

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan Lax496464Proofs.Ram.D2Valid
open Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab Lax496464Proofs.Ram.D3Dual
open Lax496464Proofs.Ram.D3Cor3 Lax496464Proofs.Ram.D2StepPure
open Lax496464Proofs.Ram.Dp1 (IsNxt nxt_gt)

/-- The table invariant of the machine. -/
def UTab (J : Instance) (n m W p N thr : ℕ) (T : List ℕ) : Prop :=
  UTabOK J n m W p N thr T ∧ ∀ i, T.getD i 0 ≤ W

theorem utab_init (J : Instance) (n m W p : ℕ) :
    UTab J n m W p ((n + 1) ^ m) ((n + 1) ^ m)
      (List.replicate ((n + 1) ^ m * (n + 1)) 0) := by
  refine ⟨⟨by simp, ?_, ?_⟩, ?_⟩
  · intro Zs hsl h
    have := hsl.codeL_lt
    omega
  · intro i hi _
    simp [hi]
  · intro i
    by_cases hi : i < (n + 1) ^ m * (n + 1)
    · simp [hi]
    · simp [List.getD_eq_getElem?_getD, hi]

theorem utab_step_empty' {J : Instance} {n m W p N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hc : c = N - 1) (hT : UTab J n m W p N (c + 1) T) : UTab J n m W p N c T :=
  ⟨utab_step_empty hN hc hT.1, hT.2⟩

theorem utab_step_invalid' {J : Instance} {n m W p N c : ℕ} {T : List ℕ} (hN : N = (n + 1) ^ m)
    (hnc : ¬ IsCode n m c) (hT : UTab J n m W p N (c + 1) T) : UTab J n m W p N c T :=
  ⟨utab_step_invalid hN hnc hT.1, hT.2⟩

theorem utab_step' {J : Instance} {n m W p N c : ℕ} {T T' : List ℕ} (hN : N = (n + 1) ^ m)
    (hT : UTab J n m W p N (c + 1) T) (hlen : T'.length = N * (n + 1))
    (hout : ∀ i, i < N * (n + 1) → i / (n + 1) ≠ c → T'.getD i 0 = T.getD i 0)
    (hblock : ∀ Zs, SL n m Zs → codeL n m Zs = c → ∀ u ≤ n, GoodU J (ofList J Zs) u →
      T'.getD (c * (n + 1) + u) 0 = dcap J W (ofList J Zs) (u * p))
    (hle : ∀ i, T'.getD i 0 ≤ W) : UTab J n m W p N c T' :=
  ⟨utab_step hN hT.1 hlen hout hblock, hle⟩

/-- **One block of the dual table.** -/
theorem ublock {J : Instance} {n m W p N c j : ℕ} {Zs : List ℕ} {T T' : List ℕ}
    (hn : J.jobs = n) (hm : 1 ≤ m)
    (hest : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) (hp : ∀ i : J.Job, J.p i = p)
    (hT : UTabOK J n m W p N (c + 1) T)
    (hsl : SL n m (j :: Zs)) (hcode : codeL n m (j :: Zs) = c)
    (hjn : j < J.jobs) {y0 : ℕ} (hnx : IsNxt j hjn y0)
    {cur1 k1 cur2 k2 : ℕ}
    (hs1 : scanF n (lstOf n (m - 1) Zs) (j + 1) = (cur1, k1))
    (hs2 : scanF n (lstOf n (m - 1) Zs) y0 = (cur2, k2))
    (hcells : ∀ u, u ≤ n → T'.getD (c * (n + 1) + u) 0 =
      dStepU W n p (J.q ⟨j, hjn⟩) (J.d ⟨j, hjn⟩) (J.w ⟨j, hjn⟩) u
        (T.getD (codeL n m (newL n Zs cur1 k1) * (n + 1) + u) 0)
        (T.getD (codeL n m (newL n Zs cur2 k2) * (n + 1) + (u + 1)) 0)) :
    ∀ u ≤ n, GoodU J (ofList J (j :: Zs)) u →
      T'.getD (c * (n + 1) + u) 0 = dcap J W (ofList J (j :: Zs)) (u * p) := by
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
  have hc1 : c < codeL J.jobs m (newL J.jobs Zs cur1 k1) := by
    rw [← hcode]; exact code_lt hm hTsl hjn hjZ hok1 (by omega)
  have hc2 : c < codeL J.jobs m (newL J.jobs Zs cur2 k2) := by
    rw [← hcode]; exact code_lt hm hTsl hjn hjZ hok2 (by omega)
  have hX1 : X1 J (ofList J (j :: Zs)) ⟨j, hjn⟩ = ofList J (newL J.jobs Zs cur1 k1) :=
    X1_ofList (J := J) hjn hjZ (cur := cur1) (k := k1) hok1
  have hX2 : X2 J (ofList J (j :: Zs)) ⟨j, hjn⟩ = ofList J (newL J.jobs Zs cur2 k2) :=
    X2_ofList (J := J) hjn hjZ hest hnx (cur := cur2) (k := k2) hok2 hjy
  have hjX : (⟨j, hjn⟩ : J.Job) ∈ ofList J (j :: Zs) := by rw [mem_ofList]; simp
  have hjmin : ∀ x ∈ ofList J (j :: Zs), (⟨j, hjn⟩ : J.Job) ≤ x := by
    intro x hx
    rw [mem_ofList] at hx
    rcases List.mem_cons.mp hx with h | h
    · exact le_of_eq (Fin.ext h.symm)
    · exact Fin.mk_le_of_le_val (by have := hjZ _ h; simp; omega)
  intro u hu hg
  rw [hcells u hu]
  have hg1 : GoodU J (ofList J (newL J.jobs Zs cur1 k1)) u := by
    rw [← hX1]; exact goodU_X1 hjX hjmin hg
  have hg2 : GoodU J (ofList J (newL J.jobs Zs cur2 k2)) (u + 1) := by
    rw [← hX2]; exact goodU_X2 hest hq hjX hjmin hg
  have hu1 := goodU_step_le hjX hg
  have h1 := hT.2.1 (newL J.jobs Zs cur1 k1) hsl1 (by omega) u hu hg1
  have h2 := hT.2.1 (newL J.jobs Zs cur2 k2) hsl2 (by omega) (u + 1) hu1 hg2
  exact dcellU_list hest hq hp hjn hjZ hg hnx hok1 hok2 hjy h1 (fun _ => h2)

end Lax496464Proofs.Ram.D5Pure
