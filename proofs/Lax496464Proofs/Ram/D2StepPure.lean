import Lax496464Proofs.Ram.D2Tab
import Lax496464Proofs.Ram.D2Scan1

/-!
# Theorem 2, Pure Layer 7: What One Step of the Main Loop Establishes

`block_rep`: if the cells of the number `c` were computed as `max(T[c₁,r], f(T[c₂, r ∸ w_j]))` from
a table right at all numbers `> c`, they are right.  `valid_iff`: the machine's verdict.
-/

namespace Lax496464Proofs.Ram.D2StepPure

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.DynamicProgram
open Lax496464Proofs.Ram.DpCore Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan
open Lax496464Proofs.Ram.D2Valid Lax496464Proofs.Ram.D2Ach Lax496464Proofs.Ram.D2Tab
open Lax496464Proofs.Ram.Dp1 (IsNxt nxt_gt fNat)

theorem block_rep {J : Instance} {m W inf N c j : ℕ} {Zs : List ℕ} {T T' : List ℕ}
    (_hN : N = (J.jobs + 1) ^ m) (hm : 1 ≤ m)
    (hest : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) (hi1 : 1 < inf)
    (hinf : ∀ i : J.Job, s i + 1 < inf)
    (hT : TabOK J J.jobs m W inf N (c + 1) T)
    (hsl : SL J.jobs m (j :: Zs)) (hcode : codeL J.jobs m (j :: Zs) = c)
    (hjn : j < J.jobs) {y0 : ℕ} (hnx : IsNxt j hjn y0)
    {cur1 k1 cur2 k2 : ℕ}
    (hs1 : scanF J.jobs (lstOf J.jobs (m - 1) Zs) (j + 1) = (cur1, k1))
    (hs2 : scanF J.jobs (lstOf J.jobs (m - 1) Zs) y0 = (cur2, k2))
    (hcells : ∀ r, r ≤ W → T'.getD (c * (W + 1) + r) 0 =
      max (T.getD (codeL J.jobs m (newL J.jobs Zs cur1 k1) * (W + 1) + r) 0)
        (fNat inf (T.getD (codeL J.jobs m (newL J.jobs Zs cur2 k2) * (W + 1) + (r - J.w ⟨j, hjn⟩)) 0)
          (J.d ⟨j, hjn⟩) (J.q ⟨j, hjn⟩) (J.p ⟨j, hjn⟩))) :
    ∀ r ≤ W, Rep inf (T'.getD (c * (W + 1) + r) 0)
      (fun P' => AchGe J (ofList J (j :: Zs)) r P') := by
  have hTsl : SL J.jobs (m - 1) Zs := sl_tail hsl
  have hjn' : j < J.jobs := hjn
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
    rw [← hcode]; exact code_lt hm hTsl hjn' hjZ hok1 (by omega)
  have hc2 : c < codeL J.jobs m (newL J.jobs Zs cur2 k2) := by
    rw [← hcode]; exact code_lt hm hTsl hjn' hjZ hok2 (by omega)
  have hX1 : X1 J (ofList J (j :: Zs)) ⟨j, hjn⟩ = ofList J (newL J.jobs Zs cur1 k1) := by
    have := X1_ofList (J := J) hjn hjZ (cur := cur1) (k := k1) hok1
    exact this
  have hX2 : X2 J (ofList J (j :: Zs)) ⟨j, hjn⟩ = ofList J (newL J.jobs Zs cur2 k2) := by
    have := X2_ofList (J := J) hjn hjZ hest hnx (cur := cur2) (k := k2) hok2 hjy
    exact this
  intro r hr
  rw [hcells r hr]
  have hjX : (⟨j, hjn⟩ : J.Job) ∈ ofList J (j :: Zs) := by rw [mem_ofList]; simp
  have hjmin : ∀ x ∈ ofList J (j :: Zs), (⟨j, hjn⟩ : J.Job) ≤ x := by
    intro x hx
    rw [mem_ofList] at hx
    rcases List.mem_cons.mp hx with h | h
    · exact le_of_eq (Fin.ext h.symm)
    · exact Fin.mk_le_of_le_val (by have := hjZ _ h; simp; omega)
  have hidx1 : codeL J.jobs m (newL J.jobs Zs cur1 k1) * (W + 1) + r ≥ 0 := Nat.zero_le _
  have h1 := hT.2.1 (newL J.jobs Zs cur1 k1) hsl1 (by omega) r hr
  have h2 := hT.2.1 (newL J.jobs Zs cur2 k2) hsl2 (by omega) (r - J.w ⟨j, hjn⟩) (by omega)
  rw [← hX1] at h1
  rw [← hX2] at h2
  exact cell_rep hest hq hi1 hinf hjX hjmin r _ _ h1 h2


theorem block_rep' {J : Instance} {n m W inf N c j : ℕ} {Zs : List ℕ} {T T' : List ℕ}
    (hn : J.jobs = n) (hN : N = (n + 1) ^ m) (hm : 1 ≤ m)
    (hest : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) (hi1 : 1 < inf)
    (hinf : ∀ i : J.Job, s i + 1 < inf)
    (hT : TabOK J n m W inf N (c + 1) T)
    (hsl : SL n m (j :: Zs)) (hcode : codeL n m (j :: Zs) = c)
    (hjn : j < J.jobs) {y0 : ℕ} (hnx : IsNxt j hjn y0)
    {cur1 k1 cur2 k2 : ℕ}
    (hs1 : scanF n (lstOf n (m - 1) Zs) (j + 1) = (cur1, k1))
    (hs2 : scanF n (lstOf n (m - 1) Zs) y0 = (cur2, k2))
    (hcells : ∀ r, r ≤ W → T'.getD (c * (W + 1) + r) 0 =
      max (T.getD (codeL n m (newL n Zs cur1 k1) * (W + 1) + r) 0)
        (fNat inf (T.getD (codeL n m (newL n Zs cur2 k2) * (W + 1) + (r - J.w ⟨j, hjn⟩)) 0)
          (J.d ⟨j, hjn⟩) (J.q ⟨j, hjn⟩) (J.p ⟨j, hjn⟩))) :
    ∀ r ≤ W, Rep inf (T'.getD (c * (W + 1) + r) 0)
      (fun P' => AchGe J (ofList J (j :: Zs)) r P') := by
  subst hn
  exact block_rep hN hm hest hq hi1 hinf hT hsl hcode hjn hnx hs1 hs2 hcells

theorem newcode_gt {n m j c y : ℕ} {Zs : List ℕ} {cur k : ℕ} (hm : 1 ≤ m)
    (hsl : SL n m (j :: Zs)) (hcode : codeL n m (j :: Zs) = c) (hy : j < y) (hyn : y ≤ n)
    (hs : scanF n (lstOf n (m - 1) Zs) y = (cur, k)) :
    c < codeL n m (newL n Zs cur k) := by
  have hTsl : SL n (m - 1) Zs := sl_tail hsl
  have hjn : j < n := hsl.lt j (by simp)
  have hjZ : ∀ z ∈ Zs, j < z := by
    intro z hz
    have := List.sortedLT_iff_pairwise.mp hsl.sorted
    exact (List.pairwise_cons.mp this).1 z hz
  have hok : ScanOK n Zs y (cur, k) := by
    have := scanF_ok n Zs (m - 1 - Zs.length) y (List.sortedLT_iff_pairwise.mp hTsl.sorted)
      hTsl.lt hyn
    have h2 : lstOf n (m - 1) Zs = Zs ++ List.replicate (m - 1 - Zs.length) n := rfl
    rw [← h2, hs] at this; exact this
  rw [← hcode]
  exact code_lt hm hTsl hjn hjZ hok hy

theorem x1_cons {n m j : ℕ} {Zs : List ℕ} (hm : 1 ≤ m) (hsl : SL n m (j :: Zs)) :
    x1 n m (codeL n m (j :: Zs)) = j := by
  have hTsl : SL n (m - 1) Zs := sl_tail hsl
  have hb0 : 0 < n + 1 := by omega
  have hc : codeL n m (j :: Zs) = enc (n + 1) (j :: lstOf n (m - 1) Zs) := by
    unfold codeL; rw [lstOf_cons hm hTsl.len]
  have hlt' : enc (n + 1) (lstOf n (m - 1) Zs) < (n + 1) ^ (m - 1) := by
    have := enc_lt hTsl.lstOf_lt
    rwa [hTsl.lstOf_length] at this
  have hdm := div_mod_pow (n + 1) j (enc (n + 1) (lstOf n (m - 1) Zs)) (m - 1) hb0 hlt'
  unfold x1
  rw [hc, enc_cons, hTsl.lstOf_length]
  exact hdm.1

theorem valid_iff {n m N c : ℕ} {V : List ℕ} (hm : 1 ≤ m) (hN : N = (n + 1) ^ m)
    (hc : c + 1 < N) (hV : ValidOK n m N (c + 1) V) :
    (x1 n m c < x2 n m c ∧ V.getD (sufc n m c) 0 = 1) ↔ IsCode n m c := by
  classical
  have hcN : c < (n + 1) ^ m := by omega
  have hne : c ≠ top n m := by unfold top; omega
  rw [isCode_iff hm hcN]
  constructor
  · rintro ⟨hlt, hv⟩
    right
    refine ⟨hlt, ?_⟩
    have hsg := sufc_gt hm hlt
    have hsl : sufc n m c < N := hN ▸ sufc_lt_pow hm
    have := hV.2.1 (sufc n m c) (by omega) hsl
    rw [this] at hv
    by_contra hnc
    rw [if_neg hnc] at hv
    omega
  · rintro (h | ⟨hlt, hcode⟩)
    · exact absurd h hne
    · refine ⟨hlt, ?_⟩
      have hsg := sufc_gt hm hlt
      have hsl : sufc n m c < N := hN ▸ sufc_lt_pow hm
      rw [hV.2.1 (sufc n m c) (by omega) hsl, if_pos hcode]

end Lax496464Proofs.Ram.D2StepPure
