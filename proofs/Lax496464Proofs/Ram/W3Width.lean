import Lax496464Proofs.Ram.W3SweepModel
import Lax496464Proofs.Ram.W3FrontX

/-!
# The Width of the Sorted Instance Is at Most the Width of the Word

`widthJ_le_widthOf`: for the instance `J = permute I f` the sorted instance is a re-indexing of,
`widthJ J ≤ widthOf x`; and the arrays: `SA` is `dueOrder J` (`sa_eq`).
-/

namespace Lax496464Proofs.Ram.W3Width

open Lax496464.FlowShop Lax496464.EstOrder Lax496464.WordEncoding Lax496464.Problems
open Lax496464.FlowShop.Instance (s HasWeight)
open Lax496464Proofs.Ram.W3Model Lax496464Proofs.Ram.W3Tab Lax496464Proofs.Ram.W3SweepModel
open Lax496464Proofs.Ram.EstPermute (permute)
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.Corollary1Prog (decision_word_facts)

theorem length_filter_range (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    ((List.range n).filter (fun i => decide (P i))).length =
      (Finset.univ.filter (fun k : Fin n => P k.val)).card := by
  rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter _)]
  refine Finset.card_bij (fun i hi => ⟨i, by
      have := List.mem_toFinset.mp hi
      simp at this; exact this.1⟩) ?_ ?_ ?_
  · intro i hi
    have := List.mem_toFinset.mp hi
    simp at this ⊢
    exact this.2
  · intro a _ b _ h
    simpa using h
  · intro k hk
    refine ⟨k.val, ?_, rfl⟩
    have hk' : P k.val := by simpa using hk
    simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨k.isLt, hk'⟩

open Classical in
theorem widthJ_le_widthOf {y : List ℕ} {I : Instance} (W : ℕ) (hEnc : EncodesInstance y I)
    (f : Fin I.jobs ≃ Fin I.jobs) : widthJ (permute I f) ≤ widthOf (y ++ [W]) := by
  obtain ⟨hjc, -, -, hqe, hde, -⟩ := decision_word_facts (W := W) hEnc
  unfold widthJ
  refine Finset.sup_le fun i _ => ?_
  -- the count at the job `f i` of `I`
  have hi : (i : ℕ) < I.jobs := i.isLt
  set fi : I.Job := f i with hfi
  have hmem : aliveAt (y ++ [W]) (start (y ++ [W]) fi.val) ≤ widthOf (y ++ [W]) := by
    unfold widthOf
    apply le_foldr_max
    exact List.mem_map.mpr ⟨fi.val, List.mem_range.mpr (by rw [hjc]; exact fi.isLt), rfl⟩
  refine le_trans (le_of_eq ?_) hmem
  unfold aliveAt
  rw [hjc, length_filter_range (fun k => start (y ++ [W]) k ≤ start (y ++ [W]) fi.val ∧
    start (y ++ [W]) fi.val < (due (y ++ [W]) k : ℤ)) I.jobs]
  symm
  have hst : ∀ k : I.Job, start (y ++ [W]) k.val = s (I := I) k := fun k => by
    simp only [start, s, hde k, hqe k]
  refine Finset.card_bij (fun k _ => f.symm k) ?_ ?_ ?_
  · intro k hk
    obtain ⟨-, hk⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hst k, hst fi, hde k] at hk
    have e1 : s (I := permute I f) (f.symm k) = s (I := I) k := by
      simp [s, permute]
    have e2 : s (I := permute I f) i = s (I := I) fi := by
      simp [s, permute, hfi]
    have e3 : ((permute I f).d (f.symm k) : ℤ) = (I.d k : ℤ) := by simp [permute]
    show s (I := permute I f) (f.symm k) ≤ s (I := permute I f) i ∧
      s (I := permute I f) i < ((permute I f).d (f.symm k) : ℤ)
    rw [e1, e2, e3]; exact hk
  · intro a _ b _ h
    exact f.symm.injective h
  · intro k hk
    obtain ⟨-, hk⟩ := Finset.mem_filter.mp hk
    refine ⟨f (show Fin I.jobs from k), ?_, f.symm_apply_apply _⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [hst (f (show Fin I.jobs from k)), hst fi, hde (f (show Fin I.jobs from k))]
    have e1 : s (I := permute I f) k = s (I := I) (f (show Fin I.jobs from k)) := by
      simp [s, permute]
    have e2 : s (I := permute I f) i = s (I := I) fi := by
      simp [s, permute, hfi]
    have e3 : ((permute I f).d k : ℤ) = (I.d (f (show Fin I.jobs from k)) : ℤ) := by
      simp [permute]
    have hk' : s (I := permute I f) k ≤ s (I := permute I f) i ∧
      s (I := permute I f) i < ((permute I f).d k : ℤ) := hk
    rw [e1, e2, e3] at hk'; exact hk'

/-! ## `SA` is `dueOrder J` -/

theorem sa_eq (J : Instance) (SA : List ℕ) (hperm : SA.Perm (List.range J.jobs))
    (hlex : SA.Pairwise (fun a b => dv J a < dv J b ∨ (dv J a = dv J b ∧ a < b))) :
    SA = (dueOrder J).map Fin.val := by
  have hp2 : ((dueOrder J).map Fin.val).Perm (List.range J.jobs) := by
    have := (dueOrder_perm J).map Fin.val
    refine this.trans ?_
    have hn : (scale J).jobs = J.jobs := rfl
    have : (List.finRange (scale J).jobs).map Fin.val = List.range (scale J).jobs := by
      apply List.ext_getElem <;> simp
    rw [this, hn]
  have hlex2 : ((dueOrder J).map Fin.val).Pairwise
      (fun a b => dv J a < dv J b ∨ (dv J a = dv J b ∧ a < b)) := by
    rw [List.pairwise_map]
    refine (dueOrder_pairwise J).imp ?_
    intro a b hab
    have hN : (Nsc J : ℤ) = (J.jobs : ℤ) + 1 := by unfold Nsc; push_cast; ring
    rw [sc_d J a, sc_d J b] at hab
    push_cast at hab
    have key := lin_lt (Nsc J) ((J.d a : ℤ) - J.d b) (a : ℕ) (b : ℕ) (by positivity)
      (by rw [hN]; exact_mod_cast Nat.lt_succ_of_lt a.isLt) (by positivity)
      (by rw [hN]; exact_mod_cast Nat.lt_succ_of_lt b.isLt)
    have e : (Nsc J : ℤ) * ((J.d a : ℤ) - J.d b) + (a : ℕ) < (b : ℕ) := by linarith
    have := key.mp e
    rw [dv_eq (J := J) a, dv_eq (J := J) b]
    rcases this with h | ⟨h, h'⟩
    · left; omega
    · right; exact ⟨by omega, by exact_mod_cast h'⟩
  refine List.Perm.eq_of_pairwise ?_ hlex hlex2 (hperm.trans hp2.symm)
  intro a b _ _ h1 h2
  omega

end Lax496464Proofs.Ram.W3Width
