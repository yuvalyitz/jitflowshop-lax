import Lax496464Proofs.Ram.EstSort
import Lax496464Proofs.Bridge
import Lax496464Proofs.Transport
import Lax496464.EstOrder

/-!
# What Sorting the Jobs Does to an Instance

The sort of `Ram/EstSort.lean` returns a permutation `P` of `0 … n−1`. Numbering the jobs by
`P` gives an instance that is the same shop — the answer to "is there a feasible set of weight
`W`" is unchanged, by `Transport` — and is in earliest-start-time order, which is what the
dynamic programs assume.
-/

namespace Lax496464Proofs.Ram.EstPermute

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.EstSort

/-- The instance with its jobs renumbered by `f`. -/
def permute (I : Instance) (f : Fin I.jobs → Fin I.jobs) : Instance where
  jobs := I.jobs
  machines := I.machines
  p k := I.p (f k)
  q k := I.q (f k)
  d k := I.d (f k)
  w k := I.w (f k)

theorem permute_hasWeight (I : Instance) (f : Fin I.jobs ≃ Fin I.jobs) (W : ℕ) :
    HasWeight (permute I f) W ↔ HasWeight I W := by
  rw [← Lax496464Proofs.Bridge.model_hasWeight, ← Lax496464Proofs.Bridge.model_hasWeight]
  let iso : Lax496464Proofs.Transport.Iso (Lax496464Proofs.Bridge.model I)
      (Lax496464Proofs.Bridge.model (permute I f)) :=
    { e := f.symm
      machines := rfl
      pre := fun x => congrArg I.p (f.apply_symm_apply x)
      proc := fun x => congrArg I.q (f.apply_symm_apply x)
      due := fun x => congrArg I.d (f.apply_symm_apply x)
      wt := fun x => congrArg I.w (f.apply_symm_apply x) }
  exact iso.hasWeight_iff W |>.symm

/-- A list that is a permutation of `0 … n−1` is a permutation of `Fin n`. -/
noncomputable def listEquiv (n : ℕ) (P : List ℕ) (h : P.Perm (List.range n)) : Fin n ≃ Fin n :=
  have hlen : P.length = n := by simpa using h.length_eq
  have hlt : ∀ k : Fin n, P.getD k 0 < n := fun k => by
    have : (k : ℕ) < P.length := by omega
    rw [List.getD_eq_getElem _ _ this]
    have := h.mem_iff.mp (List.getElem_mem this)
    simpa using this
  Equiv.ofBijective (fun k => ⟨P.getD k 0, hlt k⟩) (by
    have hnd : P.Nodup := h.nodup_iff.mpr (List.nodup_range)
    have hinj : Function.Injective (fun k : Fin n => (⟨P.getD k 0, hlt k⟩ : Fin n)) := by
      intro a b hab
      have hab' : P.getD a 0 = P.getD b 0 := congrArg Fin.val hab
      have ha : (a : ℕ) < P.length := by omega
      have hb : (b : ℕ) < P.length := by omega
      rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at hab'
      exact Fin.ext ((hnd.getElem_inj_iff).mp hab')
    exact hinj.bijective_of_finite)

theorem listEquiv_apply (n : ℕ) (P : List ℕ) (h : P.Perm (List.range n)) (k : Fin n) :
    ((listEquiv n P h k : Fin n) : ℕ) = P.getD k 0 := rfl

/-- **The sorted instance.** If `P` is a permutation of the job numbers that is sorted by
`rEst`, numbering the jobs by `P` gives an instance in earliest-start-time order that has a
feasible set of weight `W` exactly when the original does. -/
theorem est_sorted_instance (I : Instance) (A : List ℕ)
    (hd : ∀ (a : ℕ) (h : a < I.jobs), dA A I.jobs a = I.d ⟨a, h⟩)
    (hq : ∀ (a : ℕ) (h : a < I.jobs), qA A I.jobs a = I.q ⟨a, h⟩)
    (P : List ℕ) (hperm : P.Perm (List.range I.jobs)) (hsort : P.Pairwise (rEst A I.jobs)) :
    EstOrdered (permute I (listEquiv I.jobs P hperm)) ∧
      (∀ W, HasWeight (permute I (listEquiv I.jobs P hperm)) W ↔ HasWeight I W) := by
  refine ⟨?_, permute_hasWeight I _⟩
  have hlen : P.length = I.jobs := by simpa using hperm.length_eq
  intro (i : Fin I.jobs) (j : Fin I.jobs) hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · have hi : (i : ℕ) < P.length := by omega
    have hj : (j : ℕ) < P.length := by omega
    have hr := List.pairwise_iff_getElem.mp hsort i j hi hj hlt
    have hle := rEst_le hr
    have ei : ((listEquiv I.jobs P hperm i : Fin I.jobs) : ℕ) = P[i] :=
      (listEquiv_apply I.jobs P hperm i).trans (by rw [List.getD_eq_getElem _ _ hi]; rfl)
    have ej : ((listEquiv I.jobs P hperm j : Fin I.jobs) : ℕ) = P[j] :=
      (listEquiv_apply I.jobs P hperm j).trans (by rw [List.getD_eq_getElem _ _ hj]; rfl)
    have hdi := hd P[i] (by rw [← ei]; exact (listEquiv I.jobs P hperm i).isLt)
    have hqi := hq P[i] (by rw [← ei]; exact (listEquiv I.jobs P hperm i).isLt)
    have hdj := hd P[j] (by rw [← ej]; exact (listEquiv I.jobs P hperm j).isLt)
    have hqj := hq P[j] (by rw [← ej]; exact (listEquiv I.jobs P hperm j).isLt)
    have fi : (⟨P[i], by rw [← ei]; exact (listEquiv I.jobs P hperm i).isLt⟩ : Fin I.jobs)
        = listEquiv I.jobs P hperm i := Fin.ext ei.symm
    have fj : (⟨P[j], by rw [← ej]; exact (listEquiv I.jobs P hperm j).isLt⟩ : Fin I.jobs)
        = listEquiv I.jobs P hperm j := Fin.ext ej.symm
    rw [fi] at hdi hqi
    rw [fj] at hdj hqj
    show (I.d (listEquiv I.jobs P hperm i) : ℤ) - I.q (listEquiv I.jobs P hperm i) ≤
      (I.d (listEquiv I.jobs P hperm j) : ℤ) - I.q (listEquiv I.jobs P hperm j)
    rw [← hdi, ← hqi, ← hdj, ← hqj]
    exact hle

end Lax496464Proofs.Ram.EstPermute
