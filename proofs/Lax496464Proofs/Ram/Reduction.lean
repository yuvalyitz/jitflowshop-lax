import Lax496464Proofs.Ram.InstanceWord
import Lax496464Proofs.Section8
import Lax496464.Corollary4

/-!
# Section 8's construction as a map on words

The mathematics of the reduction is `Section8.construct_correct`; what is added here is the
passage to words. A Hitting Set word determines its instance and its solution size — that is
`encodes_unique` — so the map that sends it to the word of the constructed shop, with the
target as threshold, is well defined, and the two questions agree by `construct_correct`.

Nothing here is about a machine. The word RAM program that computes this map, and its
running time, are elsewhere.
-/

namespace Lax496464Proofs.Ram.Reduction

open Lax496464.HittingSet Lax496464.Construction Lax496464.WordEncoding
open Lax496464.FlowShop Lax496464Proofs.Ram.InstanceWord

/-! ## 1. A word determines what it encodes -/

theorem encodes_unique {x : List ℕ} {P P' : Lax496464.HittingSet.Instance} {k k' : ℕ}
    (h : Encodes x P k) (h' : Encodes x P' k') : P = P' ∧ k = k' := by
  refine ⟨?_, h.solutionSize_eq.symm.trans h'.solutionSize_eq⟩
  obtain ⟨n, m, F⟩ := P
  obtain ⟨n', m', F'⟩ := P'
  have hn : n = n' := h.universeSize_eq.symm.trans h'.universeSize_eq
  have hm : m = m' := h.setCount_eq.symm.trans h'.setCount_eq
  subst hn
  subst hm
  congr 1
  funext j
  ext i
  rw [h.mem_iff j i, h'.mem_iff j i]

theorem encodesInstance_unique {y : List ℕ} {I I' : Lax496464.FlowShop.Instance}
    (h : EncodesInstance y I) (h' : EncodesInstance y I') : I = I' := by
  obtain ⟨n, m, p, q, d, w⟩ := I
  obtain ⟨n', m', p', q', d', w'⟩ := I'
  have hn : n = n' := h.jobCount_eq.symm.trans h'.jobCount_eq
  have hm : m = m' := h.machineCount_eq.symm.trans h'.machineCount_eq
  subst hn
  subst hm
  congr 1 <;> funext j
  · exact (h.preTime_eq j).symm.trans (h'.preTime_eq j)
  · exact (h.procTime_eq j).symm.trans (h'.procTime_eq j)
  · exact (h.due_eq j).symm.trans (h'.due_eq j)
  · exact (h.wt_eq j).symm.trans (h'.wt_eq j)

theorem encodesDecisionInstance_unique {y : List ℕ} {I I' : Lax496464.FlowShop.Instance}
    {W W' : ℕ} (h : EncodesDecisionInstance y I W) (h' : EncodesDecisionInstance y I' W') :
    I = I' ∧ W = W' := by
  obtain ⟨z, hz, hI⟩ := h
  obtain ⟨z', hz', hI'⟩ := h'
  have hW : W = W' := by
    have := hz.symm.trans hz'
    simpa using congrArg List.getLast? this
  subst hW
  have hzz : z = z' := by
    have := hz.symm.trans hz'
    exact List.append_cancel_right this
  subst hzz
  exact ⟨encodesInstance_unique hI hI', rfl⟩

/-! ## 2. The map -/

open Classical in
/-- The word of the shop Section 8 builds from the Hitting Set word `x`, with the target as
threshold. -/
noncomputable def red (x : List ℕ) : List ℕ :=
  if h : ∃ P : Lax496464.HittingSet.Instance, ∃ k, Encodes x P k then
    decisionWord (construct h.choose (solutionSize x)) (target h.choose (solutionSize x))
  else []

theorem red_eq {x : List ℕ} {P : Lax496464.HittingSet.Instance} {k : ℕ} (h : Encodes x P k) :
    red x = decisionWord (construct P k) (target P k) := by
  classical
  have hex : ∃ P : Lax496464.HittingSet.Instance, ∃ k, Encodes x P k := ⟨P, k, h⟩
  have hc := hex.choose_spec
  obtain ⟨k₀, hk₀⟩ := hc
  have huniq := encodes_unique hk₀ h
  rw [red, dif_pos hex, huniq.1, h.solutionSize_eq]

/-! ## 3. The three facts a reduction owes, apart from its running time -/

open Lax496464.Problems Lax496464.ParameterizedComplexity

theorem red_mem_domain {x : List ℕ} (hx : x ∈ byK.Domain) : red x ∈ byMachines.Domain := by
  obtain ⟨P, k, h⟩ := hx
  rw [red_eq h]
  exact decisionWord_mem_decisionInstances _

theorem red_param_eq {x : List ℕ} (hx : x ∈ byK.Domain) :
    byMachines.param (red x) = byK.param x := by
  obtain ⟨P, k, h⟩ := hx
  rw [show byMachines.param (red x) = machineCount (red x) from rfl, red_eq h,
    machineCount_decisionWord]
  exact (rfl : (construct P k).machines = k).trans h.solutionSize_eq.symm

theorem red_correct {x : List ℕ} (hx : x ∈ byK.Domain) :
    byK.Yes x ↔ byMachines.Yes (red x) := by
  obtain ⟨P, k, h⟩ := hx
  have hk := h.size_bounds
  constructor
  · rintro ⟨P', k', h', hHS⟩
    obtain ⟨rfl, rfl⟩ := encodes_unique h' h
    exact ⟨construct P' k', target P' k',
      by rw [red_eq h']; exact encodesDecisionInstance_decisionWord _,
      (Section8.construct_correct P' k' hk.1 hk.2).mp hHS⟩
  · rintro ⟨I, W, hEnc, hHW⟩
    rw [red_eq h] at hEnc
    obtain ⟨rfl, rfl⟩ :=
      encodesDecisionInstance_unique hEnc (encodesDecisionInstance_decisionWord (I := construct P k) _)
    exact ⟨P, k, h, (Section8.construct_correct P k hk.1 hk.2).mpr hHW⟩

end Lax496464Proofs.Ram.Reduction
