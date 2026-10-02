import Lax496464Proofs.Ram.F5Math
import Lax496464Proofs.Ram.EstPermute

/-!
# Theorem 5 (Profile Sweep): the Pure Layer the Machine Needs

The machine runs on the *sorted* instance `J = permute I σ`.  The number it writes is
`fptasOut J e`; this file shows it equals `fptasOut I e`, and reads the table off:
for `c ≤ W` the column `c` of the exact table is finite iff `HasWeight (scaled J e) c`, and the
largest such `c` is `scaledOpt`.
-/

namespace Lax496464Proofs.F5QMath

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.Ram.EstPermute

theorem fit_permute (I : Instance) (σ : Fin I.jobs → Fin I.jobs) (j : Fin I.jobs) :
    Fit (permute I σ) j ↔ Fit I (σ j) := Iff.rfl

theorem wmaxFit_permute (I : Instance) (σ : Fin I.jobs ≃ Fin I.jobs) :
    wmaxFit (permute I σ) = wmaxFit I := by
  apply le_antisymm
  · refine wmaxFit_le _ fun j hj => ?_
    exact le_wmaxFit I (j := σ j) hj
  · refine wmaxFit_le _ fun j hj => ?_
    have h1 : Fit (permute I σ) (σ.symm j) := by
      rw [fit_permute]; simpa using hj
    have h2 := le_wmaxFit (permute I σ) h1
    have : (permute I σ).w (σ.symm j) = I.w j := by
      show I.w (σ (σ.symm j)) = _
      simp
    rw [this] at h2
    exact h2

theorem scaleK_permute (I : Instance) (σ : Fin I.jobs ≃ Fin I.jobs) (e : ℕ) :
    scaleK (permute I σ) e = scaleK I e := by
  unfold scaleK
  rw [wmaxFit_permute]
  rfl

theorem scaled_permute (I : Instance) (σ : Fin I.jobs ≃ Fin I.jobs) (e : ℕ) :
    scaled (permute I σ) e = permute (scaled I e) σ := by
  have hw : ∀ j : Fin I.jobs, (scaled (permute I σ) e).w j = (scaled I e).w (σ j) := by
    intro j
    have h1 := scaled_w_eq (permute I σ) e j
    have h2 := scaled_w_eq I e (σ j)
    rw [scaleK_permute] at h1
    exact h1.trans h2.symm
  show (⟨I.jobs, I.machines, I.p ∘ σ, I.q ∘ σ, I.d ∘ σ, (scaled (permute I σ) e).w⟩ : Instance) =
    ⟨I.jobs, I.machines, I.p ∘ σ, I.q ∘ σ, I.d ∘ σ, (scaled I e).w ∘ σ⟩
  congr 1
  funext j
  exact hw j

theorem scaledOpt_permute (I : Instance) (σ : Fin I.jobs ≃ Fin I.jobs) (e : ℕ) :
    scaledOpt (permute I σ) e = scaledOpt I e := by
  unfold scaledOpt
  rw [scaled_permute]
  exact optimum_eq_of_hasWeight_iff (fun W => permute_hasWeight (scaled I e) (σ : Fin (scaled I e).jobs ≃ Fin (scaled I e).jobs) W)

theorem fptasOut_permute (I : Instance) (σ : Fin I.jobs ≃ Fin I.jobs) (e : ℕ) :
    fptasOut (permute I σ) e = fptasOut I e := by
  unfold fptasOut
  rw [scaleK_permute, scaledOpt_permute]
  rfl

end Lax496464Proofs.F5QMath
