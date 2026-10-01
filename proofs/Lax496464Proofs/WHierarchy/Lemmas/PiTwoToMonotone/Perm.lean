import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Semantics

/-! # Isolated elements are interchangeable: satisfaction

`Lemmas/WDToWSat/Perm` shows that a permutation of the numbers fixing every active element
preserves the atoms; here the same for the satisfaction of a quantifier-free formula
(`sat_perm`), which is what the `Π₂` compression argument needs. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Perm

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Perm (Active imgS fix_of_active map_fix_of_mem mem_imgS)

section
variable {A : Structure} {π : Equiv.Perm ℕ}

/-- **A permutation fixing the active elements is an automorphism**: a quantifier-free formula holds
under `ρ` with `X := S` iff it holds under `π ∘ ρ` with `X := π(S)`. -/
theorem sat_perm (hπ : ∀ e, Active A e → π e = e) (S : Set (List ℕ)) :
    ∀ (ψ : Formula) (ρ : ℕ → ℕ), ψ.IsQF → (Sat A S ψ ρ ↔ Sat A (imgS π S) ψ (π ∘ ρ))
  | .rel i js, ρ, _ => by
    simp only [Sat]
    rw [← List.map_map]
    constructor
    · intro h; rw [map_fix_of_mem hπ h]; exact h
    · intro h
      have : (js.map ρ).map π = js.map ρ := by
        conv_rhs => rw [← List.map_id (js.map ρ)]
        refine List.map_congr_left fun e he => ?_
        exact fix_of_active hπ ⟨i, _, h, List.mem_map_of_mem he⟩
      rwa [this] at h
  | .eq a b, ρ, _ => by
    simp only [Sat, Function.comp]
    exact ⟨fun h => by rw [h], fun h => π.injective h⟩
  | .setVar js, ρ, _ => by
    simp only [Sat]
    rw [← List.map_map, mem_imgS]
  | .neg φ, ρ, hq => by
    simp only [Sat]; rw [sat_perm hπ S φ ρ hq]
  | .and φ ψ, ρ, hq => by
    simp only [Sat]; rw [sat_perm hπ S φ ρ hq.1, sat_perm hπ S ψ ρ hq.2]
  | .or φ ψ, ρ, hq => by
    simp only [Sat]; rw [sat_perm hπ S φ ρ hq.1, sat_perm hπ S ψ ρ hq.2]
  | .ex _ _, _, hq => absurd hq (by simp [Formula.IsQF])
  | .all _ _, _, hq => absurd hq (by simp [Formula.IsQF])

end

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Perm
