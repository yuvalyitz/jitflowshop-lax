import Lax496464.WH_A4_MachineFacts
import Lax496464.WH_A5_Bridges
import Lax759944.TuringRamPolytimeEquivalence

/-! The bridges that follow from the two machine-level ones (`polyTimeOn_univ_iff` and
`fptTimeOn_of_strict`) and the archive's equivalence of the word RAM and the Turing machine. -/

namespace Lax496464Proofs.WHierarchy.BridgesDerived

open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax759944.TuringPolytime
open Lax888481.ParameterizedComplexity (Problem Decides)
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_A4_MachineFacts
open Lax496464.WH_A5_Bridges

/--
---
conclusion: Lax496464.WH_A5_Bridges.polyTimeOn_of_ramPolytime
---
-/
theorem polyTimeOn_of_ramPolytime {F : List ℕ → List ℕ} (D : Set (List ℕ)) :
    RamPolytime F → PolyTimeOn D F := fun h => by
  obtain ⟨p, c, d, hp⟩ := (polyTimeOn_univ_iff F).mpr h
  exact ⟨p, c, d, fun x _ => hp x (Set.mem_univ x)⟩

/--
---
conclusion: Lax496464.WH_A5_Bridges.polyTimeOn_of_turingPolytime
---
-/
theorem polyTimeOn_of_turingPolytime {F : List ℕ → List ℕ} (D : Set (List ℕ)) :
    TuringPolytime F → PolyTimeOn D F := fun h =>
  polyTimeOn_of_ramPolytime D
    ((Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime F).mpr h)

/--
---
conclusion: Lax496464.WH_A5_Bridges.fptReduces_of_polyTime
---
-/
theorem fptReduces_of_polyTime {P Q : Problem} {R : List ℕ → List ℕ} :
    IsReduction P Q R → ParamBounded P Q R → PolyTimeOn P.Domain R → P ≤ᶠᵖᵗ Q :=
  fun hR hB hT => ⟨R, hR, hB, fptTimeOn_of_polyTimeOn _ hT⟩

/--
---
conclusion: Lax496464.WH_A5_Bridges.fptReduces_of_strict
---
-/
theorem fptReduces_of_strict {P Q : Problem} {R : List ℕ → List ℕ} {prog : Program} {c : ℕ}
    {g h : ℕ → ℕ} (hr : Lax888481.ParameterizedComplexity.IsFptReduction P Q R prog c g h)
    (hg : Computable g) (hh : Computable h)
    (hout : ∃ (e : ℕ → ℕ) (d : ℕ), Computable e ∧
      ∀ x ∈ P.Domain, ∀ v ∈ R x, v < 2 ^ (e (P.param x) * (bitSize x + 1) ^ d)) :
    P ≤ᶠᵖᵗ Q :=
  ⟨R, ⟨hr.maps_domain, hr.correct⟩, ⟨h, hh, hr.param_le⟩, fptTimeOn_of_strict hg hr.time hout⟩

/--
---
conclusion: Lax496464.WH_A5_Bridges.mem_FPT_of_decides
---
-/
theorem mem_FPT_of_decides {P : Problem} {prog : Program} {c : ℕ} {g : ℕ → ℕ}
    (hP : IsParameterized P) (hg : Computable g) (hd : Decides P prog c g) : P ∈ FPT := by
  classical
  refine ⟨hP, fptTimeOn_of_strict hg (fun w x hx => hd w x ⟨hx.1, hx.2.1⟩)
    ⟨fun _ => 1, 0, Computable.const 1, fun x _ v hv => ?_⟩⟩
  split_ifs at hv <;> simp_all

end Lax496464Proofs.WHierarchy.BridgesDerived
