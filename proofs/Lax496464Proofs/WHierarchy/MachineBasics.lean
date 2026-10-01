import Lax496464.WH_A4_MachineFacts

/-! The machine facts that are immediate from the definition of fixed-parameter time. -/

namespace Lax496464Proofs.WHierarchy.MachineBasics

open Lax496464.WH_A1_FptTime

/--
---
conclusion: Lax496464.WH_A4_MachineFacts.fptTimeOn_mono
---
-/
theorem fptTimeOn_mono {D D' : Set (List ℕ)} {κ : List ℕ → ℕ} {F : List ℕ → List ℕ} :
    D' ⊆ D → FptTimeOn D κ F → FptTimeOn D' κ F :=
  fun hD ⟨p, f, d, hf, h⟩ => ⟨p, f, d, hf, fun x hx => h x (hD hx)⟩

/--
---
conclusion: Lax496464.WH_A4_MachineFacts.fptTimeOn_congr
---
-/
theorem fptTimeOn_congr {D : Set (List ℕ)} {κ : List ℕ → ℕ} {F G : List ℕ → List ℕ} :
    (∀ x ∈ D, F x = G x) → FptTimeOn D κ F → FptTimeOn D κ G :=
  fun hFG ⟨p, f, d, hf, h⟩ => ⟨p, f, d, hf, fun x hx => hFG x hx ▸ h x hx⟩

/--
---
conclusion: Lax496464.WH_A4_MachineFacts.fptTimeOn_of_polyTimeOn
---
-/
theorem fptTimeOn_of_polyTimeOn {D : Set (List ℕ)} {F : List ℕ → List ℕ} (κ : List ℕ → ℕ) :
    PolyTimeOn D F → FptTimeOn D κ F :=
  fun ⟨p, c, d, h⟩ => ⟨p, fun _ => c, d, Computable.const c, h⟩

end Lax496464Proofs.WHierarchy.MachineBasics
