import Lax496464.WH_A5_Bridges
import Lax808846Proofs.Transfer

/-! From a program verified in IMP+ to polynomial or fixed-parameter time.

A program for a function `F` on the words of `D` is verified in IMP+ on the tapes
`x.length :: x` (`Tapes D`), computing `F` of the tail. `Solves` gives, at every word length at which
the layout and the value bound fit, a machine run; `WH_A5_Bridges.polyTimeOn_of_runsTo` (and its
fixed-parameter twin) turn runs within a bound, at word lengths from the bound on, into the time
notions of the submission. The work left to a caller is two inequalities per word: the value bound
and the span of the layout fit into `2 ^ bound`, and the compiled cost is within `bound`. -/

namespace Lax496464Proofs.WHierarchy.Machine.ImpBridge

open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax496464.WH_A1_FptTime Lax496464.WH_A5_Bridges

/-- The tapes of the words of `D`: each word with its length in front. -/
def Tapes (D : Set (List ℕ)) : Set (List ℕ) := {y | ∃ x ∈ D, y = x.length :: x}

theorem mem_tapes {D : Set (List ℕ)} {x : List ℕ} (hx : x ∈ D) : x.length :: x ∈ Tapes D :=
  ⟨x, hx, rfl⟩

/-- `Solves` restricts to a subset of the inputs. -/
theorem Solves.mono {L : Layout} {c : Com} {D D' : Set (List ℕ)} {f : List ℕ → List ℕ}
    {B K : List ℕ → ℕ} (h : Solves L c D f B K) (hD : D' ⊆ D) : Solves L c D' f B K :=
  ⟨h.ok, fun x hx => h.inp x (hD hx), fun x hx => h.run x (hD hx)⟩

/-- One run of the compiled program, at a word length at which this input's bound fits. -/
theorem runsTo_of_solves {L : Layout} {c : Com} {D : Set (List ℕ)} {f : List ℕ → List ℕ}
    {B K : List ℕ → ℕ} (h : Solves L c D f B K) {y : List ℕ} (hy : y ∈ D) {w : ℕ}
    (hfit : L.FitsWords (B y) w) :
    ∃ t ≤ L.const * K y + 1, RunsTo w (compileProgram L c) y (f y) t :=
  Solves.computesInTime (Solves.mono h (Set.singleton_subset_iff.mpr hy))
    (fun z hz => by rw [Set.mem_singleton_iff.mp hz]; exact hfit) y rfl

/-- The word-length hypothesis from one inequality against `2 ^ b` and `b ≤ w`. -/
theorem fitsWords_of_le {L : Layout} {Bv b w : ℕ} (h1 : 1 < Bv)
    (hB : max Bv (L.span Bv) ≤ 2 ^ b) (hw : b ≤ w) : L.FitsWords Bv w :=
  fitsWords_of_max_le h1 (hB.trans (Nat.pow_le_pow_right (by norm_num) hw))

/-- **Polynomial time from IMP+.** -/
theorem polyTimeOn_of_solves {L : Layout} {c : Com} {D : Set (List ℕ)} {F : List ℕ → List ℕ}
    {B K : List ℕ → ℕ} {c₀ d : ℕ}
    (h : Solves L c (Tapes D) (fun y => F y.tail) B K)
    (hB : ∀ x ∈ D, 1 < B (x.length :: x) ∧
      max (B (x.length :: x)) (L.span (B (x.length :: x))) ≤ 2 ^ (c₀ * (bitSize x + 1) ^ d))
    (hK : ∀ x ∈ D, L.const * K (x.length :: x) + 1 ≤ c₀ * (bitSize x + 1) ^ d)
    (hout : ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ (c₀ * (bitSize x + 1) ^ d)) :
    PolyTimeOn D F :=
  polyTimeOn_of_runsTo (p := compileProgram L c)
    (fun x hx w hw => by
      obtain ⟨t, ht, hr⟩ := runsTo_of_solves h (mem_tapes hx)
        (fitsWords_of_le (hB x hx).1 (hB x hx).2 hw)
      exact ⟨t, ht.trans (hK x hx), hr⟩) hout

/-- **Fixed-parameter time from IMP+.** -/
theorem fptTimeOn_of_solves {L : Layout} {c : Com} {D : Set (List ℕ)} {κ : List ℕ → ℕ}
    {F : List ℕ → List ℕ} {B K : List ℕ → ℕ} {f : ℕ → ℕ} {d : ℕ} (hf : Computable f)
    (h : Solves L c (Tapes D) (fun y => F y.tail) B K)
    (hB : ∀ x ∈ D, 1 < B (x.length :: x) ∧
      max (B (x.length :: x)) (L.span (B (x.length :: x))) ≤ 2 ^ fptBound f d (κ x) (bitSize x))
    (hK : ∀ x ∈ D, L.const * K (x.length :: x) + 1 ≤ fptBound f d (κ x) (bitSize x))
    (hout : ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ fptBound f d (κ x) (bitSize x)) :
    FptTimeOn D κ F :=
  fptTimeOn_of_runsTo (p := compileProgram L c) hf
    (fun x hx w hw => by
      obtain ⟨t, ht, hr⟩ := runsTo_of_solves h (mem_tapes hx)
        (fitsWords_of_le (hB x hx).1 (hB x hx).2 hw)
      exact ⟨t, ht.trans (hK x hx), hr⟩) hout

end Lax496464Proofs.WHierarchy.Machine.ImpBridge
