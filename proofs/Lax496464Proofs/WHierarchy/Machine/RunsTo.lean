import Lax496464.WH_A5_Bridges
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-! From runs of a program on the prefixed tape to fixed-parameter time: raising the bound by the bit
size makes the input part of the fitting condition automatic. -/

namespace Lax496464Proofs.WHierarchy.Machine.RunsTo

open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax496464.WH_A1_FptTime Lax496464Proofs.WHierarchy.Machine.SizeFacts

theorem le_raise (a n d : ℕ) : a * (n + 1) ^ d ≤ (a + 1) * (n + 1) ^ (d + 1) := by
  have h1 : (n + 1) ^ d ≤ (n + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  calc a * (n + 1) ^ d ≤ (a + 1) * (n + 1) ^ d := Nat.mul_le_mul_right _ (by omega)
    _ ≤ (a + 1) * (n + 1) ^ (d + 1) := Nat.mul_le_mul_left _ h1

theorem succ_le_raise (a n d : ℕ) : n + 1 ≤ (a + 1) * (n + 1) ^ (d + 1) := by
  have h1 : n + 1 ≤ (n + 1) ^ (d + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  calc n + 1 ≤ (n + 1) ^ (d + 1) := h1
    _ ≤ (a + 1) * (n + 1) ^ (d + 1) := Nat.le_mul_of_pos_left _ (by omega)

/-- The input part of the fitting condition, at any bound above the bit size. -/
theorem fits_tape {x : List ℕ} {B : ℕ} (hB : bitSize x + 1 ≤ B) :
    FitsInWords B (x.length :: x) := by
  intro a ha
  have hn : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
  have hmono : 2 ^ bitSize x ≤ 2 ^ B := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases List.mem_cons.mp ha with rfl | ha
  · exact lt_of_le_of_lt (length_le_bitSize x) (lt_of_lt_of_le hn hmono)
  · exact lt_of_lt_of_le (lt_two_pow_bitSize ha) hmono

/-- The common core: runs within a bound `b ≤ B` at every word length `w ≥ b`, outputs of at most
`b` bits, and `B` above the bit size give the definition at `B`. -/
theorem computes_of_runsTo {p : Program} {D : Set (List ℕ)} {κ : List ℕ → ℕ}
    {F : List ℕ → List ℕ} {f : ℕ → ℕ} {d : ℕ} (b : List ℕ → ℕ)
    (hb : ∀ x ∈ D, b x ≤ fptBound f d (κ x) (bitSize x))
    (hn : ∀ x ∈ D, bitSize x + 1 ≤ fptBound f d (κ x) (bitSize x))
    (hrun : ∀ x ∈ D, ∀ w : ℕ, b x ≤ w → ∃ t ≤ b x, RunsTo w p (x.length :: x) (F x) t)
    (hout : ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ b x) :
    ComputesInFptTime p D κ F f d := by
  intro x hx
  refine ⟨?_, fun w hw => ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact fits_tape (hn x hx) a ha
    · exact lt_of_lt_of_le (hout x hx a ha) (Nat.pow_le_pow_right (by norm_num) (hb x hx))
  · obtain ⟨t, ht, hr⟩ := hrun x hx w ((hb x hx).trans hw)
    exact ⟨t, ht.trans (hb x hx), hr⟩

/--
---
conclusion: Lax496464.WH_A5_Bridges.fptTimeOn_of_runsTo
---
-/
theorem fptTimeOn_of_runsTo {D : Set (List ℕ)} {κ : List ℕ → ℕ} {F : List ℕ → List ℕ}
    {p : Program} {f : ℕ → ℕ} {d : ℕ} (hf : Computable f)
    (hrun : ∀ x ∈ D, ∀ w : ℕ, fptBound f d (κ x) (bitSize x) ≤ w →
      ∃ t ≤ fptBound f d (κ x) (bitSize x), RunsTo w p (x.length :: x) (F x) t)
    (hout : ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ fptBound f d (κ x) (bitSize x)) :
    FptTimeOn D κ F :=
  ⟨p, fun k => f k + 1, d + 1, Primrec.nat_add.to_comp.comp hf (Computable.const 1),
    computes_of_runsTo _ (fun _ _ => le_raise _ _ _) (fun _ _ => succ_le_raise _ _ _) hrun hout⟩

/--
---
conclusion: Lax496464.WH_A5_Bridges.polyTimeOn_of_runsTo
---
-/
theorem polyTimeOn_of_runsTo {D : Set (List ℕ)} {F : List ℕ → List ℕ} {p : Program} {c d : ℕ}
    (hrun : ∀ x ∈ D, ∀ w : ℕ, c * (bitSize x + 1) ^ d ≤ w →
      ∃ t ≤ c * (bitSize x + 1) ^ d, RunsTo w p (x.length :: x) (F x) t)
    (hout : ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ (c * (bitSize x + 1) ^ d)) :
    PolyTimeOn D F :=
  ⟨p, c + 1, d + 1,
    computes_of_runsTo (f := fun _ => c + 1) (κ := fun _ => 0) (fun x => c * (bitSize x + 1) ^ d)
      (fun _ _ => le_raise _ _ _) (fun _ _ => succ_le_raise _ _ _) hrun hout⟩

end Lax496464Proofs.WHierarchy.Machine.RunsTo
