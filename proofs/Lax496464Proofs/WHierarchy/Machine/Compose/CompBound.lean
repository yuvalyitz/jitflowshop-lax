import Lax496464Proofs.WHierarchy.Machine.Compose.Programs
import Lax496464Proofs.WHierarchy.Machine.RunsTo
import Lax496464Proofs.WHierarchy.ComputableBounds

/-! Fixed-parameter computations compose: the program `compose p1 p2` within a fixed-parameter
bound. -/

namespace Lax496464Proofs.WHierarchy.Machine.Compose.CompBound

open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime
open Lax496464.WH_A1_FptTime
open Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics Lax496464Proofs.WHierarchy.Machine.Compose.Translate
open Lax496464Proofs.WHierarchy.Machine.Compose.Programs Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.ComputableBounds

/-- A word whose entries have at most `m` bits has at most `m + 1` bits per entry. -/
theorem bitSize_le_of_lt {m : ℕ} :
    ∀ y : List ℕ, (∀ u ∈ y, u < 2 ^ m) → bitSize y ≤ y.length * (m + 1)
  | [], _ => by simp [bitSize_nil]
  | u :: y, h => by
    rw [bitSize_cons]
    have h1 : u.size ≤ m := Nat.size_le.mpr (h u (by simp))
    have h2 := bitSize_le_of_lt y (fun u hu => h u (by simp [hu]))
    simp only [List.length_cons]
    nlinarith

theorem pow_le_pow_of_le {N a b : ℕ} (hN : 1 ≤ N) (h : a ≤ b) : N ^ a ≤ N ^ b :=
  Nat.pow_le_pow_right hN h

theorem one_le_pow {N a : ℕ} (hN : 1 ≤ N) : 1 ≤ N ^ a := Nat.one_le_pow _ _ hN

/-- The arithmetic of the composite bound. -/
theorem bound_arith {A C L N d1 d2 B1 B2 bs n : ℕ} (hA : 1 ≤ A) (hN : N = n + 1)
    (hB1 : B1 ≤ A * N ^ d1) (hbs : bs ≤ B1 * (B1 + 1))
    (hB2 : B2 ≤ C * (bs + 1) ^ d2) :
    10 * (B1 + B2) + L + n + 4 ≤
      (10 * (A + 4 ^ d2 * A ^ (2 * d2) * C) + L + 5) * N ^ (2 * d1 * (d2 + 1) + 1) := by
  set d := 2 * d1 * (d2 + 1) + 1 with hd
  have hN1 : 1 ≤ N := by omega
  have hX1 : 1 ≤ N ^ d1 := one_le_pow hN1
  have hNd : N ≤ N ^ d := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ d := pow_le_pow_of_le hN1 (by omega)
  -- the first bound
  have hdd : d1 ≤ d := by rw [hd]; nlinarith
  have e1 : B1 ≤ A * N ^ d := le_trans hB1 (Nat.mul_le_mul_left _ (pow_le_pow_of_le hN1 hdd))
  -- the size of the intermediate word
  have e2 : bs + 1 ≤ 4 * A ^ 2 * N ^ (2 * d1) := by
    have h1 : B1 + 1 ≤ 2 * (A * N ^ d1) := by
      have : 1 ≤ A * N ^ d1 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    calc bs + 1 ≤ B1 * (B1 + 1) + 1 := by omega
      _ ≤ (B1 + 1) * (B1 + 1) := by nlinarith
      _ ≤ (2 * (A * N ^ d1)) * (2 * (A * N ^ d1)) := Nat.mul_le_mul h1 h1
      _ = 4 * A ^ 2 * N ^ (2 * d1) := by ring
  have e3 : B2 ≤ 4 ^ d2 * A ^ (2 * d2) * C * N ^ d := by
    calc B2 ≤ C * (bs + 1) ^ d2 := hB2
      _ ≤ C * (4 * A ^ 2 * N ^ (2 * d1)) ^ d2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left e2 _)
      _ = 4 ^ d2 * A ^ (2 * d2) * C * N ^ (2 * d1 * d2) := by ring
      _ ≤ 4 ^ d2 * A ^ (2 * d2) * C * N ^ d :=
          Nat.mul_le_mul_left _ (pow_le_pow_of_le hN1 (by rw [hd]; nlinarith))
  have e4 : L + n + 4 ≤ (L + 5) * N ^ d := by nlinarith
  calc 10 * (B1 + B2) + L + n + 4
      ≤ 10 * (A * N ^ d + 4 ^ d2 * A ^ (2 * d2) * C * N ^ d) + (L + 5) * N ^ d := by omega
    _ = (10 * (A + 4 ^ d2 * A ^ (2 * d2) * C) + L + 5) * N ^ d := by ring

/--
---
conclusion: Lax496464.WH_A4_MachineFacts.fptTimeOn_comp
---
-/
theorem fptTimeOn_comp {D E : Set (List ℕ)} {κ κ' : List ℕ → ℕ} {F G : List ℕ → List ℕ}
    {g : ℕ → ℕ} (hF : FptTimeOn D κ F) (hmaps : ∀ x ∈ D, F x ∈ E) (hg : Computable g)
    (hκ : ∀ x ∈ D, κ' (F x) ≤ g (κ x)) (hG : FptTimeOn E κ' G) :
    FptTimeOn D κ fun x => G (F x) := by
  obtain ⟨p1, f1, d1, hf1, h1⟩ := hF
  obtain ⟨p2, f2, d2, hf2, h2⟩ := hG
  obtain ⟨F2, hF2c, hF2m, hF2⟩ := exists_monotone_bound hf2
  set L := lits p1 + lits p2 with hL
  -- the bound
  set f : ℕ → ℕ := fun k =>
    10 * ((f1 k + 1) + 4 ^ d2 * (f1 k + 1) ^ (2 * d2) * (F2 (g k) + 1)) + L + 5 with hfdef
  have hfc : Computable f := by
    have hA : Computable fun k => f1 k + 1 := computable_add hf1 (Computable.const 1)
    have hC : Computable fun k => F2 (g k) + 1 :=
      computable_add (hF2c.comp hg) (Computable.const 1)
    have h4 : Computable fun _ : ℕ => 4 ^ d2 := Computable.const _
    have hprod := computable_mul (computable_mul h4 (computable_pow (2 * d2) hA)) hC
    have hsum := computable_add hA hprod
    exact computable_add (computable_add (computable_mul (Computable.const 10) hsum)
      (Computable.const L)) (Computable.const 5)
  refine Lax496464Proofs.WHierarchy.Machine.RunsTo.fptTimeOn_of_runsTo (p := compose p1 p2) (f := f)
    (d := 2 * d1 * (d2 + 1) + 1) hfc ?_ ?_
  all_goals
    intro x hx
    obtain ⟨hfit1, hrun1⟩ := h1 x hx
    set k := κ x with hk
    set n := bitSize x with hn
    set B1 := fptBound f1 d1 k n with hB1
    set y := F x with hy
    have hyE : y ∈ E := hmaps x hx
    obtain ⟨hfit2, hrun2⟩ := h2 y hyE
    set B2 := fptBound f2 d2 (κ' y) (bitSize y) with hB2
    -- the intermediate word
    have hylen : y.length ≤ B1 := by
      obtain ⟨t, ht, hr⟩ := hrun1 B1 le_rfl
      exact (runsTo_length_le hr).trans ht
    have hyent : ∀ u ∈ y, u < 2 ^ B1 := fun u hu => hfit1 u (List.mem_append_right _ hu)
    have hbs : bitSize y ≤ B1 * (B1 + 1) :=
      (bitSize_le_of_lt y hyent).trans (Nat.mul_le_mul_right _ hylen)
    have hB1' : B1 ≤ (f1 k + 1) * (n + 1) ^ d1 := Nat.mul_le_mul_right _ (by omega)
    have hB2' : B2 ≤ (F2 (g k) + 1) * (bitSize y + 1) ^ d2 := by
      refine Nat.mul_le_mul_right _ ?_
      calc f2 (κ' y) ≤ F2 (κ' y) := hF2 _
        _ ≤ F2 (g k) := hF2m (hκ x hx)
        _ ≤ F2 (g k) + 1 := by omega
    have key := bound_arith (L := L) (by omega : 1 ≤ f1 k + 1) rfl hB1' hbs hB2'
    have hBdef : fptBound f (2 * d1 * (d2 + 1) + 1) k n =
        (10 * ((f1 k + 1) + 4 ^ d2 * (f1 k + 1) ^ (2 * d2) * (F2 (g k) + 1)) + L + 5) *
          (n + 1) ^ (2 * d1 * (d2 + 1) + 1) := rfl
    rw [← hBdef] at key
  · intro w hw
    -- the simulated word length
    obtain ⟨v, rfl⟩ : ∃ v, w = v + 2 := ⟨w - 2, by omega⟩
    have hv1 : B1 ≤ v := by omega
    have hv2 : B2 ≤ v := by omega
    obtain ⟨t1, ht1, hr1⟩ := hrun1 v hv1
    obtain ⟨t2, ht2, hr2⟩ := hrun2 v hv2
    have hLv : L < 2 ^ v := lt_of_lt_of_le Nat.lt_two_pow_self
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hyv : y.length + 1 < 2 ^ v := lt_of_lt_of_le
      (lt_of_le_of_lt (by omega : y.length + 1 ≤ B1 + 1) Nat.lt_two_pow_self)
      (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hXv : (x.length :: x).length < 2 ^ (v + 2) := by
      have := length_le_bitSize x
      simp only [List.length_cons]
      exact lt_of_lt_of_le (lt_of_le_of_lt (by omega : x.length + 1 ≤ n + 1) Nat.lt_two_pow_self)
        (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hl1 : lits p1 < 2 ^ v := lt_of_le_of_lt (by omega) hLv
    have hl2 : lits p2 < 2 ^ v := lt_of_le_of_lt (by omega) hLv
    obtain ⟨t, ht, hr⟩ := compose_runsTo (by omega) hl1 hl2 hXv hyv hr1 hr2
    exact ⟨t, by omega, hr⟩
  · intro u hu
    have := hfit2 u (List.mem_append_right _ hu)
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))

end Lax496464Proofs.WHierarchy.Machine.Compose.CompBound
