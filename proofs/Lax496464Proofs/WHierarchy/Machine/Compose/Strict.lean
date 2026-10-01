import Lax496464Proofs.WHierarchy.Machine.Compose.Programs
import Lax496464Proofs.WHierarchy.Machine.RunsTo
import Lax496464Proofs.WHierarchy.ComputableBounds

/-! The archive's strict fixed-parameter time (on the unprefixed tape, correct at the word lengths
at which input and output fit) gives fixed-parameter time, through the program `strip`. -/

namespace Lax496464Proofs.WHierarchy.Machine.Compose.Strict

open Lax808846.Ram Lax808846.RamComputes Lax759944.BinaryWordEncoding
open Lax888481.ParameterizedComplexity (Fits)
open Lax496464.WH_A1_FptTime
open Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics Lax496464Proofs.WHierarchy.Machine.Compose.Translate
open Lax496464Proofs.WHierarchy.Machine.Compose.Programs Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.ComputableBounds

/-- A word fits once its length and entries are below `2 ^ a`, and `c < 2 ^ b`, at every word
length from `a + b + 1` on. -/
theorem fits_of_lt {c W a b : ℕ} {z : List ℕ} (hlen : z.length < 2 ^ a)
    (hent : ∀ u ∈ z, u < 2 ^ a) (hc : c < 2 ^ b) (hW : a + b + 1 ≤ W) : Fits c W z := by
  intro u hu
  have h1 : z.length + u + 1 ≤ 2 ^ (a + 1) := by
    have := hent u hu; rw [pow_succ]; omega
  calc c * (z.length + u + 1) ≤ 2 ^ b * 2 ^ (a + 1) := Nat.mul_le_mul hc.le h1
    _ = 2 ^ (a + b + 1) := by rw [← pow_add]; congr 1; omega
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW

theorem lt_pow_of_le {x m a : ℕ} (hx : x < 2 ^ m) (h : m ≤ a) : x < 2 ^ a :=
  lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) h)

/-- The arithmetic of the bound. -/
theorem strict_arith {c G E0 L n len T0 e d : ℕ} (hlen : len ≤ n)
    (hT0 : T0 = c * G * (len + 1)) (hE : E0 = e * (n + 1) ^ d) :
    10 * T0 + E0 + n + c + L + 5 ≤ (10 * c * G + e + c + L + 5) * (n + 1) ^ (d + 1) := by
  have hN1 : 1 ≤ n + 1 := by omega
  have hNd : n + 1 ≤ (n + 1) ^ (d + 1) := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ (d + 1) := Nat.pow_le_pow_right hN1 (by omega)
  have hNd' : (n + 1) ^ d ≤ (n + 1) ^ (d + 1) := Nat.pow_le_pow_right hN1 (by omega)
  have e1 : T0 ≤ c * G * (n + 1) ^ (d + 1) := by
    rw [hT0]; exact Nat.mul_le_mul_left _ (le_trans (by omega) hNd)
  have e2 : E0 ≤ e * (n + 1) ^ (d + 1) := by rw [hE]; exact Nat.mul_le_mul_left _ hNd'
  have e3 : n + c + L + 5 ≤ (c + L + 5) * (n + 1) ^ (d + 1) := by nlinarith
  calc 10 * T0 + E0 + n + c + L + 5
      ≤ 10 * (c * G * (n + 1) ^ (d + 1)) + e * (n + 1) ^ (d + 1) +
          (c + L + 5) * (n + 1) ^ (d + 1) := by omega
    _ = (10 * c * G + e + c + L + 5) * (n + 1) ^ (d + 1) := by ring

/--
---
conclusion: Lax496464.WH_A5_Bridges.fptTimeOn_of_strict
---
-/
theorem fptTimeOn_of_strict {D : Set (List ℕ)} {κ : List ℕ → ℕ} {F : List ℕ → List ℕ}
    {prog : Program} {c : ℕ} {g : ℕ → ℕ} (hg : Computable g)
    (htime : ∀ w : ℕ, ComputesInTime w prog {x | x ∈ D ∧ Fits c w x ∧ Fits c w (F x)} F
      fun x => c * g (κ x) * (x.length + 1))
    (hout : ∃ (e : ℕ → ℕ) (d : ℕ), Computable e ∧
      ∀ x ∈ D, ∀ v ∈ F x, v < 2 ^ (e (κ x) * (bitSize x + 1) ^ d)) :
    FptTimeOn D κ F := by
  obtain ⟨e, d, he, hbd⟩ := hout
  set L := lits prog with hL
  set f : ℕ → ℕ := fun k => 10 * c * g k + e k + c + L + 5 with hfdef
  have hfc : Computable f := by
    have h1 : Computable fun k => 10 * c * g k :=
      computable_mul (Computable.const (10 * c)) hg
    exact computable_add (computable_add (computable_add (computable_add h1 he)
      (Computable.const c)) (Computable.const L)) (Computable.const 5)
  refine Lax496464Proofs.WHierarchy.Machine.RunsTo.fptTimeOn_of_runsTo (p := strip prog) (f := f)
    (d := d + 1) hfc ?_ ?_
  all_goals
    intro x hx
    set k := κ x with hk
    set n := bitSize x with hn
    set T0 := c * g k * (x.length + 1) with hT0
    set E0 := e k * (n + 1) ^ d with hE0
    have hent : ∀ u ∈ F x, u < 2 ^ E0 := hbd x hx
    have hxlen : x.length ≤ n := length_le_bitSize x
    have hxent : ∀ u ∈ x, u < 2 ^ n := fun u hu => lt_two_pow_bitSize hu
    have key := strict_arith (c := c) (G := g k) (L := L) hxlen hT0 hE0
    have hBdef : fptBound f (d + 1) k n = (10 * c * g k + e k + c + L + 5) * (n + 1) ^ (d + 1) :=
      rfl
    rw [← hBdef] at key
  · intro w hw
    -- the length of the output, from one run at a large word length
    have hFlen : (F x).length ≤ T0 := by
      set W := c + bitSize x + bitSize (F x) + 1
      have hfx : Fits c W x :=
        fits_of_lt (a := bitSize x + bitSize (F x)) (b := c)
          (lt_pow_of_le (lt_of_le_of_lt hxlen Nat.lt_two_pow_self) (by omega))
          (fun u hu => lt_pow_of_le (hxent u hu) (by omega)) Nat.lt_two_pow_self (by omega)
      have hfF : Fits c W (F x) :=
        fits_of_lt (a := bitSize x + bitSize (F x)) (b := c)
          (lt_pow_of_le (lt_of_le_of_lt (length_le_bitSize (F x)) Nat.lt_two_pow_self)
            (by omega))
          (fun u hu => lt_pow_of_le (lt_two_pow_bitSize hu) (by omega)) Nat.lt_two_pow_self
          (by omega)
      obtain ⟨t, ht, hr⟩ := htime W x ⟨hx, hfx, hfF⟩
      exact (runsTo_length_le hr).trans ht
    -- the simulated word length
    obtain ⟨v, rfl⟩ : ∃ v, w = v + 2 := ⟨w - 2, by omega⟩
    have hfx : Fits c v x :=
      fits_of_lt (a := n) (b := c) (lt_of_le_of_lt hxlen Nat.lt_two_pow_self) hxent
        Nat.lt_two_pow_self (by omega)
    have hfF : Fits c v (F x) :=
      fits_of_lt (a := T0 + E0) (b := c)
        (lt_pow_of_le (lt_of_le_of_lt hFlen Nat.lt_two_pow_self) (by omega))
        (fun u hu => lt_pow_of_le (hent u hu) (by omega)) Nat.lt_two_pow_self (by omega)
    obtain ⟨t, ht, hr⟩ := htime v x ⟨hx, hfx, hfF⟩
    have ht0 : t ≤ T0 := ht
    have hl : lits prog < 2 ^ v := lt_pow_of_le Nat.lt_two_pow_self (by omega)
    have hxw : x.length + 1 < 2 ^ (v + 2) :=
      lt_pow_of_le (lt_of_le_of_lt (by omega : x.length + 1 ≤ n + 1) Nat.lt_two_pow_self)
        (by omega)
    obtain ⟨t', ht', hr'⟩ := strip_runsTo (by omega) hl hxw hr
    exact ⟨t', by omega, hr'⟩
  · intro u hu
    exact lt_pow_of_le (hent u hu) (by omega)

end Lax496464Proofs.WHierarchy.Machine.Compose.Strict
