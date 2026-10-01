import Lax496464.WH_F4_IndependentSetToMcc
import Lax496464Proofs.WHierarchy.MccNP.Ram.PolyRun
import Lax391470Proofs.RamBridge

/-!
# Polynomial time on every word

The IMP+ program `readAll; validate; if ok then body` is compiled and its verified run transferred
to the word RAM; `RamBridge.ramPolytime_of_poly` gives `RamPolytime reduce`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.PolyTimeProof

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax391470Proofs.BitSize
open Lax496464Proofs.WHierarchy.MccNP.Ram.PolyNum Lax496464Proofs.WHierarchy.MccNP.Ram.PolyProg Lax496464Proofs.WHierarchy.MccNP.Ram.PolyRun
open Lax496464.WH_F2_MccConstruction (reduce)

/-- The compiled program. -/
def prog : Program := compileProgram layout cmd

theorem prog_runs (w : ℕ) (x : List ℕ)
    (hfit : ∀ v ∈ (x.length :: x), 8 * ((x.length + 1) + v + 1) ^ 4 ≤ 2 ^ w) :
    ∃ t ≤ 10 * Kfull x + 1, RunsTo w prog (x.length :: x) (reduce x) t := by
  have hs : Solves layout cmd {z | z = x.length :: x} (fun z => reduce z.tail)
      (fun z => Bd z.tail) (fun z => Kfull z.tail) := by
    refine ⟨cmd_ok, ?_, ?_⟩
    · intro z hz v hv
      rw [hz] at hv ⊢
      simp only [List.tail_cons]
      rcases List.mem_cons.mp hv with rfl | hv'
      · have := len_lt_Bd x; omega
      · exact mem_lt_Bd hv'
    · intro z hz
      rw [hz]
      simp only [List.tail_cons]
      refine ⟨fun a => if a = "a" then x.length else 0, ?_⟩
      obtain ⟨σ', hr, hq⟩ := main_spec x
        (initEnv (fun a => if a = "a" then x.length else 0) (x.length :: x))
        ⟨rfl, rfl, by simp [initEnv]⟩
      exact ⟨σ', hr, hq⟩
  obtain ⟨v, hv, hT⟩ : ∃ v ∈ (x.length :: x), x.length + Mmax x + 2 ≤ (x.length + 1) + v + 1 := by
    rcases Mmax_mem_or_zero x with hm | hm
    · exact ⟨Mmax x, List.mem_cons_of_mem _ hm, by omega⟩
    · exact ⟨x.length, List.mem_cons_self, by omega⟩
  have hf := hfit v hv
  have h := computesInTime_of_solves (w := w) (T := fun z => 10 * Kfull z.tail + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      have hB := len_lt_Bd x
      refine fitsWords_of_max_le (by omega) ?_
      simp only [Layout.span, layout, List.length_cons, List.length_nil, List.length_append,
        Validate.validateVars, Validate.SF, BodyDefs.bodyVars, max_le_iff, Bd]
      have hT4 : (x.length + 2) ^ 4 ≤ (x.length + 1 + v + 1) ^ 4 :=
        Nat.pow_le_pow_left (by omega) 4
      have hTT : x.length + 1 + v + 1 ≤ (x.length + 1 + v + 1) ^ 4 :=
        Nat.le_self_pow (by norm_num) _
      have h16 : 2 ^ 4 ≤ (x.length + 1 + v + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      have hM : Mmax x ≤ x.length + 1 + v + 1 := by omega
      generalize (x.length + 1 + v + 1) ^ 4 = P at *
      constructor
      · omega
      · simp only [BodyOk.bodyTemps]
        omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa [prog] using hrun⟩

theorem Kfull_le (x : List ℕ) :
    10 * Kfull x + 1 ≤ 16300 * (bitSize x + 1) ^ 3 := by
  have hlen := length_le_bitSize x
  have h1 : (x.length + 1) ^ 3 ≤ (bitSize x + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h2 : x.length + 1 ≤ (x.length + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold Kfull Kb Validate.Kval
  generalize (x.length + 1) ^ 3 = P at *
  generalize (bitSize x + 1) ^ 3 = Q at *
  omega

theorem out_lt (x : List ℕ) {v : ℕ} (hv : v ∈ reduce x) : v < 2 ^ (4 * bitSize x + 11) := by
  by_cases hx : Shape.Valid x
  · rw [Shape.reduce_valid hx] at hv
    have h1 := entry_le hx hv
    have hlen := length_le_bitSize x
    have h2 := Lax391470Proofs.RamBridge.add_two_le_two_pow (bitSize x)
    have h3 : (x.length + 2) ^ 4 ≤ (2 ^ (bitSize x + 1)) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have h4 : (2 ^ (bitSize x + 1)) ^ 4 = 2 ^ (4 * bitSize x + 4) := by
      rw [← Nat.pow_mul]; congr 1; ring
    have h5 : 2 ^ (4 * bitSize x + 4) < 2 ^ (4 * bitSize x + 11) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [Shape.reduce_invalid hx] at hv
    simp at hv

/-- **The reduction is computable in polynomial time on a word RAM.** -/
theorem ramPolytime : RamPolytime reduce := by
  refine Lax391470Proofs.RamBridge.ramPolytime_of_poly (c := 8) (d := 4) (K := 11) (prog := prog)
    (Polynomial.C 16300 * (Polynomial.X + Polynomial.C 1) ^ 3) (by norm_num) (by norm_num) ?_ ?_
  · intro x v hv
    exact out_lt x hv
  · intro w x hfits
    obtain ⟨t, ht, hrun⟩ := prog_runs w x hfits
    refine ⟨t, ?_, hrun⟩
    have := Kfull_le x
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    omega

/--
---
conclusion: Lax496464.WH_F4_IndependentSetToMcc.reduce_polyTime
---
The reduction is computed in polynomial time by one word RAM program, the compilation of the IMP+
program that reads the length-prefixed word into an array, decides in one linear pass whether the
word has the shape of an encoding, and, if it does, writes the word of the multicoloured graph
with the passes of the fixed-parameter program; on every other word it writes nothing. The run
costs at most `16300 (bitSize x + 1)^3` instructions when the word length fits the values, all of
which are below `(|x| + 2)^4 + max x + 1`.
-/
theorem reduce_polyTime_proved : Lax759944.RamPolytime.RamPolytime Lax496464.WH_F2_MccConstruction.reduce :=
  ramPolytime

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_polyTime := reduce_polyTime_proved

end Lax496464Proofs.WHierarchy.MccNP.Ram.PolyTimeProof
