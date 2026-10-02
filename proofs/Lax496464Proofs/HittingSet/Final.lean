import Lax496464.HittingSetHardness
import Lax496464Proofs.HittingSet.Main
import Lax391470Proofs.L2Final
import Lax391470Proofs.RamToTuring

/-!
# The Reduction Runs in Polynomial Time

The program of `Main`, compiled to the word RAM, computes the zeros and ones of the
reduction within a polynomial number of instructions; polynomial time on the word RAM
transfers to a Turing machine.
-/

namespace Lax496464Proofs.HittingSet.Final

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes
open Lax496464Proofs.HittingSet.Main Lax496464Proofs.HittingSet.Model Lax496464Proofs.HittingSet.Front Lax496464Proofs.HittingSet.Emit
open Lax496464Proofs.HittingSet.Pairs Lax496464Proofs.HittingSet.Mark Lax496464Proofs.HittingSet.Sweep Lax496464Proofs.HittingSet.Clause
open Lax391470Proofs.L2Ram Lax391470Proofs.L2Final
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime Lax391470Proofs.BitSize
open Lax391470Proofs.Bits

def layout : Layout :=
  ⟨["L", "rt", "rv", "ph", "n", "C", "k", "mx", "p", "c", "V", "nn", "m", "i", "cnt", "e",
    "v", "u", "s", "i2"],
   ["a", "vr", "sg", "cl", "mark"], 12⟩

theorem com_ok : Com.Ok layout main := by
  simp [main, front, reject, dims, head, pairsLoop, pairBody, pairEmit, clauseLoop, clauseBody,
    markLoop, markBody, elemE, markE, sweepLoop, sweepBody, emitE, setNat,
    Lax391470Proofs.EmitNat.emitNat, Lax391470Proofs.EmitNat.sizeLoop,
    Lax391470Proofs.EmitNat.sizeBody, Lax391470Proofs.EmitNat.onesLoop,
    Lax391470Proofs.EmitNat.onesBody, Lax391470Proofs.EmitNat.digLoop,
    Lax391470Proofs.EmitNat.digBody,
    Lax391470Proofs.ReadAll.readAll, Lax391470Proofs.ReadAll.readLoop,
    Lax391470Proofs.ReadAll.readBody, Lax391470Proofs.L2Scan.scanLoop,
    Lax391470Proofs.L2Scan.scanBody, Lax391470Proofs.L2Scan.dispatch,
    Lax391470Proofs.L2Scan.phase3, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-- The value bound of an input. -/
def Bd (y : List ℕ) : ℕ := Mof y.length + 5 + Mx y

theorem solves : Solves layout main Shape (fun x => red x.tail) (fun x => Bd x.tail)
    (fun x => Kmain x.tail.length) where
  ok := com_ok
  inp := by
    intro x hx v hv
    rw [shape_eq hx] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · unfold Bd Mof; nlinarith
    · have := le_Mx hv'; unfold Bd; omega
  run := by
    intro x hx
    obtain ⟨σ', hrun, hout⟩ := main_spec (B := Bd x.tail) x.tail
      (fun v hv => by have := le_Mx hv; unfold Bd; omega) (by unfold Bd; omega)
    rw [← shape_eq hx] at hrun
    exact ⟨_, σ', hrun, hout⟩

def prog : Program := compileProgram layout main

theorem prog_runs (w : ℕ) (x : List ℕ) (hfit : 52 + 5 * Bd x ≤ 2 ^ w) :
    ∃ t ≤ 10 * Kmain x.length + 1, RunsTo w prog (x.length :: x) (red x) t := by
  have hs : Solves layout main {z | z = x.length :: x} (fun z => red z.tail)
      (fun z => Bd z.tail) (fun z => Kmain z.tail.length) :=
    ⟨solves.ok, fun z hz => solves.inp z (by rw [hz]; exact ⟨by simp, by simp⟩),
      fun z hz => solves.run z (by rw [hz]; exact ⟨by simp, by simp⟩)⟩
  have h := computesInTime_of_solves (w := w) (T := fun z => 10 * Kmain z.tail.length + 1) hs
    (fun z hz => by
      rw [hz]; simp only [List.tail_cons]
      have hB : 1 < Bd x := by unfold Bd Mof; omega
      refine fitsWords_of_max_le hB ?_
      simp only [Layout.span, layout, List.length_cons, List.length_nil, max_le_iff]
      omega)
    (fun z hz => by simp [Layout.const])
  obtain ⟨t, ht, hrun⟩ := h (x.length :: x) rfl
  exact ⟨t, by simpa using ht, by simpa [prog] using hrun⟩

/-! ### Fitting into a word -/

/-- The constant of the fitting condition. -/
def cfit : ℕ := 2000

theorem fit_of (w : ℕ) (x : List ℕ)
    (h : ∀ v ∈ (x.length :: x), cfit * ((x.length + 1) + v + 1) ^ 2 ≤ 2 ^ w) :
    52 + 5 * Bd x ≤ 2 ^ w := by
  obtain ⟨v, hv, hT⟩ : ∃ v ∈ (x.length :: x), x.length + Mx x + 2 ≤ (x.length + 1) + v + 1 := by
    rcases Mx_mem_or_zero x with hm | hm
    · exact ⟨Mx x, List.mem_cons_of_mem _ hm, by omega⟩
    · exact ⟨x.length, List.mem_cons_self, by omega⟩
  have hpow := Nat.pow_le_pow_left hT 2
  have hc := Nat.mul_le_mul_left cfit hpow
  refine le_trans ?_ (le_trans hc (h v hv))
  obtain ⟨T, hTd⟩ : ∃ T, x.length + Mx x + 2 = T := ⟨_, rfl⟩
  rw [hTd]
  have hL2 : x.length + 2 ≤ T := by omega
  have hM : Mx x ≤ T := by omega
  have hTT : T ≤ T * T := Nat.le_mul_of_pos_left _ (by omega)
  have hsq : (x.length + 2) * (x.length + 2) ≤ T * T := Nat.mul_le_mul hL2 hL2
  have e : cfit * T ^ 2 = 2000 * (T * T) := by unfold cfit; ring
  rw [e]
  unfold Bd Mof
  omega

/-! ### The running time is polynomial in the bit size -/

/-- `Kmain` is a fourth-degree polynomial in the length. -/
theorem Kmain_le (L : ℕ) : 10 * Kmain L + 1 ≤ 10000000 * (L + 2) ^ 4 := by
  obtain ⟨Z, hZ⟩ : ∃ Z, L + 2 = Z := ⟨_, rfl⟩
  have hZ2 : 2 ≤ Z := by omega
  have hLZ : L ≤ Z := by omega
  obtain ⟨Z2, hZ2d⟩ : ∃ Z2, Z * Z = Z2 := ⟨_, rfl⟩
  obtain ⟨Z3, hZ3d⟩ : ∃ Z3, Z2 * Z = Z3 := ⟨_, rfl⟩
  obtain ⟨Z4, hZ4d⟩ : ∃ Z4, Z3 * Z = Z4 := ⟨_, rfl⟩
  have hZZ2 : Z ≤ Z2 := by rw [← hZ2d]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hZ23 : Z2 ≤ Z3 := by rw [← hZ3d]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hZ34 : Z3 ≤ Z4 := by rw [← hZ4d]; exact Nat.le_mul_of_pos_right _ (by omega)
  have h4 : (L + 2) ^ 4 = Z4 := by rw [hZ, ← hZ4d, ← hZ3d, ← hZ2d]; ring
  rw [h4]
  have hS : Sof L ≤ 4 * Z := by unfold Sof; omega
  have hKs : Kscan L ≤ 100 * Z := by unfold Kscan; omega
  have hKp : Kpair (Sof L) + 4 ≤ 800 * Z := by unfold Kpair; omega
  have hP : (Kpair (Sof L) + 4) * (L + 2) ≤ 800 * Z2 := by
    have := Nat.mul_le_mul hKp (show L + 2 ≤ Z by omega)
    rw [Nat.mul_assoc, hZ2d] at this; exact this
  have hKsw : Ksweep (Sof L) + 4 ≤ 260 * Z := by unfold Ksweep; omega
  have hSw : (Ksweep (Sof L) + 4) * (2 * L + 4) ≤ 520 * Z2 := by
    have := Nat.mul_le_mul hKsw (show 2 * L + 4 ≤ 2 * Z by omega)
    rw [show 260 * Z * (2 * Z) = 520 * (Z * Z) by ring, hZ2d] at this; exact this
  have hKc : Kclause (Sof L) L + 4 ≤ 1000 * Z2 := by unfold Kclause Kmark; omega
  have hC : (Kclause (Sof L) L + 4) * (L + 1) ≤ 1000 * Z3 := by
    have := Nat.mul_le_mul hKc (show L + 1 ≤ Z by omega)
    rw [Nat.mul_assoc, hZ3d] at this; exact this
  unfold Kmain
  omega

/-- **The reduction, on zeros and ones, is polynomial-time on a word RAM.** -/
theorem ramPolytime_red : RamPolytime red := by
  have hK : cfit * 4 ^ 2 ≤ 2 ^ 15 := by unfold cfit; norm_num
  refine Lax391470Proofs.RamBridge.ramPolytime_of_poly (c := cfit) (d := 2) (K := 15)
    (prog := prog) (Polynomial.C 10000000 * (Polynomial.X + Polynomial.C 2) ^ 4)
    (by omega) hK ?_ ?_
  · intro x v hv
    have h1 : v ≤ 1 := by
      unfold red natBits at hv
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hv
      split_ifs <;> omega
    have h2 : 2 ≤ 2 ^ (2 * bitSize x + 15) :=
      le_trans (by norm_num) (Nat.pow_le_pow_right (by omega)
        (show 1 ≤ 2 * bitSize x + 15 by omega))
    omega
  · intro w x hfits
    obtain ⟨t, ht, hrun⟩ := prog_runs w x (fit_of w x hfits)
    refine ⟨t, ?_, hrun⟩
    have h1 := Kmain_le x.length
    have hlen := length_le_bitSize x
    have h2 : (x.length + 2) ^ 4 ≤ (bitSize x + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    have := Nat.mul_le_mul_left 10000000 h2
    omega

open Lax434930.PolynomialTime in
/-- The reduction, as a function on words, is polynomial-time on a Turing machine. -/
theorem reduceWord_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id id Lax496464.HittingSetFromSat.reduceWord) :=
  Lax391470Proofs.RamToTuring.polyTime_of_ram ramPolytime_red red_natBits

open Lax434930.PolynomialTime Lax496464.HittingSet Lax496464.HittingSetFromSat in
/--
---
conclusion: Lax496464.HittingSetHardness.fromSat_polyTime
---
The reduction is a word RAM program on the zeros and ones of its input: a finite-state
scan decodes the formula into arrays of literal indices, signs and clause numbers; the
three numbers and the pairs are written directly; for each clause the elements of its
literals are marked and counted in one pass over the positions, and a sweep of the marks
writes them in increasing order. Polynomial time on the word RAM transfers to a Turing
machine, and the machine writing the word of the instance is one writing the instance.
-/
theorem fromSat_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id
      (fun z : Instance × ℕ => encodeInstance z.1 z.2) reduce) := by
  obtain ⟨t⟩ := reduceWord_polyTime
  exact ⟨{ t with outputsFun := fun w => t.outputsFun w }⟩

end Lax496464Proofs.HittingSet.Final
