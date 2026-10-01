import Lax496464.WH_A5_Bridges
import Lax496464Proofs.WHierarchy.Machine.SizeFacts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Reading the last entry of a word, in constant time: the parameter of every problem whose
parameter is written last. -/

namespace Lax496464Proofs.WHierarchy.Machine.LastEntry

open Lax808846.Ram Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A5_Bridges Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-- On the tape `x.length :: x`, entry `x.length` is the last entry of `x` (or the prefix `0` when
`x` is empty). -/
def lastProg : Program :=
  [.inputLength 0, .set 1 1, .sub 0 0 1, .inputLoad 2 0, .write 2, .halt]

theorem tape_getElem (x : List ℕ) :
    (x.length :: x)[x.length]'(by simp) = x.getLast?.getD 0 := by
  rcases List.eq_nil_or_concat x with rfl | ⟨l, a, rfl⟩
  · simp
  · simp

theorem lastProg_runsTo (x : List ℕ) (w : ℕ) (hw : x.length + 2 < 2 ^ w)
    (hv : x.getLast?.getD 0 < 2 ^ w) :
    RunsTo w lastProg (x.length :: x) [x.getLast?.getD 0] 6 := by
  have h1 : 1 < 2 ^ w := by omega
  have hn : x.length + 1 < 2 ^ w := by omega
  have hn' : x.length < 2 ^ w := by omega
  have h0 : (0 : ℕ) < 2 ^ w := by omega
  have h2 : (2 : ℕ) < 2 ^ w := by omega
  refine ⟨5, _, rfl, ?_, ?_, ?_⟩ <;>
    simp [step, lastProg, Instr.effect, setCell, initState, terminalCost,
      Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn', Nat.mod_eq_of_lt h0,
      Nat.mod_eq_of_lt h2]
  rw [tape_getElem, Nat.mod_eq_of_lt hv]

/-- **The last entry is computable in polynomial time.** -/
theorem polyTimeOn_last (D : Set (List ℕ)) : PolyTimeOn D fun x => [x.getLast?.getD 0] := by
  refine polyTimeOn_of_runsTo (p := lastProg) (c := 6) (d := 1) (fun x _ w hw => ?_) ?_
  · have hs := length_le_bitSize x
    have hv : x.getLast?.getD 0 < 2 ^ bitSize x := by
      rcases List.eq_nil_or_concat x with rfl | ⟨l, a, rfl⟩
      · simp
      · simpa using lt_two_pow_bitSize (x := l ++ [a]) (v := a) (by simp)
    have hbw : bitSize x + 3 ≤ w := by nlinarith
    have hpow : 2 ^ bitSize x * 8 ≤ 2 ^ w := by
      calc 2 ^ bitSize x * 8 = 2 ^ (bitSize x + 3) := by ring
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hbw
    have hlt : bitSize x < 2 ^ bitSize x := Nat.lt_two_pow_self
    refine ⟨6, by nlinarith, lastProg_runsTo x w (by omega) (by omega)⟩
  · intro x _ v hv
    simp only [List.mem_singleton] at hv
    subst hv
    rcases List.eq_nil_or_concat x with rfl | ⟨l, a, rfl⟩
    · simp
    · have := lt_two_pow_bitSize (x := l ++ [a]) (v := a) (by simp)
      rw [List.concat_eq_append, List.getLast?_concat, Option.getD_some]
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

end Lax496464Proofs.WHierarchy.Machine.LastEntry
