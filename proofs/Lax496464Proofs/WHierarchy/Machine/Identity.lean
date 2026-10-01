import Lax496464.WH_A4_MachineFacts
import Lax496464.WH_A5_Bridges
import Lax496464Proofs.WHierarchy.Machine.SizeFacts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! The identity in linear time: skip the length prefix, then copy the tape to the output. -/

namespace Lax496464Proofs.WHierarchy.Machine.Identity

open Lax808846.Ram Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A5_Bridges Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-- `read 0; loop: jeof end; read 0; write 0; jump loop; end: halt`. -/
def copyProg : Program := [.read 0, .jeof 5, .read 0, .write 0, .jump 1, .halt]

theorem run_add (w : ℕ) (p : Program) (a b : ℕ) (s : State) :
    run w p (a + b) s = (run w p a s).bind (run w p b) := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih =>
    rw [Nat.add_right_comm, run, run, Option.bind_assoc]
    congr 1
    funext s'
    exact ih s'

/-- The copy loop: from the loop head with `r` left on the tape, `4 · |r|` steps copy `r`. -/
theorem copy_loop (w : ℕ) (r : List ℕ) (hr : ∀ v ∈ r, v < 2 ^ w) (s : State) (hpc : s.pc = 1)
    (hinp : s.inp = r) :
    ∃ s', run w copyProg (4 * r.length) s = some s' ∧ s'.pc = 1 ∧ s'.inp = [] ∧
      s'.out = s.out ++ r := by
  induction r generalizing s with
  | nil => exact ⟨s, rfl, hpc, hinp, by simp⟩
  | cons v r ih =>
    have hv : v < 2 ^ w := hr v (by simp)
    obtain ⟨s', h1, h2, h3, h4⟩ := ih (fun u hu => hr u (by simp [hu]))
      { pc := 1, mem := setCell w s.mem 0 v, input := s.input, inp := r,
        out := s.out ++ [v] } rfl rfl
    refine ⟨s', ?_, h2, h3, by rw [h4]; simp⟩
    have hsplit : 4 * (v :: r).length = 4 + 4 * r.length := by simp; ring
    rw [hsplit, run_add]
    have h4steps : run w copyProg 4 s = some
        { pc := 1, mem := setCell w s.mem 0 v, input := s.input, inp := r,
          out := s.out ++ [v] } := by
      have hw : (0 : ℕ) < 2 ^ w := by positivity
      simp [run, step, copyProg, hpc, hinp, Instr.effect, setCell, Nat.mod_eq_of_lt hv,
        Nat.mod_eq_of_lt hw]
    rw [h4steps]
    exact h1

theorem copyProg_runsTo (w : ℕ) (x : List ℕ) (hx : ∀ v ∈ x, v < 2 ^ w) :
    RunsTo w copyProg (x.length :: x) x (4 * x.length + 3) := by
  have h0 : run w copyProg 1 (initState (x.length :: x)) = some
      { pc := 1, mem := setCell w (fun _ => 0) 0 x.length, input := x.length :: x, inp := x,
        out := [] } := by
    simp [run, step, copyProg, initState, Instr.effect]
  obtain ⟨s', h1, h2, h3, h4⟩ := copy_loop w x hx
    { pc := 1, mem := setCell w (fun _ => 0) 0 x.length, input := x.length :: x, inp := x,
      out := [] } rfl rfl
  have h5 : step w copyProg s' = some { s' with pc := 5 } := by
    simp [step, copyProg, h2, Instr.effect, h3]
  refine ⟨1 + 4 * x.length + 1, { s' with pc := 5 }, ?_, ?_, ?_, ?_⟩
  · rw [run_add, run_add, h0]
    simp only [Option.bind_some]
    rw [h1]
    simp [run, h5]
  · simp [step, copyProg, Instr.effect]
  · simpa using h4
  · simp [terminalCost, copyProg]; ring

/-- The identity in polynomial time. -/
theorem polyTimeOn_id (D : Set (List ℕ)) : PolyTimeOn D fun x => x := by
  refine polyTimeOn_of_runsTo (p := copyProg) (c := 7) (d := 1) (fun x _ w hw => ?_) ?_
  · have hs := length_le_bitSize x
    have hpow : 2 ^ bitSize x ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by
      simp at hw; omega)
    refine ⟨4 * x.length + 3, by simp; omega, copyProg_runsTo w x fun v hv =>
      lt_of_lt_of_le (lt_two_pow_bitSize hv) hpow⟩
  · intro x _ v hv
    exact lt_of_lt_of_le (lt_two_pow_bitSize hv)
      (Nat.pow_le_pow_right (by norm_num) (by simp; omega))

/--
---
conclusion: Lax496464.WH_A4_MachineFacts.fptTimeOn_id
---
-/
theorem fptTimeOn_id (D : Set (List ℕ)) (κ : List ℕ → ℕ) : FptTimeOn D κ fun x => x :=
  Lax496464.WH_A4_MachineFacts.fptTimeOn_of_polyTimeOn κ (polyTimeOn_id D)

end Lax496464Proofs.WHierarchy.Machine.Identity
