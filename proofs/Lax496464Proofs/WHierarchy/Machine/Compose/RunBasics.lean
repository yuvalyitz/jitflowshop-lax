import Lax496464.WH_A1_FptTime
import Mathlib.Tactic

/-! Basic facts about runs of word-RAM programs: composition of runs, the output only grows (by at
most one entry per step), code blocks contained in a program, and straight-line execution of
blocks of instructions that always advance the program counter. -/

namespace Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics

open Lax808846.Ram

theorem run_zero (w : ℕ) (p : Program) (s : State) : run w p 0 s = some s := rfl

theorem run_succ (w : ℕ) (p : Program) (k : ℕ) (s : State) :
    run w p (k + 1) s = (step w p s).bind (run w p k) := rfl

theorem run_add (w : ℕ) (p : Program) :
    ∀ (a b : ℕ) (s : State), run w p (a + b) s = (run w p a s).bind (run w p b)
  | 0, b, s => by simp [run]
  | a + 1, b, s => by
    rw [Nat.add_right_comm, run_succ, run_succ]
    cases h : step w p s with
    | none => simp
    | some s1 => simpa using run_add w p a b s1

theorem run_trans {w : ℕ} {p : Program} {a b : ℕ} {s s1 s2 : State}
    (h1 : run w p a s = some s1) (h2 : run w p b s1 = some s2) : run w p (a + b) s = some s2 := by
  rw [run_add, h1]; simpa using h2

theorem run_of_step {w : ℕ} {p : Program} {k : ℕ} {s s1 s2 : State}
    (h1 : step w p s = some s1) (h2 : run w p k s1 = some s2) : run w p (k + 1) s = some s2 := by
  rw [run_succ, h1]; simpa using h2

theorem run_one {w : ℕ} {p : Program} {s s1 : State} (h1 : step w p s = some s1) :
    run w p 1 s = some s1 := run_of_step h1 rfl

theorem step_of_fetch {w : ℕ} {p : Program} {s : State} {i : Instr} (hf : p[s.pc]? = some i) :
    step w p s = i.effect w s := by
  simp [step, hf]

/-! ### The output grows by at most one entry per step -/

theorem effect_out {w : ℕ} {i : Instr} {s s' : State} (h : i.effect w s = some s') :
    ∃ l : List ℕ, s'.out = s.out ++ l ∧ l.length ≤ 1 := by
  cases i with
  | write a =>
    simp only [Instr.effect, Option.some.injEq] at h
    subst h; exact ⟨[_], rfl, by simp⟩
  | read a =>
    simp only [Instr.effect] at h
    rcases hs : s.inp.head? with _ | v <;> rw [hs] at h <;> simp at h
    subst h; exact ⟨[], by simp, by simp⟩
  | halt => simp [Instr.effect] at h
  | _ =>
    simp only [Instr.effect, Option.some.injEq] at h
    subst h; exact ⟨[], by simp, by simp⟩

theorem step_out {w : ℕ} {p : Program} {s s' : State} (h : step w p s = some s') :
    ∃ l : List ℕ, s'.out = s.out ++ l ∧ l.length ≤ 1 := by
  unfold step at h
  rcases hi : p[s.pc]? with _ | i <;> rw [hi] at h
  · simp at h
  · exact effect_out h

theorem run_out {w : ℕ} {p : Program} :
    ∀ (k : ℕ) (s s' : State), run w p k s = some s' →
      ∃ l : List ℕ, s'.out = s.out ++ l ∧ l.length ≤ k
  | 0, s, s', h => by
    simp only [run, Option.some.injEq] at h; subst h; exact ⟨[], by simp, by simp⟩
  | k + 1, s, s', h => by
    rw [run_succ] at h
    rcases hs : step w p s with _ | s1 <;> rw [hs] at h
    · simp at h
    · obtain ⟨l1, h1, hl1⟩ := step_out hs
      obtain ⟨l2, h2, hl2⟩ := run_out k s1 s' (by simpa using h)
      exact ⟨l1 ++ l2, by rw [h2, h1, List.append_assoc], by simp; omega⟩

/-- The output of a run has at most as many entries as the run has steps. -/
theorem runsTo_length_le {w : ℕ} {p : Program} {x y : List ℕ} {t : ℕ} (h : RunsTo w p x y t) :
    y.length ≤ t := by
  obtain ⟨k, s, hr, -, hy, ht⟩ := h
  obtain ⟨l, hl, hlen⟩ := run_out k _ _ hr
  subst hy ht
  rw [hl]; simp [initState]; omega

/-- A later state's output extends an earlier one's. -/
theorem run_out_prefix {w : ℕ} {p : Program} {k : ℕ} {s s' : State}
    (h : run w p k s = some s') : s.out.length ≤ s'.out.length := by
  obtain ⟨l, hl, -⟩ := run_out k s s' h
  rw [hl]; simp

/-! ### Blocks of code -/

/-- The program `P` holds the block `blk` from position `pc0` on. -/
def Contains (P : Program) (pc0 : ℕ) (blk : List Instr) : Prop :=
  ∀ j < blk.length, P[pc0 + j]? = blk[j]?

theorem Contains.left {P : Program} {pc0 : ℕ} {a b : List Instr} (h : Contains P pc0 (a ++ b)) :
    Contains P pc0 a := by
  intro j hj
  have := h j (by simp; omega)
  rw [this, List.getElem?_append_left hj]

theorem Contains.right {P : Program} {pc0 : ℕ} {a b : List Instr} (h : Contains P pc0 (a ++ b)) :
    Contains P (pc0 + a.length) b := by
  intro j hj
  have := h (a.length + j) (by simp; omega)
  rw [← Nat.add_assoc] at this
  rw [this, List.getElem?_append_right (by omega)]
  simp

theorem Contains.head {P : Program} {pc0 : ℕ} {i : Instr} {b : List Instr}
    (h : Contains P pc0 (i :: b)) : P[pc0]? = some i := by
  simpa using h 0 (by simp)

theorem Contains.tail {P : Program} {pc0 : ℕ} {i : Instr} {b : List Instr}
    (h : Contains P pc0 (i :: b)) : Contains P (pc0 + 1) b :=
  Contains.right (a := [i]) h

/-! ### Straight-line instructions -/

/-- The instructions that always succeed and advance the program counter by one. -/
def isPlain : Instr → Bool
  | .set .. | .load .. | .store .. | .add .. | .sub .. | .mul .. | .div .. | .and ..
  | .shiftl .. | .not .. | .inputLength .. | .inputLoad .. | .write .. => true
  | _ => false

/-- The effect of a plain instruction, as a total function. -/
def plainEff (w : ℕ) (i : Instr) (s : State) : State := (i.effect w s).getD s

theorem effect_plain {w : ℕ} {i : Instr} (h : isPlain i = true) (s : State) :
    i.effect w s = some (plainEff w i s) := by
  cases i <;> simp_all [isPlain, plainEff, Instr.effect]

theorem plainEff_pc {w : ℕ} {i : Instr} (h : isPlain i = true) (s : State) :
    (plainEff w i s).pc = s.pc + 1 := by
  cases i <;> simp_all [isPlain, plainEff, Instr.effect]

theorem plainEff_input {w : ℕ} {i : Instr} (h : isPlain i = true) (s : State) :
    (plainEff w i s).input = s.input := by
  cases i <;> simp_all [isPlain, plainEff, Instr.effect]

theorem plainEff_inp {w : ℕ} {i : Instr} (h : isPlain i = true) (s : State) :
    (plainEff w i s).inp = s.inp := by
  cases i <;> simp_all [isPlain, plainEff, Instr.effect]

/-- Straight-line execution of a block of plain instructions. -/
def plainRun (w : ℕ) (blk : List Instr) (s : State) : State :=
  blk.foldl (fun s i => plainEff w i s) s

@[simp] theorem plainRun_nil (w : ℕ) (s : State) : plainRun w [] s = s := rfl

@[simp] theorem plainRun_cons (w : ℕ) (i : Instr) (blk : List Instr) (s : State) :
    plainRun w (i :: blk) s = plainRun w blk (plainEff w i s) := rfl

theorem plainRun_pc {w : ℕ} :
    ∀ (blk : List Instr) (s : State), (∀ i ∈ blk, isPlain i = true) →
      (plainRun w blk s).pc = s.pc + blk.length
  | [], s, _ => by simp
  | i :: blk, s, h => by
    rw [plainRun_cons, plainRun_pc blk _ (fun j hj => h j (by simp [hj])),
      plainEff_pc (h i (by simp))]
    simp; omega

theorem run_plain {w : ℕ} {P : Program} :
    ∀ (blk : List Instr) (s : State), (∀ i ∈ blk, isPlain i = true) → Contains P s.pc blk →
      run w P blk.length s = some (plainRun w blk s)
  | [], s, _, _ => rfl
  | i :: blk, s, h, hc => by
    have hi := h i (by simp)
    have h1 : step w P s = some (plainEff w i s) := by
      rw [step_of_fetch hc.head, effect_plain hi]
    have hc' : Contains P (plainEff w i s).pc blk := by
      rw [plainEff_pc hi]; exact hc.tail
    exact run_of_step h1 (run_plain blk _ (fun j hj => h j (by simp [hj])) hc')

end Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics
