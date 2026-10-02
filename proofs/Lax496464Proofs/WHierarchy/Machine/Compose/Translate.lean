import Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics

/-! The translation of a program into one that simulates it at word length `v` inside a machine of
word length `v + 2`.

Memory is interleaved by address modulo `4`: cell `a` of the simulated program lives at
`4 * a + o` (offset `o = 0` or `2`); cells `4 * i + 1` hold a buffer (a tape of numbers, entry `i`
at `4 * i + 1`); and the cells `3, 7, 11, 15` are reserved: `3` holds the mask `2 ^ v - 1`, `7` and
`11` are temporaries, `15` is the read pointer into a buffer used as input tape. Every arithmetic
result is masked (`and` with cell `3`), which reproduces the reduction modulo `2 ^ v`.

The simulated program reads its input either from the machine's own input (`native δ`: the
machine's input is the simulated input with `δ` entries in front, which the machine has already
consumed from its sequential tape) or from the buffer (`buffer`); it writes its output either to
the machine's output (`real`) or into the buffer (`buffer`: entry `0` of the buffer counts the
entries written, entry `i + 1` is the `i`-th output). -/

namespace Lax496464Proofs.WHierarchy.Machine.Compose.Translate

open Lax808846.Ram Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics

set_option genSizeOfSpec false in
/-- Where the simulated program's input comes from. -/
inductive InM
  /-- The machine's own input, with `δ` entries in front. -/
  | native (δ : ℕ)
  /-- The buffer, entry `i` at cell `4 * i + 1`, read pointer in cell `15`. -/
  | buffer
  deriving DecidableEq

set_option genSizeOfSpec false in
/-- Where the simulated program's output goes. -/
inductive OutM
  /-- The buffer: its length at cell `1`, entry `i` at cell `4 * (i + 1) + 1`. -/
  | buffer
  /-- The machine's output tape. -/
  | real
  deriving DecidableEq

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- A mode of simulation. -/
structure Mode where
  /-- The offset of the simulated memory. -/
  o : ℕ
  /-- The input source. -/
  inm : InM
  /-- The output target. -/
  outm : OutM

/-- The masking instruction: reduce cell `A` modulo `2 ^ v` (cell `3` holds `2 ^ v - 1`). -/
def msk (A : ℕ) : Instr := .and A A 3

/-- The translation of one instruction, given the labels of the simulated program's instructions
and the exit label (where the simulation continues when the simulated program halts). -/
def compileI (M : Mode) (lab : ℕ → ℕ) (ex : ℕ) : Instr → List Instr
  | .set a n => [.set (4 * a + M.o) n, msk (4 * a + M.o)]
  | .load a b =>
      [.set 7 4, .mul 7 7 (4 * b + M.o), .set 11 M.o, .add 7 7 11, .load (4 * a + M.o) 7,
        msk (4 * a + M.o)]
  | .store a b => [.set 7 4, .mul 7 7 (4 * a + M.o), .set 11 M.o, .add 7 7 11,
      .store 7 (4 * b + M.o)]
  | .add a b c => [.add (4 * a + M.o) (4 * b + M.o) (4 * c + M.o), msk (4 * a + M.o)]
  | .sub a b c => [.sub (4 * a + M.o) (4 * b + M.o) (4 * c + M.o), msk (4 * a + M.o)]
  | .mul a b c => [.mul (4 * a + M.o) (4 * b + M.o) (4 * c + M.o), msk (4 * a + M.o)]
  | .div a b c => [.div (4 * a + M.o) (4 * b + M.o) (4 * c + M.o), msk (4 * a + M.o)]
  | .and a b c => [.and (4 * a + M.o) (4 * b + M.o) (4 * c + M.o), msk (4 * a + M.o)]
  | .shiftl a b c => [.shiftl (4 * a + M.o) (4 * b + M.o) (4 * c + M.o), msk (4 * a + M.o)]
  | .not a b => [.not (4 * a + M.o) (4 * b + M.o), msk (4 * a + M.o)]
  | .jump l => [.jump (lab l)]
  | .jzero a l => [.jzero (4 * a + M.o) (lab l)]
  | .jeof l =>
      match M.inm with
      | .native _ => [.jeof (lab l)]
      | .buffer => [.set 11 1, .sub 7 15 1, .sub 7 11 7, .jzero 7 (lab l)]
  | .inputLength a =>
      match M.inm with
      | .native δ => [.inputLength (4 * a + M.o), .set 11 δ, .sub (4 * a + M.o) (4 * a + M.o) 11,
          msk (4 * a + M.o)]
      | .buffer => [.set 11 1, .add (4 * a + M.o) 1 11, msk (4 * a + M.o)]
  | .inputLoad a b =>
      match M.inm with
      | .native δ => [.set 11 δ, .add 7 (4 * b + M.o) 11, .inputLoad (4 * a + M.o) 7,
          msk (4 * a + M.o)]
      | .buffer => [.set 7 4, .mul 7 7 (4 * b + M.o), .set 11 1, .add 7 7 11,
          .load (4 * a + M.o) 7, msk (4 * a + M.o)]
  | .halt => [.jump ex]
  | .read a =>
      match M.inm with
      | .native _ => [.jeof ex, .read (4 * a + M.o), msk (4 * a + M.o)]
      | .buffer => [.set 11 1, .sub 7 15 1, .sub 7 11 7, .jzero 7 ex, .set 7 4, .mul 7 7 15,
          .add 7 7 11, .load (4 * a + M.o) 7, .add 15 15 11, msk (4 * a + M.o)]
  | .write a =>
      match M.outm with
      | .real => [.write (4 * a + M.o)]
      | .buffer => [.set 7 4, .mul 7 7 1, .set 11 5, .add 7 7 11, .store 7 (4 * a + M.o),
          .set 11 1, .add 1 1 11]

/-- The length of a translated instruction (it does not depend on the labels). -/
def blen (M : Mode) (i : Instr) : ℕ := (compileI M (fun _ => 0) 0 i).length

theorem length_compileI (M : Mode) (lab : ℕ → ℕ) (ex : ℕ) (i : Instr) :
    (compileI M lab ex i).length = blen M i := by
  unfold blen
  cases i <;> simp only [compileI] <;>
    first
    | rfl
    | (cases M.inm <;> rfl)

/-- The position of the translation of instruction `l` relative to the start of the translated
program. -/
def pos (M : Mode) (p : Program) (l : ℕ) : ℕ := ((p.take l).map (blen M)).sum

/-- The label of instruction `l` when the translation starts at `b`. -/
def labOf (M : Mode) (p : Program) (b l : ℕ) : ℕ := b + pos M p l

/-- The exit label: just after the translation. -/
def exitOf (M : Mode) (p : Program) (b : ℕ) : ℕ := labOf M p b p.length

/-- The translated program, placed at position `b`, exiting to `exitOf M p b`. -/
def compileProg (M : Mode) (p : Program) (b : ℕ) : List Instr :=
  (p.map (compileI M (labOf M p b) (exitOf M p b))).flatten

theorem pos_succ (M : Mode) (p : Program) {l : ℕ} (hl : l < p.length) :
    pos M p (l + 1) = pos M p l + blen M p[l] := by
  simp only [pos]
  rw [List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hl]
  simp

theorem pos_of_le (M : Mode) (p : Program) {l : ℕ} (hl : p.length ≤ l) :
    pos M p l = pos M p p.length := by
  simp [pos, List.take_of_length_le hl]

theorem labOf_succ (M : Mode) (p : Program) (b : ℕ) {l : ℕ} (hl : l < p.length) :
    labOf M p b (l + 1) = labOf M p b l + blen M p[l] := by
  simp [labOf, pos_succ M p hl]; omega

theorem labOf_of_le (M : Mode) (p : Program) (b : ℕ) {l : ℕ} (hl : p.length ≤ l) :
    labOf M p b l = exitOf M p b := by
  simp [labOf, exitOf, pos_of_le M p hl]

theorem labOf_zero (M : Mode) (p : Program) (b : ℕ) : labOf M p b 0 = b := by
  simp [labOf, pos]

theorem length_compileProg (M : Mode) (p : Program) (b : ℕ) :
    (compileProg M p b).length = pos M p p.length := by
  simp [compileProg, pos, List.length_flatten, Function.comp_def, length_compileI]

theorem exitOf_eq (M : Mode) (p : Program) (b : ℕ) :
    exitOf M p b = b + (compileProg M p b).length := by
  simp [exitOf, labOf, length_compileProg]

/-- Entries of a flattened list. -/
theorem getElem?_flatten_sum {α : Type} :
    ∀ (L : List (List α)) (n : ℕ) (hn : n < L.length) (j : ℕ), j < L[n].length →
      L.flatten[((L.take n).map List.length).sum + j]? = L[n][j]?
  | [], n, hn, _, _ => by simp at hn
  | l :: L, 0, _, j, hj => by
    simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons,
      List.getElem_cons_zero]
    rw [List.getElem?_append_left (by simpa using hj)]
  | l :: L, n + 1, hn, j, hj => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons,
      List.getElem_cons_succ]
    rw [Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
    exact getElem?_flatten_sum L n (by simpa using hn) j hj

/-- The translation of instruction `pc` sits at its label. -/
theorem contains_instr {P : Program} {M : Mode} {p : Program} {b : ℕ}
    (hP : Contains P b (compileProg M p b)) {pc : ℕ} (hpc : pc < p.length) :
    Contains P (labOf M p b pc) (compileI M (labOf M p b) (exitOf M p b) p[pc]) := by
  intro j hj
  set L := p.map (compileI M (labOf M p b) (exitOf M p b)) with hL
  have hn : pc < L.length := by simp [hL, hpc]
  have hLn : L[pc] = compileI M (labOf M p b) (exitOf M p b) p[pc] := by simp [hL]
  have hsum : ((L.take pc).map List.length).sum = pos M p pc := by
    simp [hL, pos, List.map_take, Function.comp_def, length_compileI]
  have key := getElem?_flatten_sum L pc hn j (by rw [hLn]; exact hj)
  rw [hsum, hLn] at key
  have hlt : pos M p pc + j < (compileProg M p b).length := by
    have : (compileProg M p b)[pos M p pc + j]?.isSome := by
      simp only [compileProg]; rw [← hL, key]; simp [hj]
    simpa using this
  have := hP (pos M p pc + j) hlt
  rw [labOf, Nat.add_assoc, this]
  simp only [compileProg]; rw [← hL, key]

/-! ### Literal cell addresses -/

/-- The largest cell address written literally in an instruction. -/
def maxLit : Instr → ℕ
  | .set a _ => a
  | .load a b => max a b
  | .store a b => max a b
  | .add a b c => max a (max b c)
  | .sub a b c => max a (max b c)
  | .mul a b c => max a (max b c)
  | .div a b c => max a (max b c)
  | .and a b c => max a (max b c)
  | .shiftl a b c => max a (max b c)
  | .not a b => max a b
  | .jzero a _ => a
  | .inputLength a => a
  | .inputLoad a b => max a b
  | .read a => a
  | .write a => a
  | _ => 0

/-- A bound on the literal cell addresses of a program. -/
def lits (p : Program) : ℕ := (p.map maxLit).sum

theorem maxLit_le_lits {p : Program} {i : Instr} (h : i ∈ p) : maxLit i ≤ lits p :=
  List.le_sum_of_mem (List.mem_map_of_mem h)

end Lax496464Proofs.WHierarchy.Machine.Compose.Translate
