import Lax496464Proofs.WHierarchy.Machine.Compose.SimRun

/-! The two programs built from the simulation.

* `compose p1 p2` runs `p1` on its own input, keeping the output in the buffer, and then `p2` on the
  buffer (with its length in front), writing `p2`'s output: at word length `v + 2` it computes what
  `p2` computes at word length `v` on the output of `p1` at word length `v`.
* `strip p` runs `p` on the input `x` when handed the tape `x.length :: x`. -/

namespace Lax496464Proofs.WHierarchy.Machine.Compose.Programs

open Lax808846.Ram Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics
open Lax496464Proofs.WHierarchy.Machine.Compose.Translate Lax496464Proofs.WHierarchy.Machine.Compose.Rel
open Lax496464Proofs.WHierarchy.Machine.Compose.StepOther Lax496464Proofs.WHierarchy.Machine.Compose.SimRun

/-- The mode of the first program of a composition. -/
def M1 : Mode := ⟨0, .native 0, .buffer⟩

/-- The mode of the second program of a composition. -/
def M2 : Mode := ⟨2, .buffer, .real⟩

/-- The mode of a program run on the tape without its length. -/
def MS : Mode := ⟨0, .native 1, .real⟩

theorem valid_M1 : Valid M1 :=
  ⟨Or.inl rfl, fun δ h => by simp [M1] at h; omega, fun h => by simp [M1] at h⟩

theorem valid_M2 : Valid M2 := ⟨Or.inr rfl, fun δ h => by simp [M2] at h, fun _ => rfl⟩

theorem valid_MS : Valid MS :=
  ⟨Or.inl rfl, fun δ h => by simp [MS] at h; omega, fun h => by simp [MS] at h⟩

/-- Computing the mask `2 ^ v - 1` into cell `3` at word length `v + 2`. -/
def prologue : List Instr := [.not 3 3, .set 7 4, .div 3 3 7]

/-- The composition. -/
def compose (p1 p2 : Program) : Program :=
  prologue ++ compileProg M1 p1 3 ++
    compileProg M2 p2 (3 + (compileProg M1 p1 3).length)

/-- The program reading its tape without the leading length. -/
def strip (p : Program) : Program :=
  (prologue ++ [.read 7]) ++ compileProg MS p 4

theorem contains_self (P : Program) : Contains P 0 P := by
  intro j hj; simp

theorem Contains.congr {P : Program} {pc pc' : ℕ} {blk : List Instr} (h : Contains P pc blk)
    (e : pc = pc') : Contains P pc' blk := e ▸ h

/-- The state after the prologue. -/
theorem prologue_run {v : ℕ} (hv : 2 ≤ v) {P : Program} (hP : Contains P 0 prologue)
    (X : List ℕ) :
    ∃ S0, run (v + 2) P 3 (initState X) = some S0 ∧ S0.pc = 3 ∧ S0.input = X ∧ S0.inp = X ∧
      S0.out = [] ∧ S0.mem 3 = 2 ^ v - 1 ∧ ∀ c, c ≠ 3 → c ≠ 7 → S0.mem c = 0 := by
  have hpl : ∀ i ∈ prologue, isPlain i = true := by simp [prologue, isPlain]
  have hrun := run_plain (w := v + 2) _ (initState X) hpl hP
  refine ⟨_, hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [plainRun_pc _ _ hpl]; rfl
  · exact plainRun_input _ _ hpl
  · exact plainRun_inp _ _ hpl
  · simp [prologue, plainEff, Instr.effect, initState]
  · have h3 := small_mod hv (by norm_num : 3 < 16)
    have h7 := small_mod hv (by norm_num : 7 < 16)
    have h4 := small_mod hv (by norm_num : 4 < 16)
    have hp : 2 ^ (v + 2) = 4 * 2 ^ v := by ring
    have hpos : 0 < 2 ^ v := by positivity
    have hq : (2 ^ (v + 2) - 1) / 4 = 2 ^ v - 1 := by omega
    have hq' : (2 ^ (v + 2) - 1) % 2 ^ (v + 2) = 2 ^ (v + 2) - 1 := Nat.mod_eq_of_lt (by omega)
    have hq'' : (2 ^ v - 1) % 2 ^ (v + 2) = 2 ^ v - 1 := Nat.mod_eq_of_lt (by omega)
    simp [prologue, plainEff, Instr.effect, initState, setCell, h3, h7, h4, hq', hq, hq'']
  · intro c h3 h7
    simp [prologue, plainEff, Instr.effect, initState, setCell, small_mod hv (by norm_num : 3 < 16),
      small_mod hv (by norm_num : 7 < 16), h3, h7]

/-! ### The composition -/

section
variable (p1 p2 : Program)

/-- Where the second translation starts. -/
def base2 : ℕ := 3 + (compileProg M1 p1 3).length

theorem contains_prologue : Contains (compose p1 p2) 0 prologue :=
  (contains_self _).left.left

theorem contains_first : Contains (compose p1 p2) 3 (compileProg M1 p1 3) :=
  Contains.congr (contains_self (compose p1 p2)).left.right (by simp [prologue])

theorem contains_second : Contains (compose p1 p2) (base2 p1) (compileProg M2 p2 (base2 p1)) :=
  Contains.congr (contains_self (compose p1 p2)).right (by simp [prologue, base2]; omega)

theorem exit_first : exitOf M1 p1 3 = base2 p1 := by rw [exitOf_eq]; rfl

theorem exit_second : exitOf M2 p2 (base2 p1) = (compose p1 p2).length := by
  rw [exitOf_eq]; simp [compose, prologue, base2]; omega

end

/-- **The composition computes the composite.** If `p1` runs to `y` on `X` and `p2` runs to `z` on
`y.length :: y`, both at word length `v`, then `compose p1 p2` runs to `z` on `X` at word length
`v + 2`, within `3 + 10 (t1 + t2)` steps. -/
theorem compose_runsTo {v : ℕ} (hv : 2 ≤ v) {p1 p2 : Program} (hl1 : lits p1 < 2 ^ v)
    (hl2 : lits p2 < 2 ^ v) {X y z : List ℕ} {t1 t2 : ℕ} (hX : X.length < 2 ^ (v + 2))
    (hy : y.length + 1 < 2 ^ v) (h1 : RunsTo v p1 X y t1)
    (h2 : RunsTo v p2 (y.length :: y) z t2) :
    ∃ t ≤ 3 + 10 * (t1 + t2), RunsTo (v + 2) (compose p1 p2) X z t := by
  obtain ⟨S0, hrun0, hpc0, hi0, hp0, ho0, hm3, hm0⟩ :=
    prologue_run hv (contains_prologue p1 p2) X
  -- the first program
  have hR0 : Sim M1 v (initState X) S0 := by
    refine ⟨⟨fun a ha => ?_, fun a => ?_, hm3⟩, ⟨⟨[], by simp [hi0, initState], rfl⟩,
      by simp [hp0, initState], by simpa [initState] using hX⟩, ⟨ho0, fun i hi => ?_⟩⟩
    · simp only [M1, Nat.add_zero, initState]; exact hm0 _ (by omega) (by omega)
    · simp [initState]
    · rw [hm0 _ (by omega) (by omega)]
      rcases i with _ | i <;> simp [initState]
  obtain ⟨k1, hk1, sf1, S1, hrun1, hpc1, hy1, hR1, hfr1⟩ :=
    sim_runsTo valid_M1 hv (contains_first p1 p2) hl1 h1 hR0 hpc0 (fun _ => by omega)
  rw [exit_first] at hpc1
  -- the second program
  have hR1' : Sim M2 v (initState (y.length :: y)) S1 := by
    have hout := hR1.outr
    simp only [M1, OutRel] at hout
    obtain ⟨hout1, hbuf⟩ := hout
    rw [hy1] at hbuf
    have hnw : ∀ c, c % 4 ≠ 0 → c % 4 ≠ 1 → c ≠ 7 → c ≠ 11 → S1.mem c = S0.mem c := by
      intro c e0 e1 e7 e11
      apply hfr1
      simp only [Wr, M1]
      intro h
      rcases h with h | h | h | ⟨-, h⟩ | ⟨h, -⟩
      · exact e0 h
      · exact e7 h
      · exact e11 h
      · exact e1 h
      · cases h
    refine ⟨⟨fun a ha => ?_, fun a => ?_, hR1.core.mask⟩, ⟨⟨y, rfl⟩, hbuf, by simpa [initState] using hy,
      ?_, ?_⟩, ?_⟩
    · simp only [M2, initState]
      rw [hnw _ (by omega) (by omega) (by omega) (by omega), hm0 _ (by omega) (by omega)]
    · simp [initState]
    · show S1.mem 15 ≤ _
      rw [hnw 15 (by omega) (by omega) (by omega) (by omega), hm0 15 (by omega) (by omega)]
      simp
    · show (y.length :: y) = List.drop (S1.mem 15) (y.length :: y)
      rw [hnw 15 (by omega) (by omega) (by omega) (by omega), hm0 15 (by omega) (by omega)]
      rfl
    · show S1.out = []
      exact hout1
  obtain ⟨k2, hk2, sf2, S2, hrun2, hpc2, hz2, hR2, -⟩ :=
    sim_runsTo valid_M2 hv (contains_second p1 p2) hl2 h2 hR1' hpc1 (fun h => by cases h)
  rw [exit_second] at hpc2
  have hout2 : S2.out = z := by
    have := hR2.outr
    simp only [M2, OutRel] at this
    rw [this, hz2]
  refine ⟨3 + k1 + k2 + 0, by omega, 3 + k1 + k2, S2, run_trans (run_trans hrun0 hrun1) hrun2,
    ?_, hout2, ?_⟩
  · simp [step, hpc2]
  · simp [terminalCost, hpc2]

/-! ### Stripping the length -/

theorem contains_prologue' (p : Program) : Contains (strip p) 0 (prologue ++ [.read 7]) :=
  (contains_self _).left

theorem contains_strip (p : Program) : Contains (strip p) 4 (compileProg MS p 4) :=
  Contains.congr (contains_self (strip p)).right (by simp [prologue])

theorem exit_strip (p : Program) : exitOf MS p 4 = (strip p).length := by
  rw [exitOf_eq]; simp [strip, prologue]; omega

/-- **Stripping the length.** If `p` runs to `y` on `x` at word length `v`, then `strip p` runs
to `y` on `x.length :: x` at word length `v + 2`, within `4 + 10 t` steps. -/
theorem strip_runsTo {v : ℕ} (hv : 2 ≤ v) {p : Program} (hl : lits p < 2 ^ v) {x y : List ℕ}
    {t : ℕ} (hx : x.length + 1 < 2 ^ (v + 2)) (h : RunsTo v p x y t) :
    ∃ t' ≤ 4 + 10 * t, RunsTo (v + 2) (strip p) (x.length :: x) y t' := by
  have hc := contains_prologue' p
  obtain ⟨S0, hrun0, hpc0, hi0, hp0, ho0, hm3, hm0⟩ := prologue_run hv hc.left (x.length :: x)
  -- reading the length
  have hf : (strip p)[S0.pc]? = some (.read 7) := by
    rw [hpc0]; simpa [prologue] using hc.right.head
  set S0' : State := { S0 with
    pc := S0.pc + 1
    mem := setCell (v + 2) S0.mem 7 x.length
    inp := x } with hS0'
  have hst : step (v + 2) (strip p) S0 = some S0' := by
    rw [step_of_fetch hf]; simp [Instr.effect, hp0, hS0']
  have h7 := small_lt hv (by norm_num : 7 < 16)
  have hR0 : Sim MS v (initState x) S0' := by
    refine ⟨⟨fun a ha => ?_, fun a => ?_, ?_⟩, ⟨⟨[x.length], by simp [hS0', hi0, initState], rfl⟩,
      by simp [hS0', initState], by simpa [initState, Nat.add_comm] using hx⟩, ?_⟩
    · simp only [MS, Nat.add_zero, initState, hS0']
      rw [setCell_apply h7, if_neg (by omega)]; exact hm0 _ (by omega) (by omega)
    · simp [initState]
    · simp only [hS0']; rw [setCell_apply h7, if_neg (by omega)]; exact hm3
    · show S0'.out = []
      simp [hS0', ho0]
  obtain ⟨k, hk, sf, S1, hrun1, hpc1, hy1, hR1, -⟩ :=
    sim_runsTo valid_MS hv (contains_strip p) hl h hR0 (by simp [hS0', hpc0])
      (fun h => by cases h)
  rw [exit_strip] at hpc1
  have hout : S1.out = y := by
    have := hR1.outr
    simp only [MS, OutRel] at this
    rw [this, hy1]
  refine ⟨3 + 1 + k + 0, by omega, 3 + 1 + k, S1,
    run_trans (run_trans hrun0 (run_one hst)) hrun1, ?_, hout, ?_⟩
  · simp [step, hpc1]
  · simp [terminalCost, hpc1]

end Lax496464Proofs.WHierarchy.Machine.Compose.Programs
