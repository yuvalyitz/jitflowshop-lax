import Lax496464Proofs.WHierarchy.Machine.Compose.StepOther

/-! The simulation of whole runs: one simulated step is at most ten machine steps, a halting
simulated program reaches the exit label, and a run of the simulated program to its output is
simulated by a run of the machine to the exit label. -/

namespace Lax496464Proofs.WHierarchy.Machine.Compose.SimRun

open Lax808846.Ram Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics
open Lax496464Proofs.WHierarchy.Machine.Compose.Translate Lax496464Proofs.WHierarchy.Machine.Compose.Rel
open Lax496464Proofs.WHierarchy.Machine.Compose.StepMasked Lax496464Proofs.WHierarchy.Machine.Compose.StepOther

section
variable {M : Mode} {v : ℕ} {P p : Program} {b : ℕ}

theorem lits_lt {i : Instr} (hlit : lits p < 2 ^ v) {pc : ℕ} (hpc : pc < p.length)
    (hi : p[pc] = i) : maxLit i < 2 ^ v :=
  lt_of_le_of_lt (maxLit_le_lits (hi ▸ List.getElem_mem hpc)) hlit

/-- **One step.** -/
theorem sim_step (hM : Valid M) (hv : 2 ≤ v) (hP : Contains P b (compileProg M p b))
    (hlit : lits p < 2 ^ v) {s s' S : State} (hR : Sim M v s S)
    (hpc : S.pc = labOf M p b s.pc) (hs : step v p s = some s')
    (hout : M.outm = .buffer → s'.out.length < 2 ^ v) :
    StepOK M v P (labOf M p b) s' S := by
  have hlt : s.pc < p.length := by
    by_contra h
    simp [step, List.getElem?_eq_none (by omega : p.length ≤ s.pc)] at hs
  have hc := contains_instr hP hlt
  rw [← hpc] at hc
  have hlab := labOf_succ M p b hlt
  rw [← hpc] at hlab
  simp only [step, List.getElem?_eq_getElem hlt, Option.bind_some] at hs
  have hml := lits_lt hlit hlt rfl
  generalize p[s.pc] = i at hc hlab hs hml
  cases i with
  | set a n =>
    exact stepOK_set hM hv hR (by simpa [maxLit] using hml) hc hlab hs
  | load a b' =>
    simp only [maxLit, max_lt_iff] at hml
    exact stepOK_load hM hv hR hml.1 hml.2 hc hlab hs
  | store a b' =>
    simp only [maxLit, max_lt_iff] at hml
    exact stepOK_store hM hv hR hml.1 hml.2 hc hlab hs
  | add a b' c =>
    simp only [maxLit, max_lt_iff] at hml
    exact stepOK_bin hM hv hR Instr.add (· + ·) (fun _ _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ _ => by simp) hml.1 hml.2.1 hml.2.2 hc hlab hs
  | sub a b' c =>
    simp only [maxLit, max_lt_iff] at hml
    exact stepOK_bin hM hv hR Instr.sub (· - ·) (fun _ _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ _ => by simp) hml.1 hml.2.1 hml.2.2 hc hlab hs
  | mul a b' c =>
    simp only [maxLit, max_lt_iff] at hml
    exact stepOK_bin hM hv hR Instr.mul (· * ·) (fun _ _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ _ => by simp) hml.1 hml.2.1 hml.2.2 hc hlab hs
  | div a b' c =>
    simp only [maxLit, max_lt_iff] at hml
    exact stepOK_bin hM hv hR Instr.div (· / ·) (fun _ _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ _ => by simp) hml.1 hml.2.1 hml.2.2 hc hlab hs
  | and a b' c =>
    simp only [maxLit, max_lt_iff] at hml
    exact stepOK_bin hM hv hR Instr.and Nat.land (fun _ _ _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ _ => by simp) hml.1 hml.2.1 hml.2.2 hc hlab hs
  | shiftl a b' c =>
    simp only [maxLit, max_lt_iff] at hml
    exact stepOK_bin hM hv hR Instr.shiftl (fun x y => x * 2 ^ y) (fun _ _ _ _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ _ => by simp) hml.1 hml.2.1 hml.2.2 hc hlab hs
  | not a b' =>
    simp only [maxLit, max_lt_iff] at hml
    exact stepOK_not hM hv hR hml.1 hml.2 hc hlab hs
  | jump l => exact stepOK_jump hM hR hc hs
  | jzero a l =>
    exact stepOK_jzero hM hR (by simpa [maxLit] using hml) hc hlab hs
  | jeof l =>
    cases hm : M.inm with
    | native δ =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_jeof_native hM hR hm hc hlab hs
    | buffer =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_jeof_buffer hM hv hR hm hc hlab hs
  | inputLength a =>
    have ha : a < 2 ^ v := by simpa [maxLit] using hml
    cases hm : M.inm with
    | native δ =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_inputLength_native hM hv hR hm ha hc hlab hs
    | buffer =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_inputLength_buffer hM hv hR hm ha hc hlab hs
  | inputLoad a b' =>
    simp only [maxLit, max_lt_iff] at hml
    cases hm : M.inm with
    | native δ =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_inputLoad_native hM hv hR hm hml.1 hml.2 hc hlab hs
    | buffer =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_inputLoad_buffer hM hv hR hm hml.1 hml.2 hc hlab hs
  | halt => simp [Instr.effect] at hs
  | read a =>
    have ha : a < 2 ^ v := by simpa [maxLit] using hml
    cases hm : M.inm with
    | native δ =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_read_native hM hv hR hm ha hc hlab hs
    | buffer =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_read_buffer hM hv hR hm ha hc hlab hs
  | write a =>
    have ha : a < 2 ^ v := by simpa [maxLit] using hml
    cases hm : M.outm with
    | real =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_write_real hM hR hm ha hc hlab hs
    | buffer =>
      simp only [compileI, blen, hm, List.length_cons, List.length_nil] at hc hlab
      exact stepOK_write_buffer hM hv hR hm ha hc hlab hs (hout hm)

/-- **Halting.** When the simulated program halts, the machine reaches the exit label within
four steps (none when the simulated program ran past its end), changing only temporaries. -/
theorem sim_halt (hv : 2 ≤ v) (hP : Contains P b (compileProg M p b))
    {s S : State} (hR : Sim M v s S) (hpc : S.pc = labOf M p b s.pc) (hs : step v p s = none) :
    ∃ k ≤ 4 * terminalCost p s, ∃ S', run (v + 2) P k S = some S' ∧
      S'.pc = exitOf M p b ∧ S'.input = S.input ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      ∀ c, c ≠ 7 → c ≠ 11 → S'.mem c = S.mem c := by
  by_cases hlt : s.pc < p.length
  · have hc := contains_instr hP hlt
    rw [← hpc] at hc
    have htc : terminalCost p s = 1 := by simp [terminalCost, hlt]
    rw [htc]
    simp only [step, List.getElem?_eq_getElem hlt, Option.bind_some] at hs
    generalize p[s.pc] = i at hc hs
    cases i with
    | halt =>
      simp only [compileI] at hc
      refine ⟨1, by norm_num, { S with pc := exitOf M p b }, ?_, rfl, rfl, rfl, rfl,
        fun _ _ _ => rfl⟩
      exact run_one (by rw [step_of_fetch hc.head]; rfl)
    | read a =>
      simp only [Instr.effect] at hs
      have hsi : s.inp = [] := by
        rcases h : s.inp with _ | ⟨x, l⟩
        · rfl
        · rw [h] at hs; simp at hs
      cases hm : M.inm with
      | native δ =>
        simp only [compileI, hm] at hc
        have hin := hR.inr
        rw [hm] at hin
        obtain ⟨-, hinp, -⟩ := hin
        refine ⟨1, by norm_num, { S with pc := exitOf M p b }, ?_, rfl, rfl, rfl, rfl,
          fun _ _ _ => rfl⟩
        exact run_one (by rw [step_of_fetch hc.head]; simp [Instr.effect, hinp, hsi])
      | buffer =>
        simp only [compileI, hm] at hc
        obtain ⟨hz, -, hfr, hi, hp, ho, hpc1⟩ := eof_block hv hR hm
        have hpl : ∀ i ∈ [Instr.set 11 1, .sub 7 15 1, .sub 7 11 7], isPlain i = true := by
          simp [isPlain]
        have hc' : Contains P S.pc ([.set 11 1, .sub 7 15 1, .sub 7 11 7] ++
            [.jzero 7 (exitOf M p b)] ++ _) := hc
        have hrun1 := run_plain (w := v + 2) _ _ hpl hc'.left.left
        set S1 := plainRun (v + 2) [.set 11 1, .sub 7 15 1, .sub 7 11 7] S
        have hst : step (v + 2) P S1 = some { S1 with pc := exitOf M p b } := by
          have := hc'.left.right.head
          rw [step_of_fetch (by rw [hpc1]; simpa using this)]
          simp [Instr.effect, small_mod hv (by norm_num : 7 < 16), hz.mpr hsi]
        exact ⟨4, le_rfl, _, run_trans hrun1 (run_one hst), rfl, hi, hp, ho,
          fun c h7 h11 => hfr c h7 h11⟩
    | _ => simp [Instr.effect] at hs
  · have htc : terminalCost p s = 0 := by simp [terminalCost, hlt]
    rw [htc]
    exact ⟨0, le_rfl, S, rfl, by rw [hpc, labOf_of_le M p b (by omega)], rfl, rfl, rfl,
      fun _ _ _ => rfl⟩

/-- **Runs.** -/
theorem sim_run (hM : Valid M) (hv : 2 ≤ v) (hP : Contains P b (compileProg M p b))
    (hlit : lits p < 2 ^ v) :
    ∀ (k : ℕ) (s S sf : State), Sim M v s S → S.pc = labOf M p b s.pc →
      run v p k s = some sf → (M.outm = .buffer → sf.out.length < 2 ^ v) →
      ∃ k' ≤ 10 * k, ∃ S', run (v + 2) P k' S = some S' ∧ S'.pc = labOf M p b sf.pc ∧
        Sim M v sf S' ∧ Frame M S S'
  | 0, s, S, sf, hR, hpc, hrun, _ => by
    simp only [run, Option.some.injEq] at hrun
    subst hrun
    exact ⟨0, le_rfl, S, rfl, hpc, hR, Frame.refl M S⟩
  | k + 1, s, S, sf, hR, hpc, hrun, hout => by
    rw [run_succ] at hrun
    rcases hs : step v p s with _ | s1
    · rw [hs] at hrun; simp at hrun
    rw [hs] at hrun
    simp only [Option.bind_some] at hrun
    have hle := run_out_prefix hrun
    obtain ⟨k1, hk1, S1, hrun1, hpc1, hR1, hfr1⟩ :=
      sim_step hM hv hP hlit hR hpc hs (fun h => lt_of_le_of_lt hle (hout h))
    obtain ⟨k2, hk2, S2, hrun2, hpc2, hR2, hfr2⟩ :=
      sim_run hM hv hP hlit k s1 S1 sf hR1 hpc1 hrun hout
    exact ⟨k1 + k2, by omega, S2, run_trans hrun1 hrun2, hpc2, hR2, hfr1.trans hfr2⟩

/-- **A run to an output.** A run of the simulated program from its initial state is simulated by
a run of the machine from a related state at the start of the translation to the exit label,
within ten machine steps per simulated step. -/
theorem sim_runsTo (hM : Valid M) (hv : 2 ≤ v) (hP : Contains P b (compileProg M p b))
    (hlit : lits p < 2 ^ v) {x y : List ℕ} {t : ℕ} (h : RunsTo v p x y t) {S0 : State}
    (hR : Sim M v (initState x) S0) (hpc : S0.pc = b)
    (hout : M.outm = .buffer → y.length < 2 ^ v) :
    ∃ k ≤ 10 * t, ∃ (sf S' : State), run (v + 2) P k S0 = some S' ∧ S'.pc = exitOf M p b ∧
      sf.out = y ∧ Sim M v sf S' ∧ Frame M S0 S' := by
  obtain ⟨k, sf, hrun, hstop, hy, ht⟩ := h
  obtain ⟨k1, hk1, S1, hrun1, hpc1, hR1, hfr1⟩ :=
    sim_run hM hv hP hlit k (initState x) S0 sf hR (by rw [hpc]; simp [initState, labOf_zero])
      hrun (fun h => hy ▸ hout h)
  obtain ⟨k2, hk2, S2, hrun2, hpc2, hi, hp, ho, hm⟩ := sim_halt hv hP hR1 hpc1 hstop
  obtain ⟨hR2, hfr2⟩ := sim_frame hM (s' := sf) hR1 rfl rfl rfl rfl hi hp ho hm
  exact ⟨k1 + k2, by rw [ht]; omega, sf, S2, run_trans hrun1 hrun2, hpc2, hy, hR2,
    hfr1.trans hfr2⟩

end

end Lax496464Proofs.WHierarchy.Machine.Compose.SimRun
