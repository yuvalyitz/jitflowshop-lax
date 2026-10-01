import Lax496464Proofs.WHierarchy.Machine.Compose.StepMasked

/-! Simulation of the remaining instructions: `store`, the jumps, and the input and output
instructions (in their non-halting cases). -/

namespace Lax496464Proofs.WHierarchy.Machine.Compose.StepOther

open Lax808846.Ram Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics
open Lax496464Proofs.WHierarchy.Machine.Compose.Translate Lax496464Proofs.WHierarchy.Machine.Compose.Rel
open Lax496464Proofs.WHierarchy.Machine.Compose.StepMasked

/-! ### Generic preservation lemmas -/

/-- Changing only temporaries and the counter preserves the relation. -/
theorem sim_frame {M : Mode} (hM : Valid M) {v : ℕ} {s s' S S' : State} (hR : Sim M v s S)
    (hm : s'.mem = s.mem) (hi : s'.input = s.input) (hp : s'.inp = s.inp) (ho : s'.out = s.out)
    (Hi : S'.input = S.input) (Hp : S'.inp = S.inp) (Ho : S'.out = S.out)
    (hfr : ∀ c, c ≠ 7 → c ≠ 11 → S'.mem c = S.mem c) : Sim M v s' S' ∧ Frame M S S' := by
  refine ⟨⟨⟨fun a ha => ?_, fun a => ?_, ?_⟩, hR.inr.frame hi hp Hi Hp ?_,
    hR.outr.frame ho Ho ?_⟩, ?_⟩
  · obtain ⟨e1, e2, -, -, -⟩ := cell_ne hM a
    rw [hm, hfr _ e1 e2]; exact hR.core.mem a ha
  · rw [hm]; exact hR.core.val a
  · rw [hfr 3 (by omega) (by omega)]; exact hR.core.mask
  · intro c hc; exact hfr c (by omega) (by omega)
  · intro c hc; exact hfr c (by omega) (by omega)
  · intro c hc
    simp only [Wr, not_or] at hc
    exact hfr c hc.2.1 hc.2.2.1

/-- Writing a word into the cell of a simulated address preserves the relation. -/
theorem sim_write {M : Mode} (hM : Valid M) {v : ℕ} {s s' S S' : State} (hR : Sim M v s S)
    {x val : ℕ} (hx : x < 2 ^ v) (hval : val < 2 ^ v)
    (hm : s'.mem = setCell v s.mem x val) (hi : s'.input = s.input) (hp : s'.inp = s.inp)
    (ho : s'.out = s.out)
    (Hi : S'.input = S.input) (Hp : S'.inp = S.inp) (Ho : S'.out = S.out)
    (h1 : S'.mem (4 * x + M.o) = val)
    (hfr : ∀ c, c ≠ 4 * x + M.o → c ≠ 7 → c ≠ 11 → S'.mem c = S.mem c) :
    Sim M v s' S' ∧ Frame M S S' := by
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM x
  have hxm : x % 2 ^ v = x := Nat.mod_eq_of_lt hx
  refine ⟨⟨⟨fun a ha => ?_, fun a => ?_, ?_⟩, hR.inr.frame hi hp Hi Hp ?_,
    hR.outr.frame ho Ho ?_⟩, ?_⟩
  · rw [hm]
    simp only [setCell, hxm]
    by_cases h : a = x
    · subst h; rw [if_pos rfl, h1, Nat.mod_eq_of_lt hval]
    · rw [if_neg h, hfr _ (by omega) ?_ ?_]
      · exact hR.core.mem a ha
      · rcases hM.o with h | h <;> rw [h] <;> omega
      · rcases hM.o with h | h <;> rw [h] <;> omega
  · rw [hm]; simp only [setCell]
    split_ifs
    · exact Nat.mod_lt _ (by positivity)
    · exact hR.core.val a
  · rw [hfr 3 hne3.symm (by omega) (by omega)]; exact hR.core.mask
  · intro c hc
    have hA' : c ≠ 4 * x + M.o := by
      rcases hc with hc | hc
      · intro h; rw [h] at hc; exact hne1 hc
      · rw [hc]; exact hne15.symm
    exact hfr c hA' (by omega) (by omega)
  · intro c hc
    have hA' : c ≠ 4 * x + M.o := by intro h; rw [h] at hc; exact hne1 hc
    exact hfr c hA' (by omega) (by omega)
  · intro c hc
    simp only [Wr, not_or] at hc
    have hA' : c ≠ 4 * x + M.o := by
      intro h; apply hc.1; rw [h]; rcases hM.o with h' | h' <;> rw [h'] <;> omega
    exact hfr c hA' hc.2.1 hc.2.2.1

/-- A final mask after arbitrary machine steps that computed the value (and may have changed the
inputs, the read pointer and the output as the relation requires). -/
theorem mask_tail {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {S S1 s s' : State} {a r r' k : ℕ} (hR : Sim M v s S) (ha : a < 2 ^ v)
    (hrun : run (v + 2) P k S = some S1) (hc : P[S1.pc]? = some (msk (4 * a + M.o)))
    (h1 : S1.mem (4 * a + M.o) = r % 2 ^ (v + 2))
    (hfr : ∀ c, c ≠ 4 * a + M.o → c ≠ 7 → c ≠ 11 → c ≠ 15 → S1.mem c = S.mem c)
    (h15 : M.inm ≠ .buffer → S1.mem 15 = S.mem 15)
    (hmem' : s'.mem = setCell v s.mem a r') (hr : r % 2 ^ v = r' % 2 ^ v)
    (hin : InRel v M.inm s' S1) (hout : OutRel v M.outm s' S1) :
    ∃ S2, run (v + 2) P (k + 1) S = some S2 ∧ S2.pc = S1.pc + 1 ∧ Sim M v s' S2 ∧
      Frame M S S2 := by
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
  have hA := four_mul_lt (o := M.o) ha (by rcases hM.o with h | h <;> omega)
  have hav : a % 2 ^ v = a := Nat.mod_eq_of_lt ha
  have h3 : S1.mem 3 = 2 ^ v - 1 := by
    rw [hfr 3 hne3.symm (by omega) (by omega) (by omega)]; exact hR.core.mask
  have hstep : step (v + 2) P S1 = some (plainEff (v + 2) (msk (4 * a + M.o)) S1) := by
    rw [step_of_fetch hc]; exact effect_plain rfl _
  have hmem : ∀ c, (plainEff (v + 2) (msk (4 * a + M.o)) S1).mem c =
      if c = 4 * a + M.o then r' % 2 ^ v else S1.mem c := by
    intro c
    simp only [plainEff, msk, Instr.effect, Option.getD_some]
    rw [setCell_apply hA, Nat.mod_eq_of_lt hA, small_mod hv (by norm_num : 3 < 16), h3, h1,
      land_mask, mod_mod_two, hr]
    split_ifs
    · exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by positivity)) (pow_lt_pow2 v))
    · rfl
  refine ⟨_, run_trans hrun (run_one hstep), by simp [plainEff, msk, Instr.effect], ?_, ?_⟩
  · refine ⟨⟨fun a' ha' => ?_, fun a' => ?_, ?_⟩, hin.frame rfl rfl ?_ ?_ ?_,
      hout.frame rfl ?_ ?_⟩
    · rw [hmem, hmem']
      simp only [setCell, hav]
      by_cases h : a' = a
      · subst h; simp
      · rw [if_neg (by omega), if_neg h, hfr _ (by omega) ?_ ?_ ?_]
        · exact hR.core.mem a' ha'
        all_goals rcases hM.o with h | h <;> rw [h] <;> omega
    · rw [hmem']; simp only [setCell]
      split_ifs
      · exact Nat.mod_lt _ (by positivity)
      · exact hR.core.val a'
    · rw [hmem, if_neg hne3.symm]; exact h3
    · simp [plainEff, msk, Instr.effect]
    · simp [plainEff, msk, Instr.effect]
    · intro c hc
      have hA' : c ≠ 4 * a + M.o := by
        rcases hc with hc | hc
        · intro h; rw [h] at hc; exact hne1 hc
        · rw [hc]; exact hne15.symm
      rw [hmem, if_neg hA']
    · simp [plainEff, msk, Instr.effect]
    · intro c hc
      have hA' : c ≠ 4 * a + M.o := by intro h; rw [h] at hc; exact hne1 hc
      rw [hmem, if_neg hA']
  · intro c hc
    simp only [Wr, not_or] at hc
    have hA' : c ≠ 4 * a + M.o := by
      intro h; apply hc.1; rw [h]; rcases hM.o with h' | h' <;> rw [h'] <;> omega
    rw [hmem, if_neg hA']
    by_cases h15' : c = 15
    · subst h15'
      apply h15; intro hb; exact hc.2.2.2.2 ⟨hb, rfl⟩
    · exact hfr c hA' hc.2.1 hc.2.2.1 h15'

/-! ### `store` -/

theorem stepOK_store {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S) {a b : ℕ} (ha : a < 2 ^ v)
    (hb : b < 2 ^ v)
    (hc : Contains P S.pc [.set 7 4, .mul 7 7 (4 * a + M.o), .set 11 M.o, .add 7 7 11,
      .store 7 (4 * b + M.o)])
    (hlab : lab (s.pc + 1) = S.pc + 5) (hs : (Instr.store a b).effect v s = some s') :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  obtain ⟨ha7, ha11, -, -, -⟩ := cell_ne hM a
  obtain ⟨hb7, hb11, -, -, -⟩ := cell_ne hM b
  have hA := four_mul_lt ha ho
  have hB := four_mul_lt hb ho
  have hsa := hR.core.val a
  have hsb := hR.core.val b
  have hX := four_mul_lt hsa ho
  have hX' : 4 * s.mem a < 2 ^ (v + 2) := by omega
  obtain ⟨hx7, hx11, -, -, -⟩ := cell_ne hM (s.mem a)
  have h7 := small_mod hv (by norm_num : 7 < 16)
  have h11 := small_mod hv (by norm_num : 11 < 16)
  have h4 := small_mod hv (by norm_num : 4 < 16)
  have hom : M.o % 2 ^ (v + 2) = M.o := small_mod hv (by omega)
  have hpl : ∀ i ∈ [Instr.set 7 4, .mul 7 7 (4 * a + M.o), .set 11 M.o, .add 7 7 11,
      .store 7 (4 * b + M.o)], isPlain i = true := by simp [isPlain]
  have hrun := run_plain (w := v + 2) _ _ hpl hc
  simp only [Instr.effect, Option.some.injEq] at hs
  subst hs
  set S' := plainRun (v + 2) [Instr.set 7 4, .mul 7 7 (4 * a + M.o), .set 11 M.o, .add 7 7 11,
    .store 7 (4 * b + M.o)] S with hS'
  have e1 : S'.mem (4 * s.mem a + M.o) = s.mem b := by
    simp only [hS', plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h7, h11, h4, hom, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, hR.core.mem a ha]
    have hsb' : s.mem b < 2 ^ (v + 2) := lt_trans hsb (pow_lt_pow2 v)
    simp [ha7, hb7, hb11, Nat.mod_eq_of_lt hX', Nat.mod_eq_of_lt hX, hR.core.mem b hb,
      Nat.mod_eq_of_lt hsb']
  have e2 : ∀ c, c ≠ 4 * s.mem a + M.o → c ≠ 7 → c ≠ 11 → S'.mem c = S.mem c := by
    intro c h1 h2 h3
    simp only [hS', plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h7, h11, h4, hom, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, hR.core.mem a ha]
    simp [ha7, h1, h2, h3, Nat.mod_eq_of_lt hX', Nat.mod_eq_of_lt hX]
  have key := sim_write (S' := S')
    (s' := { s with
      pc := s.pc + 1
      mem := setCell v s.mem (s.mem (a % 2 ^ v)) (s.mem (b % 2 ^ v)) })
    hM hR hsa hsb (by rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]) rfl rfl rfl
    (plainRun_input _ _ hpl) (plainRun_inp _ _ hpl) (by simp [hS', plainEff, Instr.effect]) e1 e2
  refine ⟨5, by norm_num, _, hrun, ?_, key.1, key.2⟩
  rw [plainRun_pc _ _ hpl]; exact hlab.symm

/-! ### Jumps -/

theorem stepOK_jump {M : Mode} (hM : Valid M) {v : ℕ} {P : Program} {lab : ℕ → ℕ} {S s s' : State}
    (hR : Sim M v s S) {l : ℕ} (hc : Contains P S.pc [.jump (lab l)])
    (hs : (Instr.jump l).effect v s = some s') : StepOK M v P lab s' S := by
  simp only [Instr.effect, Option.some.injEq] at hs
  subst hs
  have hstep : step (v + 2) P S = some { S with pc := lab l } := by
    rw [step_of_fetch hc.head]; rfl
  obtain ⟨hsim, hfr⟩ := sim_frame hM (s' := { s with pc := l }) (S' := { S with pc := lab l }) hR
    rfl rfl rfl rfl rfl rfl rfl (fun _ _ _ => rfl)
  exact ⟨1, by norm_num, _, run_one hstep, rfl, hsim, hfr⟩

theorem stepOK_jzero {M : Mode} (hM : Valid M) {v : ℕ} {P : Program} {lab : ℕ → ℕ}
    {S s s' : State} (hR : Sim M v s S) {a l : ℕ} (ha : a < 2 ^ v)
    (hc : Contains P S.pc [.jzero (4 * a + M.o) (lab l)])
    (hlab : lab (s.pc + 1) = S.pc + 1)
    (hs : (Instr.jzero a l).effect v s = some s') : StepOK M v P lab s' S := by
  have hA := four_mul_lt (o := M.o) ha (by rcases hM.o with h | h <;> omega)
  simp only [Instr.effect, Option.some.injEq] at hs
  subst hs
  set X := if S.mem (4 * a + M.o) = 0 then lab l else S.pc + 1 with hX
  have hstep : step (v + 2) P S = some { S with pc := X } := by
    rw [step_of_fetch hc.head]; simp [Instr.effect, Nat.mod_eq_of_lt hA, hX]
  obtain ⟨hsim, hfr⟩ := sim_frame hM
    (s' := { s with pc := if s.mem (a % 2 ^ v) = 0 then l else s.pc + 1 })
    (S' := { S with pc := X }) hR rfl rfl rfl rfl rfl rfl rfl (fun _ _ _ => rfl)
  refine ⟨1, by norm_num, _, run_one hstep, ?_, hsim, hfr⟩
  simp only [hX, Nat.mod_eq_of_lt ha, hR.core.mem a ha]
  split_ifs <;> simp [hlab]

theorem stepOK_jeof_native {M : Mode} (hM : Valid M) {v : ℕ} {P : Program} {lab : ℕ → ℕ}
    {S s s' : State} (hR : Sim M v s S) {δ : ℕ} (hmode : M.inm = .native δ) {l : ℕ}
    (hc : Contains P S.pc [.jeof (lab l)])
    (hlab : lab (s.pc + 1) = S.pc + 1)
    (hs : (Instr.jeof l).effect v s = some s') : StepOK M v P lab s' S := by
  have hin := hR.inr
  rw [hmode] at hin
  obtain ⟨-, hinp, -⟩ := hin
  simp only [Instr.effect, Option.some.injEq] at hs
  subst hs
  set X := if S.inp.isEmpty then lab l else S.pc + 1 with hX
  have hstep : step (v + 2) P S = some { S with pc := X } := by
    rw [step_of_fetch hc.head]; simp [Instr.effect, hX]
  obtain ⟨hsim, hfr⟩ := sim_frame hM
    (s' := { s with pc := if s.inp.isEmpty then l else s.pc + 1 })
    (S' := { S with pc := X }) hR rfl rfl rfl rfl rfl rfl rfl (fun _ _ _ => rfl)
  refine ⟨1, by norm_num, _, run_one hstep, ?_, hsim, hfr⟩
  simp only [hX, hinp]
  split_ifs <;> simp [hlab]

/-- The end-of-tape test of the buffer: cell `7` is set to `0` exactly at the end. -/
theorem eof_block {M : Mode} {v : ℕ} (hv : 2 ≤ v) {S s : State} (hR : Sim M v s S)
    (hmode : M.inm = .buffer) :
    let S1 := plainRun (v + 2) [.set 11 1, .sub 7 15 1, .sub 7 11 7] S
    (S1.mem 7 = 0 ↔ s.inp = []) ∧ S1.mem 11 = 1 ∧
      (∀ c, c ≠ 7 → c ≠ 11 → S1.mem c = S.mem c) ∧ S1.input = S.input ∧ S1.inp = S.inp ∧
      S1.out = S.out ∧ S1.pc = S.pc + 3 := by
  intro S1
  have hin := hR.inr
  rw [hmode] at hin
  obtain ⟨⟨y, hy⟩, hbuf, hlt, hr, hinp⟩ := hin
  have h1 : S.mem 1 = y.length := by
    have := hbuf 0 (by positivity); simpa [hy] using this
  have h7 := small_mod hv (by norm_num : 7 < 16)
  have h11 := small_mod hv (by norm_num : 11 < 16)
  have h1m := small_mod hv (by norm_num : 1 < 16)
  have h15 := small_mod hv (by norm_num : 15 < 16)
  have hlen : s.input.length = y.length + 1 := by rw [hy]; simp
  have hD : (S.mem 15 - y.length) % 2 ^ (v + 2) = S.mem 15 - y.length := by
    apply Nat.mod_eq_of_lt; have := pow_lt_pow2 v; omega
  have hpl : ∀ i ∈ [Instr.set 11 1, .sub 7 15 1, .sub 7 11 7], isPlain i = true := by
    simp [isPlain]
  refine ⟨?_, ?_, ?_, plainRun_input _ _ hpl, plainRun_inp _ _ hpl, ?_, ?_⟩
  · have hD2 : (1 - (S.mem 15 - y.length)) % 2 ^ (v + 2) = 1 - (S.mem 15 - y.length) := by
      apply Nat.mod_eq_of_lt; have := pow_lt_pow2 v; omega
    have e7 : S1.mem 7 = 1 - (S.mem 15 - y.length) := by
      simp [S1, plainEff, Instr.effect, setCell, h7, h11, h1m, h15, h1, hD, hD2]
    rw [e7, hinp, List.drop_eq_nil_iff, hlen]; omega
  · simp [S1, plainEff, Instr.effect, setCell, h7, h11, h1m, h15]
  · intro c hc7 hc11
    simp [S1, plainEff, Instr.effect, setCell, h7, h11, h1m, h15, hc7, hc11]
  · simp [S1, plainEff, Instr.effect]
  · simp only [S1]; rw [plainRun_pc _ _ hpl]; rfl

theorem stepOK_jeof_buffer {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program} {lab : ℕ → ℕ}
    {S s s' : State} (hR : Sim M v s S) (hmode : M.inm = .buffer) {l : ℕ}
    (hc : Contains P S.pc ([.set 11 1, .sub 7 15 1, .sub 7 11 7] ++ [.jzero 7 (lab l)]))
    (hlab : lab (s.pc + 1) = S.pc + 4)
    (hs : (Instr.jeof l).effect v s = some s') : StepOK M v P lab s' S := by
  obtain ⟨hz, -, hfr, hi, hp, ho, hpc⟩ := eof_block hv hR hmode
  set S1 := plainRun (v + 2) [.set 11 1, .sub 7 15 1, .sub 7 11 7] S with hS1
  have hpl : ∀ i ∈ [Instr.set 11 1, .sub 7 15 1, .sub 7 11 7], isPlain i = true := by
    simp [isPlain]
  have hrun1 := run_plain (w := v + 2) _ _ hpl hc.left
  simp only [Instr.effect, Option.some.injEq] at hs
  subst hs
  set X := if S1.mem 7 = 0 then lab l else S1.pc + 1 with hX
  have hstep : step (v + 2) P S1 = some { S1 with pc := X } := by
    have := hc.right.head
    rw [step_of_fetch (by rw [hpc]; simpa using this)]
    simp [Instr.effect, small_mod hv (by norm_num : 7 < 16), hX]
  obtain ⟨hsim, hframe⟩ := sim_frame hM
    (s' := { s with pc := if s.inp.isEmpty then l else s.pc + 1 })
    (S' := { S1 with pc := X }) hR rfl rfl rfl rfl hi hp ho (fun c h7 h11 => hfr c h7 h11)
  refine ⟨4, by norm_num, _, run_trans hrun1 (run_one hstep), ?_, hsim, hframe⟩
  simp only [hX]
  by_cases he : s.inp = []
  · simp [he, hz.mpr he]
  · have : S1.mem 7 ≠ 0 := fun h => he (hz.mp h)
    simp [he, this, hpc, hlab]

/-! ### Reading -/

theorem stepOK_read_native {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {lab : ℕ → ℕ} {ex : ℕ} {S s s' : State} (hR : Sim M v s S) {δ : ℕ}
    (hmode : M.inm = .native δ) {a : ℕ} (ha : a < 2 ^ v)
    (hc : Contains P S.pc [.jeof ex, .read (4 * a + M.o), msk (4 * a + M.o)])
    (hlab : lab (s.pc + 1) = S.pc + 3)
    (hs : (Instr.read a).effect v s = some s') : StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
  have hA := four_mul_lt ha ho
  have hin := hR.inr
  rw [hmode] at hin
  obtain ⟨⟨pre, hpre, hlen⟩, hinp, hfit⟩ := hin
  simp only [Instr.effect] at hs
  rcases hsi : s.inp with _ | ⟨x0, rest⟩
  · rw [hsi] at hs; simp at hs
  rw [hsi] at hs
  simp only [List.head?_cons, Option.map_some, Option.some.injEq, List.tail_cons] at hs
  subst hs
  have hSi : S.inp = x0 :: rest := by rw [hinp, hsi]
  have hc0 := hc.head
  have hc1 := hc.tail.head
  have hc2 := hc.tail.tail.head
  set S1 : State := { S with pc := S.pc + 1 } with hS1
  have hst1 : step (v + 2) P S = some S1 := by
    rw [step_of_fetch hc0]; simp [Instr.effect, hSi, hS1]
  set S2 : State := { S1 with
    pc := S1.pc + 1
    mem := setCell (v + 2) S1.mem (4 * a + M.o) x0
    inp := rest } with hS2
  have hst2 : step (v + 2) P S1 = some S2 := by
    rw [step_of_fetch (by simpa [hS1] using hc1)]; simp [Instr.effect, hS1, hS2, hSi]
  have hrun : run (v + 2) P 2 S = some S2 := run_of_step hst1 (run_one hst2)
  have hin' : InRel v M.inm { s with pc := s.pc + 1, mem := setCell v s.mem a x0, inp := rest }
      S2 := by
    rw [hmode]
    exact ⟨⟨pre, by simp [hS2, hS1, hpre], hlen⟩, rfl, hfit⟩
  have hout' : OutRel v M.outm { s with pc := s.pc + 1, mem := setCell v s.mem a x0, inp := rest }
      S2 := by
    refine hR.outr.frame rfl rfl ?_
    intro c hc
    have : c ≠ 4 * a + M.o := by intro h; rw [h] at hc; exact hne1 hc
    simp [hS2, hS1, setCell_apply hA, this]
  obtain ⟨S3, hrun3, hpc3, hsim, hframe⟩ := mask_tail
    (s' := { s with pc := s.pc + 1, mem := setCell v s.mem a x0, inp := rest })
    (r := x0) (r' := x0)
    hM hv hR ha hrun (by simpa [hS2, hS1, Nat.add_assoc] using hc2)
    (by simp [hS2, setCell_apply hA])
    (fun c h1 _ _ _ => by simp [hS2, hS1, setCell_apply hA, h1])
    (fun _ => by simp [hS2, hS1, setCell_apply hA, hne15.symm]) rfl rfl hin' hout'
  refine ⟨3, by norm_num, S3, hrun3, ?_, hsim, hframe⟩
  rw [hpc3, hS2, hS1, ← hlab]

theorem stepOK_read_buffer {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {lab : ℕ → ℕ} {ex : ℕ} {S s s' : State} (hR : Sim M v s S)
    (hmode : M.inm = .buffer) {a : ℕ} (ha : a < 2 ^ v)
    (hc : Contains P S.pc ([.set 11 1, .sub 7 15 1, .sub 7 11 7] ++ [.jzero 7 ex] ++
      [.set 7 4, .mul 7 7 15, .add 7 7 11, .load (4 * a + M.o) 7, .add 15 15 11] ++
      [msk (4 * a + M.o)]))
    (hlab : lab (s.pc + 1) = S.pc + 10)
    (hs : (Instr.read a).effect v s = some s') : StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
  have hA := four_mul_lt ha ho
  have hin := hR.inr
  rw [hmode] at hin
  obtain ⟨⟨y, hy⟩, hbuf, hlt, hr, hinp⟩ := hin
  simp only [Instr.effect] at hs
  rcases hsi : s.inp with _ | ⟨x0, rest⟩
  · rw [hsi] at hs; simp at hs
  rw [hsi] at hs
  simp only [List.head?_cons, Option.map_some, Option.some.injEq, List.tail_cons] at hs
  subst hs
  -- the read pointer
  set r := S.mem 15 with hrdef
  have hrlt : r < s.input.length := by
    by_contra h
    have : s.input.drop r = [] := List.drop_eq_nil_of_le (by omega)
    rw [← hinp, hsi] at this; simp at this
  have hx0 : s.input[r]?.getD 0 = x0 := by
    have : (s.input.drop r).head? = some x0 := by rw [← hinp, hsi]; rfl
    rw [List.head?_drop] at this; rw [this]; rfl
  have hrest : rest = s.input.drop (r + 1) := by
    have : (s.input.drop r).tail = rest := by rw [← hinp, hsi]; rfl
    rw [← this, List.tail_drop]
  -- first part: the end-of-tape test
  obtain ⟨hz, hS11, hfr1, hi1, hp1, ho1, hpc1⟩ := eof_block hv hR hmode
  set S1 := plainRun (v + 2) [.set 11 1, .sub 7 15 1, .sub 7 11 7] S with hS1
  have hpl1 : ∀ i ∈ [Instr.set 11 1, .sub 7 15 1, .sub 7 11 7], isPlain i = true := by
    simp [isPlain]
  have hrun1 := run_plain (w := v + 2) _ _ hpl1 hc.left.left.left
  have h70 : S1.mem 7 ≠ 0 := fun h => by rw [hz.mp h] at hsi; simp at hsi
  have hst2 : step (v + 2) P S1 = some { S1 with pc := S1.pc + 1 } := by
    have := hc.left.left.right.head
    rw [step_of_fetch (by rw [hpc1]; simpa using this)]
    simp [Instr.effect, small_mod hv (by norm_num : 7 < 16), h70]
  set S2 : State := { S1 with pc := S1.pc + 1 } with hS2
  -- second part: the load
  have hpl3 : ∀ i ∈ [Instr.set 7 4, .mul 7 7 15, .add 7 7 11, .load (4 * a + M.o) 7,
      .add 15 15 11], isPlain i = true := by simp [isPlain]
  have hc3 : Contains P S2.pc [.set 7 4, .mul 7 7 15, .add 7 7 11, .load (4 * a + M.o) 7,
      .add 15 15 11] := by
    have := hc.left.right
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rw [hS2, hpc1]; simpa [Nat.add_assoc] using this
  have hrun3 := run_plain (w := v + 2) _ _ hpl3 hc3
  set S3 := plainRun (v + 2) [.set 7 4, .mul 7 7 15, .add 7 7 11, .load (4 * a + M.o) 7,
      .add 15 15 11] S2 with hS3
  have hrun : run (v + 2) P 9 S = some S3 :=
    run_trans (a := 3) (b := 6) hrun1 (run_of_step hst2 hrun3)
  have hpc3 : S3.pc = S.pc + 9 := by
    rw [hS3, plainRun_pc _ _ hpl3, hS2, hpc1]; simp
  -- the memory of `S3`
  have h7 := small_mod hv (by norm_num : 7 < 16)
  have h11 := small_mod hv (by norm_num : 11 < 16)
  have h4 := small_mod hv (by norm_num : 4 < 16)
  have h15 := small_mod hv (by norm_num : 15 < 16)
  have hrv : r < 2 ^ v := lt_trans hrlt hlt
  have hX := four_mul_lt hrv (by norm_num : 1 < 4)
  have hX' : 4 * r < 2 ^ (v + 2) := by omega
  have hr1 : r + 1 < 2 ^ (v + 2) := lt_trans (by omega) (pow_lt_pow2 v)
  have hS27 : S2.mem 11 = 1 := hS11
  have hS2r : S2.mem 15 = r := by
    show S1.mem 15 = r; rw [hfr1 15 (by omega) (by omega)]
  have hS2x : S2.mem (4 * r + 1) = s.input[r]?.getD 0 := by
    show S1.mem (4 * r + 1) = _
    rw [hfr1 _ (by omega) (by omega)]; exact hbuf r hrv
  have hm3 : ∀ c, S3.mem c = if c = 15 then r + 1 else if c = 4 * a + M.o then
      (s.input[r]?.getD 0) % 2 ^ (v + 2) else if c = 7 then 4 * r + 1 else S2.mem c := by
    intro c
    simp only [hS3, plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some,
      setCell, h7, h11, h4, h15, Nat.mod_eq_of_lt hA, hS27, hS2r]
    have hx7 : 4 * r + 1 ≠ 7 := by omega
    have hx11 : 4 * r + 1 ≠ 11 := by omega
    simp [hne11.symm, hne15.symm, hx7, Nat.mod_eq_of_lt hX', Nat.mod_eq_of_lt hX,
      Nat.mod_eq_of_lt hr1, hS2x]
    split_ifs <;> rfl
  have g1 : P[S3.pc]? = some (msk (4 * a + M.o)) := by
    have := hc.right.head
    rw [hpc3]; simpa [Nat.add_assoc] using this
  have g2 : S3.mem (4 * a + M.o) = x0 % 2 ^ (v + 2) := by
    rw [hm3, if_neg hne15, if_pos rfl, hx0]
  have g3 : ∀ c, c ≠ 4 * a + M.o → c ≠ 7 → c ≠ 11 → c ≠ 15 → S3.mem c = S.mem c := by
    intro c h1 h2 h3 h4'
    rw [hm3, if_neg h4', if_neg h1, if_neg h2]
    exact hfr1 c h2 h3
  have g4 : InRel v M.inm { s with pc := s.pc + 1, mem := setCell v s.mem a x0, inp := rest }
      S3 := by
    rw [hmode]
    refine ⟨⟨y, hy⟩, fun i hi => ?_, hlt, ?_, ?_⟩
    · have h1' : 4 * i + 1 ≠ 15 := by omega
      have h2' : 4 * i + 1 ≠ 4 * a + M.o := fun h => hne1 (by rw [← h]; omega)
      have h3' : 4 * i + 1 ≠ 7 := by omega
      rw [hm3, if_neg h1', if_neg h2', if_neg h3']
      show S1.mem _ = _
      rw [hfr1 _ h3' (by omega)]; exact hbuf i hi
    · rw [hm3, if_pos rfl]; exact hrlt
    · rw [hm3, if_pos rfl]; exact hrest
  have g5 : OutRel v M.outm { s with pc := s.pc + 1, mem := setCell v s.mem a x0, inp := rest }
      S3 := by
    refine hR.outr.frame rfl ?_ ?_
    · simp [hS3, plainEff, Instr.effect, hS2, ho1]
    · intro c hc
      have h2' : c ≠ 4 * a + M.o := fun h => hne1 (by rw [← h]; exact hc)
      rw [hm3, if_neg (by omega), if_neg h2', if_neg (by omega)]
      show S1.mem c = _
      exact hfr1 c (by omega) (by omega)
  obtain ⟨S4, hrun4, hpc4, hsim, hframe⟩ := mask_tail
    (s' := { s with pc := s.pc + 1, mem := setCell v s.mem a x0, inp := rest })
    (r := x0) (r' := x0)
    hM hv hR ha hrun g1 g2 g3 (fun h => absurd hmode h) rfl rfl g4 g5
  refine ⟨10, le_rfl, S4, hrun4, ?_, hsim, hframe⟩
  rw [hpc4, hpc3, ← hlab]

/-! ### Writing -/

theorem stepOK_write_real {M : Mode} (hM : Valid M) {v : ℕ} {P : Program} {lab : ℕ → ℕ}
    {S s s' : State} (hR : Sim M v s S) (hmode : M.outm = .real) {a : ℕ} (ha : a < 2 ^ v)
    (hc : Contains P S.pc [.write (4 * a + M.o)])
    (hlab : lab (s.pc + 1) = S.pc + 1)
    (hs : (Instr.write a).effect v s = some s') : StepOK M v P lab s' S := by
  have hA := four_mul_lt (o := M.o) ha (by rcases hM.o with h | h <;> omega)
  simp only [Instr.effect, Option.some.injEq] at hs
  subst hs
  have hsa := hR.core.val a
  have hstep := step_of_fetch (w := v + 2) hc.head
  simp only [Instr.effect] at hstep
  refine ⟨1, by norm_num, _, run_one hstep, by simp [hlab],
    ⟨⟨hR.core.mem, hR.core.val, hR.core.mask⟩, hR.inr.frame rfl rfl rfl rfl (fun _ _ => rfl), ?_⟩,
    fun _ _ => rfl⟩
  have hout := hR.outr
  rw [hmode] at hout ⊢
  show S.out ++ _ = s.out ++ _
  rw [hout, Nat.mod_eq_of_lt hA, hR.core.mem a ha, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hsa,
    Nat.mod_eq_of_lt (lt_trans hsa (pow_lt_pow2 v))]

theorem stepOK_write_buffer {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S) (hmode : M.outm = .buffer) {a : ℕ}
    (ha : a < 2 ^ v)
    (hc : Contains P S.pc [.set 7 4, .mul 7 7 1, .set 11 5, .add 7 7 11, .store 7 (4 * a + M.o),
      .set 11 1, .add 1 1 11])
    (hlab : lab (s.pc + 1) = S.pc + 7)
    (hs : (Instr.write a).effect v s = some s') (hlen : s'.out.length < 2 ^ v) :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
  have hA := four_mul_lt ha ho
  simp only [Instr.effect, Option.some.injEq] at hs
  subst hs
  have hsa := hR.core.val a
  have hout := hR.outr
  rw [hmode] at hout
  obtain ⟨hSo, hbuf⟩ := hout
  set n := s.out.length with hn
  have hlen' : n + 1 < 2 ^ v := by simpa [hn] using hlen
  have h1 : S.mem 1 = n := by have := hbuf 0 (by positivity); simpa using this
  have h7 := small_mod hv (by norm_num : 7 < 16)
  have h11 := small_mod hv (by norm_num : 11 < 16)
  have h4 := small_mod hv (by norm_num : 4 < 16)
  have h5 := small_mod hv (by norm_num : 5 < 16)
  have h1m := small_mod hv (by norm_num : 1 < 16)
  have hX := four_mul_lt (by omega : n + 1 < 2 ^ v) (by norm_num : 1 < 4)
  have hX4 : 4 * n < 2 ^ (v + 2) := by omega
  have hX5 : 4 * n + 5 < 2 ^ (v + 2) := by omega
  have hn1 : n + 1 < 2 ^ (v + 2) := lt_trans hlen' (pow_lt_pow2 v)
  have hpl : ∀ i ∈ [Instr.set 7 4, .mul 7 7 1, .set 11 5, .add 7 7 11, .store 7 (4 * a + M.o),
      .set 11 1, .add 1 1 11], isPlain i = true := by simp [isPlain]
  have hrun := run_plain (w := v + 2) _ _ hpl hc
  set S' := plainRun (v + 2) [Instr.set 7 4, .mul 7 7 1, .set 11 5, .add 7 7 11,
      .store 7 (4 * a + M.o), .set 11 1, .add 1 1 11] S with hS'
  have hm : ∀ c, c ≠ 7 → c ≠ 11 → S'.mem c =
      if c = 1 then n + 1 else if c = 4 * n + 5 then s.mem a else S.mem c := by
    intro c hc7 hc11
    simp only [hS', plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some,
      setCell, h7, h11, h4, h5, h1m, Nat.mod_eq_of_lt hA, h1]
    have e1 : 4 * n + 5 ≠ 7 := by omega
    have e2 : 4 * n + 5 ≠ 11 := by omega
    have e3 : 4 * n + 5 ≠ 1 := by omega
    have hsa' : s.mem a < 2 ^ (v + 2) := lt_trans hsa (pow_lt_pow2 v)
    simp [hc7, hc11, hne7, hne11, Nat.mod_eq_of_lt hX4,
      Nat.mod_eq_of_lt hX5, Nat.mod_eq_of_lt hn1, hR.core.mem a ha, Nat.mod_eq_of_lt hsa']
  refine ⟨7, by norm_num, S', hrun, ?_, ⟨⟨fun a' ha' => ?_, hR.core.val, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [hS', plainRun_pc _ _ hpl]; exact hlab.symm
  · have e1 : 4 * a' + M.o ≠ 1 := by rcases hM.o with h | h <;> rw [h] <;> omega
    have e2 : 4 * a' + M.o ≠ 4 * n + 5 := by rcases hM.o with h | h <;> rw [h] <;> omega
    obtain ⟨e3, e4, -, -, -⟩ := cell_ne hM a'
    rw [hm _ e3 e4, if_neg e1, if_neg e2]; exact hR.core.mem a' ha'
  · rw [hm 3 (by omega) (by omega), if_neg (by omega), if_neg (by omega)]; exact hR.core.mask
  · have hin := hR.inr
    cases hinm : M.inm with
    | buffer => rw [hM.io hinm] at hmode; cases hmode
    | native δ =>
      rw [hinm] at hin
      obtain ⟨⟨pre, e1, e2⟩, e3, e4⟩ := hin
      exact ⟨⟨pre, by rw [plainRun_input _ _ hpl]; exact e1, e2⟩,
        by rw [plainRun_inp _ _ hpl]; exact e3, e4⟩
  · rw [hmode]
    have hx : s.mem (a % 2 ^ v) % 2 ^ v = s.mem a := by
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hsa]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [← hSo]; simp [hS', plainEff, Instr.effect]
    · show S'.mem (4 * i + 1) = ((s.out ++ [s.mem (a % 2 ^ v) % 2 ^ v]).length ::
        (s.out ++ [s.mem (a % 2 ^ v) % 2 ^ v]))[i]?.getD 0
      rw [hx, hm _ (by omega) (by omega)]
      rcases i with _ | j
      · simp [hn]
      · rw [if_neg (by omega)]
        have hbj := hbuf (j + 1) hi
        simp only [List.getElem?_cons_succ] at hbj ⊢
        by_cases hj : j < n
        · rw [if_neg (by omega), hbj, List.getElem?_append_left (by omega)]
        · by_cases hj' : j = n
          · subst hj'; rw [if_pos (by omega), List.getElem?_append_right (by omega)]; simp [hn]
          · rw [if_neg (by omega), hbj, List.getElem?_eq_none (by omega),
              List.getElem?_eq_none (by simp; omega)]
  · intro c hc'
    simp only [Wr, not_or, hmode] at hc'
    have e1 : c % 4 ≠ 1 := by intro h; apply hc'.2.2.2.1; simp [h]
    rw [hm c hc'.2.1 hc'.2.2.1, if_neg (by omega), if_neg (by omega)]

end Lax496464Proofs.WHierarchy.Machine.Compose.StepOther
