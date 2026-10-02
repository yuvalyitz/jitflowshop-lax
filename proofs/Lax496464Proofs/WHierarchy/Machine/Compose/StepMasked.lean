import Lax496464Proofs.WHierarchy.Machine.Compose.Rel

/-! Simulation of the instructions whose translation ends by masking the result: `set`, the
arithmetic instructions, `not`, `load`, `inputLength` and `inputLoad`. -/

namespace Lax496464Proofs.WHierarchy.Machine.Compose.StepMasked

open Lax808846.Ram Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics
open Lax496464Proofs.WHierarchy.Machine.Compose.Translate Lax496464Proofs.WHierarchy.Machine.Compose.Rel

/-- The conclusion of the simulation of one step: a bounded number of machine steps reach a state
related to the next simulated state. -/
def StepOK (M : Mode) (v : ℕ) (P : Program) (lab : ℕ → ℕ) (s' S : State) : Prop :=
  ∃ k ≤ 10, ∃ S', run (v + 2) P k S = some S' ∧ S'.pc = lab s'.pc ∧ Sim M v s' S' ∧ Frame M S S'

/-- The masked blocks, packaged: the next simulated state is the previous one with `a` set. -/
theorem stepOK_masked {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {lab : ℕ → ℕ} {blk : List Instr} {S s s' : State} {a r r' : ℕ} (hR : Sim M v s S)
    (ha : a < 2 ^ v)
    (hc : Contains P S.pc (blk ++ [msk (4 * a + M.o)]))
    (hlab : lab (s.pc + 1) = S.pc + (blk.length + 1))
    (hs' : s' = { s with pc := s.pc + 1, mem := setCell v s.mem a r' })
    (hpl : ∀ i ∈ blk, isPlain i = true)
    (h1 : (plainRun (v + 2) blk S).mem (4 * a + M.o) = r % 2 ^ (v + 2))
    (hfr : ∀ c, c ≠ 4 * a + M.o → c ≠ 7 → c ≠ 11 → (plainRun (v + 2) blk S).mem c = S.mem c)
    (hout : (plainRun (v + 2) blk S).out = S.out)
    (hr : r % 2 ^ v = r' % 2 ^ v) (hlen : blk.length + 1 ≤ 10) :
    StepOK M v P lab s' S := by
  obtain ⟨S', hrun, hpc, hrel, hfr'⟩ := masked_block hM hv hR ha hc hpl h1 hfr hout hr
  subst hs'
  exact ⟨_, hlen, S', hrun, by rw [hpc, ← hlab], hrel, hfr'⟩

/-! ### Effects of single plain instructions on memory -/

section
variable {w : ℕ}

theorem mem_set {A n : ℕ} (hA : A < 2 ^ w) (S : State) (c : ℕ) :
    (plainEff w (.set A n) S).mem c = if c = A then n % 2 ^ w else S.mem c := by
  simp [plainEff, Instr.effect, setCell_apply hA]

theorem out_plainEff_of_ne_write {i : Instr} (hi : ∀ a, i ≠ .write a) (S : State) :
    (plainEff w i S).out = S.out := by
  cases i with
  | write a => exact absurd rfl (hi a)
  | read a =>
    simp only [plainEff, Instr.effect]
    rcases S.inp.head? with _ | v <;> rfl
  | _ => simp [plainEff, Instr.effect]

end

/-! ### Single arithmetic instructions -/

/-- A binary arithmetic instruction `op` computing `f`. -/
theorem stepOK_bin {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S)
    (op : ℕ → ℕ → ℕ → Instr) (f : ℕ → ℕ → ℕ)
    (hop : ∀ w A B C (S : State), (op A B C).effect w S =
      some { S with pc := S.pc + 1, mem := setCell w S.mem A (f (S.mem (B % 2 ^ w))
        (S.mem (C % 2 ^ w))) })
    (hplain : ∀ A B C, isPlain (op A B C) = true)
    (hwr : ∀ A B C a', op A B C ≠ .write a')
    {a b c : ℕ} (ha : a < 2 ^ v) (hb : b < 2 ^ v) (hc' : c < 2 ^ v)
    (hc : Contains P S.pc [op (4 * a + M.o) (4 * b + M.o) (4 * c + M.o), msk (4 * a + M.o)])
    (hlab : lab (s.pc + 1) = S.pc + 2) (hs : (op a b c).effect v s = some s') :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  have hA := four_mul_lt ha ho
  have hB := four_mul_lt hb ho
  have hC := four_mul_lt hc' ho
  rw [hop] at hs
  refine stepOK_masked hM hv hR ha (blk := [op (4 * a + M.o) (4 * b + M.o) (4 * c + M.o)])
    (r := f (s.mem b) (s.mem c)) hc hlab (Option.some.inj hs).symm ?_ ?_ ?_ ?_ ?_ (by simp)
  · simp [hplain]
  · simp only [plainRun_single, plainEff, hop, Option.getD_some]
    rw [setCell_apply hA, if_pos rfl, Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt hC,
      hR.core.mem b hb, hR.core.mem c hc']
  · intro c' h1 _ _
    simp only [plainRun_single, plainEff, hop, Option.getD_some]
    rw [setCell_apply hA, if_neg h1]
  · simp only [plainRun_single]; exact out_plainEff_of_ne_write (hwr _ _ _) _
  · rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc']

theorem stepOK_set {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S) {a n : ℕ} (ha : a < 2 ^ v)
    (hc : Contains P S.pc [.set (4 * a + M.o) n, msk (4 * a + M.o)])
    (hlab : lab (s.pc + 1) = S.pc + 2) (hs : (Instr.set a n).effect v s = some s') :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  have hA := four_mul_lt ha ho
  refine stepOK_masked hM hv hR ha (blk := [.set (4 * a + M.o) n]) (r := n) hc hlab
    (Option.some.inj hs).symm (by simp [isPlain]) ?_ ?_ ?_ rfl (by simp)
  · rw [plainRun_single, mem_set hA, if_pos rfl]
  · intro c h1 _ _; rw [plainRun_single, mem_set hA, if_neg h1]
  · simp [plainEff, Instr.effect]

theorem stepOK_not {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S) {a b : ℕ} (ha : a < 2 ^ v)
    (hb : b < 2 ^ v)
    (hc : Contains P S.pc [.not (4 * a + M.o) (4 * b + M.o), msk (4 * a + M.o)])
    (hlab : lab (s.pc + 1) = S.pc + 2) (hs : (Instr.not a b).effect v s = some s') :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  have hA := four_mul_lt ha ho
  have hB := four_mul_lt hb ho
  refine stepOK_masked hM hv hR ha (blk := [.not (4 * a + M.o) (4 * b + M.o)])
    (r := 2 ^ (v + 2) - 1 - s.mem b) hc hlab (Option.some.inj hs).symm (by simp [isPlain])
    ?_ ?_ ?_ ?_ (by simp)
  · simp only [plainRun_single, plainEff, Instr.effect, Option.getD_some]
    rw [setCell_apply hA, if_pos rfl, Nat.mod_eq_of_lt hB, hR.core.mem b hb]
  · intro c h1 _ _
    simp only [plainRun_single, plainEff, Instr.effect, Option.getD_some]
    rw [setCell_apply hA, if_neg h1]
  · simp [plainEff, Instr.effect]
  · rw [Nat.mod_eq_of_lt hb]; exact not_mod (hR.core.val b)

theorem stepOK_load {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S) {a b : ℕ} (ha : a < 2 ^ v)
    (hb : b < 2 ^ v)
    (hc : Contains P S.pc ([.set 7 4, .mul 7 7 (4 * b + M.o), .set 11 M.o, .add 7 7 11,
      .load (4 * a + M.o) 7] ++ [msk (4 * a + M.o)]))
    (hlab : lab (s.pc + 1) = S.pc + 6) (hs : (Instr.load a b).effect v s = some s') :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
  have hA := four_mul_lt ha ho
  have hB := four_mul_lt hb ho
  have hsb := hR.core.val b
  have hX := four_mul_lt hsb ho
  have hX' : 4 * s.mem b < 2 ^ (v + 2) := by omega
  have h7 := small_mod hv (by norm_num : 7 < 16)
  have h11 := small_mod hv (by norm_num : 11 < 16)
  have h4 := small_mod hv (by norm_num : 4 < 16)
  have hom : M.o % 2 ^ (v + 2) = M.o := small_mod hv (by omega)
  refine stepOK_masked hM hv hR ha (r := s.mem (s.mem b)) hc hlab (Option.some.inj hs).symm
    (by simp [isPlain]) ?_ ?_ ?_ ?_ (by simp)
  · simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h7, h11, h4, hom, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, hR.core.mem b hb]
    obtain ⟨hb7, hb11, -, -, -⟩ := cell_ne hM b
    obtain ⟨hx7, hx11, -, -, -⟩ := cell_ne hM (s.mem b)
    simp [hb7, hx7, hx11, Nat.mod_eq_of_lt hX', Nat.mod_eq_of_lt hX,
      hR.core.mem _ hsb]
  · intro c h1 h2 h3
    simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h7, h11, h4, hom, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, hR.core.mem b hb]
    simp [h1, h2, h3]
  · simp [plainEff, Instr.effect]
  · rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hsb]

theorem stepOK_inputLength_native {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v)
    {P : Program} {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S) {δ : ℕ}
    (hmode : M.inm = .native δ) {a : ℕ} (ha : a < 2 ^ v)
    (hc : Contains P S.pc ([.inputLength (4 * a + M.o), .set 11 δ,
      .sub (4 * a + M.o) (4 * a + M.o) 11] ++ [msk (4 * a + M.o)]))
    (hlab : lab (s.pc + 1) = S.pc + 4) (hs : (Instr.inputLength a).effect v s = some s') :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
  have hA := four_mul_lt ha ho
  have hδ := hM.δ δ hmode
  have hin := hR.inr
  rw [hmode] at hin
  obtain ⟨⟨pre, hpre, hlen⟩, -, hfit⟩ := hin
  have h11 := small_mod hv (by norm_num : 11 < 16)
  have hdm : δ % 2 ^ (v + 2) = δ := small_mod hv (by omega)
  have hL : (pre.length + s.input.length) % 2 ^ (v + 2) = δ + s.input.length := by
    rw [hlen]; exact Nat.mod_eq_of_lt hfit
  refine stepOK_masked hM hv hR ha (r := s.input.length) hc hlab (Option.some.inj hs).symm
    (by simp [isPlain]) ?_ ?_ ?_ rfl (by simp)
  · simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h11, hdm, Nat.mod_eq_of_lt hA, hpre]
    simp [hne11, hL]
  · intro c h1 h2 h3
    simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h11, hdm, Nat.mod_eq_of_lt hA]
    simp [h1, h3]
  · simp [plainEff, Instr.effect]

theorem stepOK_inputLoad_native {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v)
    {P : Program} {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S) {δ : ℕ}
    (hmode : M.inm = .native δ) {a b : ℕ} (ha : a < 2 ^ v) (hb : b < 2 ^ v)
    (hc : Contains P S.pc ([.set 11 δ, .add 7 (4 * b + M.o) 11, .inputLoad (4 * a + M.o) 7] ++
      [msk (4 * a + M.o)]))
    (hlab : lab (s.pc + 1) = S.pc + 4) (hs : (Instr.inputLoad a b).effect v s = some s') :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
  obtain ⟨hb7, hb11, -, -, -⟩ := cell_ne hM b
  have hA := four_mul_lt ha ho
  have hB := four_mul_lt hb ho
  have hδ := hM.δ δ hmode
  have hin := hR.inr
  rw [hmode] at hin
  obtain ⟨⟨pre, hpre, hlen⟩, -, -⟩ := hin
  have hsb := hR.core.val b
  have h7 := small_mod hv (by norm_num : 7 < 16)
  have h11 := small_mod hv (by norm_num : 11 < 16)
  have hdm : δ % 2 ^ (v + 2) = δ := small_mod hv (by omega)
  have hX : (s.mem b + δ) % 2 ^ (v + 2) = s.mem b + δ := by
    apply Nat.mod_eq_of_lt; have := pow_lt_pow2 v
    have : 2 ^ (v + 2) = 4 * 2 ^ v := by ring
    omega
  have hget : (pre ++ s.input)[s.mem b + δ]? = s.input[s.mem b]? := by
    rw [List.getElem?_append_right (by omega)]; congr 1; omega
  refine stepOK_masked hM hv hR ha (r := s.input[s.mem b]?.getD 0) hc hlab
    (Option.some.inj hs).symm (by simp [isPlain]) ?_ ?_ ?_ ?_ (by simp)
  · simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h7, h11, hdm, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, hpre, hR.core.mem b hb]
    simp [hb11, hX, hget]
  · intro c h1 h2 h3
    simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h7, h11, hdm, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB]
    simp [h1, h2, h3]
  · simp [plainEff, Instr.effect]
  · rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hsb]

theorem stepOK_inputLength_buffer {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v)
    {P : Program} {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S)
    (hmode : M.inm = .buffer) {a : ℕ} (ha : a < 2 ^ v)
    (hc : Contains P S.pc ([.set 11 1, .add (4 * a + M.o) 1 11] ++ [msk (4 * a + M.o)]))
    (hlab : lab (s.pc + 1) = S.pc + 3) (hs : (Instr.inputLength a).effect v s = some s') :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
  have hA := four_mul_lt ha ho
  have hin := hR.inr
  rw [hmode] at hin
  obtain ⟨⟨y, hy⟩, hbuf, hlt, -, -⟩ := hin
  have h1 : S.mem 1 = y.length := by
    have := hbuf 0 (by positivity); simpa [hy] using this
  have h11 := small_mod hv (by norm_num : 11 < 16)
  have h1m := small_mod hv (by norm_num : 1 < 16)
  have hne1' : 4 * a + M.o ≠ 1 := fun h => hne1 (by rw [h])
  refine stepOK_masked hM hv hR ha (r := s.input.length) hc hlab (Option.some.inj hs).symm
    (by simp [isPlain]) ?_ ?_ ?_ rfl (by simp)
  · simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h11, h1m, Nat.mod_eq_of_lt hA]
    simp [h1, hy]
  · intro c h1 h2 h3
    simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h11, h1m, Nat.mod_eq_of_lt hA]
    simp [h1, h3]
  · simp [plainEff, Instr.effect]

theorem stepOK_inputLoad_buffer {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v)
    {P : Program} {lab : ℕ → ℕ} {S s s' : State} (hR : Sim M v s S)
    (hmode : M.inm = .buffer) {a b : ℕ} (ha : a < 2 ^ v) (hb : b < 2 ^ v)
    (hc : Contains P S.pc ([.set 7 4, .mul 7 7 (4 * b + M.o), .set 11 1, .add 7 7 11,
      .load (4 * a + M.o) 7] ++ [msk (4 * a + M.o)]))
    (hlab : lab (s.pc + 1) = S.pc + 6) (hs : (Instr.inputLoad a b).effect v s = some s') :
    StepOK M v P lab s' S := by
  have ho : M.o < 4 := by rcases hM.o with h | h <;> omega
  obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
  obtain ⟨hb7, hb11, -, -, -⟩ := cell_ne hM b
  have hA := four_mul_lt ha ho
  have hB := four_mul_lt hb ho
  have hin := hR.inr
  rw [hmode] at hin
  obtain ⟨-, hbuf, -, -, -⟩ := hin
  have hsb := hR.core.val b
  have hX := four_mul_lt hsb (by norm_num : 1 < 4)
  have hX' : 4 * s.mem b < 2 ^ (v + 2) := by omega
  have h7 := small_mod hv (by norm_num : 7 < 16)
  have h11 := small_mod hv (by norm_num : 11 < 16)
  have h4 := small_mod hv (by norm_num : 4 < 16)
  have h1m := small_mod hv (by norm_num : 1 < 16)
  have hx7 : 4 * s.mem b + 1 ≠ 7 := by omega
  have hx11 : 4 * s.mem b + 1 ≠ 11 := by omega
  refine stepOK_masked hM hv hR ha (r := s.input[s.mem b]?.getD 0) hc hlab
    (Option.some.inj hs).symm (by simp [isPlain]) ?_ ?_ ?_ ?_ (by simp)
  · simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h7, h11, h4, h1m, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, hR.core.mem b hb]
    simp [hb7, hx7, hx11, Nat.mod_eq_of_lt hX', Nat.mod_eq_of_lt hX,
      hbuf _ hsb]
  · intro c h1 h2 h3
    simp only [plainRun_cons, plainRun_nil, plainEff, Instr.effect, Option.getD_some, setCell,
      h7, h11, h4, h1m, Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB]
    simp [h1, h2, h3]
  · simp [plainEff, Instr.effect]
  · rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hsb]

end Lax496464Proofs.WHierarchy.Machine.Compose.StepMasked
