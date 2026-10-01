import Lax496464Proofs.WHierarchy.Machine.Compose.Translate

/-! The relation between a simulated state (at word length `v`) and the simulating machine state
(at word length `v + 2`), and the generic step for a translated instruction that ends by masking
its result. -/

namespace Lax496464Proofs.WHierarchy.Machine.Compose.Rel

open Lax808846.Ram Lax496464Proofs.WHierarchy.Machine.Compose.RunBasics
open Lax496464Proofs.WHierarchy.Machine.Compose.Translate

/-- The simulated memory is stored at the cells `4 * a + o`, holds words, and cell `3` holds the
mask. -/
structure Core (v o : ℕ) (s S : State) : Prop where
  mem : ∀ a < 2 ^ v, S.mem (4 * a + o) = s.mem a
  val : ∀ a, s.mem a < 2 ^ v
  mask : S.mem 3 = 2 ^ v - 1

/-- The relation of the inputs. -/
def InRel (v : ℕ) : InM → State → State → Prop
  | .native δ, s, S =>
      (∃ pre : List ℕ, S.input = pre ++ s.input ∧ pre.length = δ) ∧ S.inp = s.inp ∧
        δ + s.input.length < 2 ^ (v + 2)
  | .buffer, s, S =>
      (∃ y : List ℕ, s.input = y.length :: y) ∧
        (∀ i < 2 ^ v, S.mem (4 * i + 1) = s.input[i]?.getD 0) ∧ s.input.length < 2 ^ v ∧
        S.mem 15 ≤ s.input.length ∧ s.inp = s.input.drop (S.mem 15)

/-- The relation of the outputs. -/
def OutRel (v : ℕ) : OutM → State → State → Prop
  | .real, s, S => S.out = s.out
  | .buffer, s, S =>
      S.out = [] ∧ ∀ i < 2 ^ v, S.mem (4 * i + 1) = (s.out.length :: s.out)[i]?.getD 0

/-- The simulation relation, apart from the program counters. -/
structure Sim (M : Mode) (v : ℕ) (s S : State) : Prop where
  core : Core v M.o s S
  inr : InRel v M.inm s S
  outr : OutRel v M.outm s S

/-- The cells a translated instruction may write. -/
def Wr (M : Mode) (c : ℕ) : Prop :=
  c % 4 = M.o ∨ c = 7 ∨ c = 11 ∨ (M.outm = .buffer ∧ c % 4 = 1) ∨ (M.inm = .buffer ∧ c = 15)

/-- Only writable cells change. -/
def Frame (M : Mode) (S S' : State) : Prop := ∀ c, ¬ Wr M c → S'.mem c = S.mem c

theorem Frame.refl (M : Mode) (S : State) : Frame M S S := fun _ _ => rfl

theorem Frame.trans {M : Mode} {S1 S2 S3 : State} (h1 : Frame M S1 S2) (h2 : Frame M S2 S3) :
    Frame M S1 S3 := fun c hc => (h2 c hc).trans (h1 c hc)

/-- The admissible modes. -/
structure Valid (M : Mode) : Prop where
  o : M.o = 0 ∨ M.o = 2
  δ : ∀ δ, M.inm = .native δ → δ ≤ 1
  io : M.inm = .buffer → M.outm = .real

theorem InRel.frame {v : ℕ} {m : InM} {s s' S S' : State} (h : InRel v m s S)
    (hi : s'.input = s.input) (hp : s'.inp = s.inp) (Hi : S'.input = S.input)
    (Hp : S'.inp = S.inp) (Hm : ∀ c, c % 4 = 1 ∨ c = 15 → S'.mem c = S.mem c) :
    InRel v m s' S' := by
  cases m with
  | native δ =>
    obtain ⟨⟨pre, h1, h2⟩, h3, h4⟩ := h
    exact ⟨⟨pre, by rw [Hi, hi, h1], h2⟩, by rw [Hp, hp, h3], by rw [hi]; exact h4⟩
  | buffer =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    refine ⟨by rw [hi]; exact h1, fun i hi' => ?_, by rw [hi]; exact h3, ?_, ?_⟩
    · rw [Hm _ (Or.inl (by omega)), hi]; exact h2 i hi'
    · rw [Hm 15 (Or.inr rfl), hi]; exact h4
    · rw [Hm 15 (Or.inr rfl), hi, hp]; exact h5

theorem OutRel.frame {v : ℕ} {m : OutM} {s s' S S' : State} (h : OutRel v m s S)
    (ho : s'.out = s.out) (Ho : S'.out = S.out) (Hm : ∀ c, c % 4 = 1 → S'.mem c = S.mem c) :
    OutRel v m s' S' := by
  cases m with
  | real => show S'.out = s'.out; rw [Ho, ho]; exact h
  | buffer =>
    obtain ⟨h1, h2⟩ := h
    refine ⟨by rw [Ho]; exact h1, fun i hi => ?_⟩
    rw [Hm _ (by omega), ho]; exact h2 i hi

/-! ### Arithmetic -/

theorem setCell_apply {w A : ℕ} (hA : A < 2 ^ w) (m : ℕ → ℕ) (val c : ℕ) :
    setCell w m A val c = if c = A then val % 2 ^ w else m c := by
  simp [setCell, Nat.mod_eq_of_lt hA]

theorem land_mask (x v : ℕ) : Nat.land x (2 ^ v - 1) = x % 2 ^ v :=
  Nat.and_two_pow_sub_one_eq_mod x v

theorem mod_mod_two (r v : ℕ) : r % 2 ^ (v + 2) % 2 ^ v = r % 2 ^ v :=
  Nat.mod_mod_of_dvd r (pow_dvd_pow 2 (by omega))

theorem pow_lt_pow2 (v : ℕ) : 2 ^ v < 2 ^ (v + 2) :=
  Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem four_mul_lt {v a o : ℕ} (ha : a < 2 ^ v) (ho : o < 4) : 4 * a + o < 2 ^ (v + 2) := by
  have : 2 ^ (v + 2) = 4 * 2 ^ v := by ring
  omega

theorem not_mod {v x : ℕ} (hx : x < 2 ^ v) :
    (2 ^ (v + 2) - 1 - x) % 2 ^ v = (2 ^ v - 1 - x) % 2 ^ v := by
  have h : 2 ^ (v + 2) - 1 - x = (2 ^ v - 1 - x) + 2 ^ v * 3 := by
    have : 2 ^ (v + 2) = 4 * 2 ^ v := by ring
    omega
  rw [h, Nat.add_mul_mod_self_left]

theorem small_lt {v : ℕ} (hv : 2 ≤ v) {n : ℕ} (hn : n < 16) : n < 2 ^ (v + 2) := by
  have : 2 ^ 4 ≤ 2 ^ (v + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem small_mod {v : ℕ} (hv : 2 ≤ v) {n : ℕ} (hn : n < 16) : n % 2 ^ (v + 2) = n :=
  Nat.mod_eq_of_lt (small_lt hv hn)

/-! ### Cells -/

theorem cell_ne {M : Mode} (hM : Valid M) (a : ℕ) :
    4 * a + M.o ≠ 7 ∧ 4 * a + M.o ≠ 11 ∧ 4 * a + M.o ≠ 3 ∧ 4 * a + M.o ≠ 15 ∧
      (4 * a + M.o) % 4 ≠ 1 := by
  rcases hM.o with h | h <;> rw [h] <;> omega

theorem cell_inj {M : Mode} {a a' : ℕ} : 4 * a' + M.o = 4 * a + M.o ↔ a' = a := by omega

/-! ### Plain blocks -/

theorem plainRun_input {w : ℕ} :
    ∀ (blk : List Instr) (s : State), (∀ i ∈ blk, isPlain i = true) →
      (plainRun w blk s).input = s.input
  | [], s, _ => rfl
  | i :: blk, s, h => by
    rw [plainRun_cons, plainRun_input blk _ (fun j hj => h j (by simp [hj])),
      plainEff_input (h i (by simp))]

theorem plainRun_inp {w : ℕ} :
    ∀ (blk : List Instr) (s : State), (∀ i ∈ blk, isPlain i = true) →
      (plainRun w blk s).inp = s.inp
  | [], s, _ => rfl
  | i :: blk, s, h => by
    rw [plainRun_cons, plainRun_inp blk _ (fun j hj => h j (by simp [hj])),
      plainEff_inp (h i (by simp))]

theorem plainRun_append (w : ℕ) (a b : List Instr) (s : State) :
    plainRun w (a ++ b) s = plainRun w b (plainRun w a s) := by
  simp [plainRun, List.foldl_append]

theorem plainRun_single (w : ℕ) (i : Instr) (s : State) : plainRun w [i] s = plainEff w i s := rfl

/-- **Masked result.** A translated instruction that consists of plain instructions computing a
value `r` into the cell of `a`, followed by the mask, simulates the simulated instruction writing
`r'` into `a`, when `r ≡ r'` modulo `2 ^ v`. -/
theorem masked_block {M : Mode} (hM : Valid M) {v : ℕ} (hv : 2 ≤ v) {P : Program}
    {blk : List Instr} {S s : State} {a r r' : ℕ} (hR : Sim M v s S) (ha : a < 2 ^ v)
    (hc : Contains P S.pc (blk ++ [msk (4 * a + M.o)]))
    (hpl : ∀ i ∈ blk, isPlain i = true)
    (h1 : (plainRun (v + 2) blk S).mem (4 * a + M.o) = r % 2 ^ (v + 2))
    (hfr : ∀ c, c ≠ 4 * a + M.o → c ≠ 7 → c ≠ 11 → (plainRun (v + 2) blk S).mem c = S.mem c)
    (hout : (plainRun (v + 2) blk S).out = S.out)
    (hr : r % 2 ^ v = r' % 2 ^ v) :
    ∃ S', run (v + 2) P (blk.length + 1) S = some S' ∧ S'.pc = S.pc + (blk.length + 1) ∧
      Sim M v { s with pc := s.pc + 1, mem := setCell v s.mem a r' } S' ∧ Frame M S S' := by
  have hpl' : ∀ i ∈ blk ++ [msk (4 * a + M.o)], isPlain i = true := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact hpl i hi
    · simp at hi; subst hi; rfl
  have hrun := run_plain (w := v + 2) _ _ hpl' hc
  simp only [List.length_append, List.length_singleton] at hrun
  refine ⟨_, hrun, by rw [plainRun_pc _ _ hpl']; simp, ?_, ?_⟩
  all_goals
    obtain ⟨hne7, hne11, hne3, hne15, hne1⟩ := cell_ne hM a
    have hA := four_mul_lt (o := M.o) ha (by rcases hM.o with h | h <;> omega)
    have hav : a % 2 ^ v = a := Nat.mod_eq_of_lt ha
    set S1 := plainRun (v + 2) blk S with hS1
    have h3 : S1.mem 3 = 2 ^ v - 1 := by rw [hfr 3 hne3.symm (by omega) (by omega)]; exact hR.core.mask
    have hS2 : plainRun (v + 2) (blk ++ [msk (4 * a + M.o)]) S =
        plainEff (v + 2) (msk (4 * a + M.o)) S1 := by rw [plainRun_append]; rfl
    have hmem : ∀ c, (plainEff (v + 2) (msk (4 * a + M.o)) S1).mem c =
        if c = 4 * a + M.o then r' % 2 ^ v else S1.mem c := by
      intro c
      simp only [plainEff, msk, Instr.effect, Option.getD_some]
      rw [setCell_apply hA, Nat.mod_eq_of_lt hA, small_mod hv (by norm_num : 3 < 16), h3, h1,
        land_mask, mod_mod_two, hr]
      split_ifs
      · exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by positivity)) (pow_lt_pow2 v))
      · rfl
    rw [hS2]
  · refine ⟨⟨fun a' ha' => ?_, fun a' => ?_, ?_⟩, ?_, ?_⟩
    · rw [hmem]
      simp only [setCell, hav]
      by_cases h : a' = a
      · subst h; simp
      · rw [if_neg (by omega), if_neg h, hfr _ (by omega) ?_ ?_]
        · exact hR.core.mem a' ha'
        · rcases hM.o with h | h <;> rw [h] <;> omega
        · rcases hM.o with h | h <;> rw [h] <;> omega
    · simp only [setCell]
      split_ifs
      · exact Nat.mod_lt _ (by positivity)
      · exact hR.core.val a'
    · rw [hmem, if_neg hne3.symm]; exact h3
    · refine hR.inr.frame rfl rfl ?_ ?_ ?_
      · simp [plainEff, msk, Instr.effect]; exact plainRun_input _ _ hpl
      · simp [plainEff, msk, Instr.effect]; exact plainRun_inp _ _ hpl
      · intro c hc
        have h7 : c ≠ 7 := by omega
        have h11 : c ≠ 11 := by omega
        have hA' : c ≠ 4 * a + M.o := by
          rcases hc with hc | hc
          · intro h; rw [h] at hc; exact hne1 hc
          · rw [hc]; exact hne15.symm
        rw [hmem, if_neg hA', hfr c hA' h7 h11]
    · refine hR.outr.frame rfl ?_ ?_
      · simp [plainEff, msk, Instr.effect]; exact hout
      · intro c hc
        have hA' : c ≠ 4 * a + M.o := by intro h; rw [h] at hc; exact hne1 hc
        rw [hmem, if_neg hA', hfr c hA' (by omega) (by omega)]
  · intro c hc
    simp only [Wr, not_or] at hc
    have hA' : c ≠ 4 * a + M.o := by
      intro h; apply hc.1; rw [h]; rcases hM.o with h' | h' <;> rw [h'] <;> omega
    rw [hmem, if_neg hA', hfr c hA' hc.2.1 hc.2.2.1]

end Lax496464Proofs.WHierarchy.Machine.Compose.Rel
