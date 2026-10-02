import Lax496464Proofs.WHierarchy.Logic.McParam.Prog
import Lax496464.WH_B5_HierarchyFacts
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-!
# The Parameter of Model Checking Is Computable in Polynomial Time

The program `prog` reads the word, skips the structure with `headSkip` and adds up the size of the
formula with `scanLoop`, in `O(|x|)` steps with values below `(|x| + 2)² + max x + 9`.
-/

namespace Lax496464Proofs.WHierarchy.Logic.McParam.Final

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding
open Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.ReadTape
open Lax496464Proofs.WHierarchy.Logic.McParam.Math Lax496464Proofs.WHierarchy.Logic.McParam.Prog

/-! ### Skipping the structure -/

/-- The invariant of the loop over the blocks. -/
def HI (D : Dec) (σ : Env) : Prop :=
  σ.arrs "a" = D.word ∧ σ.vars "rt_n" = D.word.length ∧ σ.vars "mp_s" = D.s ∧
    σ.vars "mp_i" ≤ D.s ∧ σ.vars "mp_p" = D.s + 2 + D.pre (σ.vars "mp_i")

/-- The facts about the values the program needs. -/
structure VOk (w : List ℕ) (B : ℕ) : Prop where
  entries : ∀ v ∈ w, v < B
  len : w.length + 8 < B

theorem VOk.getD_lt {w : List ℕ} {B : ℕ} (h : VOk w B) (j : ℕ) : w.getD j 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases hj : w[j]? with _ | v
  · have := h.len; simp; omega
  · exact h.entries v (List.mem_of_getElem? hj)

set_option maxHeartbeats 2000000 in
theorem headBody_spec (D : Dec) {B : ℕ} (hB : VOk D.word B) :
    Spec B (fun σ => HI D σ ∧ σ.vars "mp_i" < D.s) headBody
      (fun σ σ' => HI D σ' ∧ σ'.vars "mp_i" = σ.vars "mp_i" + 1) 30 := by
  refine spec_of_point fun σ ⟨⟨ha, hn, hs, hi, hp⟩, hlt⟩ => ?_
  have hL := hB.len
  have hpos := D.pos_lt hlt
  have hsl := D.s_lt
  have hmul := D.cnt_mul_le hlt
  have hpre := D.pre_succ hlt
  have hle := D.pre_le (i := σ.vars "mp_i" + 1) (by omega)
  have hst := D.start_eq
  have e1 : (σ.arrs "a").getD (σ.vars "mp_p") 0 = D.cnt (σ.vars "mp_i") := by
    rw [ha, hp]; exact D.getD_cnt hlt
  have e2 : (σ.arrs "a").getD (1 + σ.vars "mp_i") 0 = D.ar (σ.vars "mp_i") := by
    rw [ha]; exact D.getD_ar hlt
  have b1 : D.cnt (σ.vars "mp_i") < B := by rw [← e1, ha]; exact hB.getD_lt _
  have b2 : D.ar (σ.vars "mp_i") < B := by rw [← e2, ha]; exact hB.getD_lt _
  have i1 : σ.vars "mp_p" < (σ.arrs "a").length := by rw [ha, hp]; exact hpos
  have i2 : 1 + σ.vars "mp_i" < (σ.arrs "a").length := by rw [ha]; omega
  unfold Dec.start at hst
  unfold headBody
  run_vcg
  all_goals subst_vars
  all_goals
    try simp only [vars_setVar, arrs_setVar, String.reduceEq, ↓reduceIte] at *
  all_goals (try rw [e1] at *)
  all_goals (try rw [e2] at *)
  all_goals first
    | omega
    | (simp only [HI, vars_setVar, arrs_setVar, String.reduceEq, ↓reduceIte, and_true]
       exact ⟨ha, hn, hs, by omega, by rw [hpre]; omega⟩)

theorem headSkip_run (D : Dec) {B : ℕ} (hB : VOk D.word B) {σ : Env}
    (ha : σ.arrs "a" = D.word) (hn : σ.vars "rt_n" = D.word.length) :
    ∃ σ', Run B headSkip σ σ' (3 + (4 + ((30 + 4) * D.s + 6))) ∧ HI D σ' ∧
      σ'.vars "mp_i" = D.s ∧ σ'.out = σ.out := by
  have hL := hB.len
  have hsl := D.s_lt
  have hloop := Spec.forRangeZero (B := B) (c := headBody) "mp_i" "mp_s" (HI D) D.s 30
    (by omega) (fun σ h => h.2.2.2.1) (fun σ h => h.2.2.1) (headBody_spec D hB)
  have h0 : (D.word).getD 0 0 = D.s := by simp [Dec.word, Dec.s]
  have r1 : Run B (.assign "mp_s" (.get "a" (.lit 0))) σ (σ.setVar "mp_s" D.s)
      (1 + (Expr.get "a" (.lit 0)).size) := by
    refine Run.assign ?_
    rw [← h0, ← ha]
    exact RunStep.eval_get B σ "a" (.lit 0) 0 (evalB_lit (by omega)) (by rw [ha]; omega)
      (by rw [ha, h0]; omega)
  set σ1 := σ.setVar "mp_s" D.s with hσ1
  have r2 : Run B (.assign "mp_p" (.add (W "mp_s") (.lit 2))) σ1 (σ1.setVar "mp_p" (D.s + 2))
      (1 + (Expr.add (W "mp_s") (.lit 2)).size) := by
    refine Run.assign ?_
    have : σ1.vars "mp_s" = D.s := by simp [σ1]
    rw [← this]
    exact evalB_bin (evalB_var (by rw [this]; omega)) (evalB_lit (by omega)) (by
      simp only [Bop.apply_add]; rw [this]; omega)
  set σ2 := σ1.setVar "mp_p" (D.s + 2) with hσ2
  obtain ⟨σ3, r3, hI, hi⟩ := hloop σ2 (by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [σ1, σ2, ha, hn, Dec.pre])
  have hout : σ3.out = σ2.out := by
    have := r3.out_eq (by decide)
    exact this
  refine ⟨σ3, r1.seq (r2.seq r3), hI, hi, ?_⟩
  rw [hout]; simp [σ1, σ2]

theorem SI_start (D : Dec) {σ : Env} (hI : HI D σ) (hi : σ.vars "mp_i" = D.s) :
    SI D.word D.φ (σ.setVar "mp_acc" 0) := by
  obtain ⟨ha, hn, -, -, hp⟩ := hI
  have hst := D.start_eq
  refine ⟨by simp [ha], by simp [hn], ?_, [D.φ], ?_, by simp⟩
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hp, hi]; unfold Dec.start at hst; omega
  · simp only [vars_setVar, String.reduceEq, ↓reduceIte]
    rw [hp, hi]
    have := D.drop_start
    unfold Dec.start at this
    simp [this]

/-- The cost of the program. -/
def Kp (D : Dec) : ℕ :=
  16 * D.word.length + 7 +
    (3 + (4 + ((30 + 4) * D.s + 6)) + (1 + 1 + (64 * D.word.length + 4) + (1 + 1)))

theorem tail_run (D : Dec) {B : ℕ} (hB : VOk D.word B) {σ : Env}
    (ha : σ.arrs "a" = D.word) (hn : σ.vars "rt_n" = D.word.length) (ho : σ.out = []) :
    ∃ σ', Run B (.seq headSkip (.seq scanLoop (.write (W "mp_acc")))) σ σ'
      (3 + (4 + ((30 + 4) * D.s + 6)) + (1 + 1 + (64 * D.word.length + 4) + (1 + 1))) ∧
      σ'.out = [D.φ.size] := by
  have hL := hB.len
  have hφ : D.φ.size ≤ D.word.length :=
    (Lax496464Proofs.WHierarchy.Logic.FormulaCode.size_le_length_encode D.φ).trans (by
      have := D.start_eq; omega)
  obtain ⟨σ1, r1, hI, hi, ho1⟩ := headSkip_run D hB ha hn
  have r2 : Run B (.assign "mp_acc" (.lit 0)) σ1 (σ1.setVar "mp_acc" 0)
      (1 + (Expr.lit 0).size) := Run.assign (evalB_lit (by omega))
  obtain ⟨σ3, r3, ⟨hS, hp3⟩, -, -, -, ho3⟩ :=
    (scanWhile_spec hB.entries hφ (by omega)).frame (σ1.setVar "mp_acc" 0) (SI_start D hI hi)
  have hacc := acc_of_SI_end hS hp3
  have r4 : Run B (.write (W "mp_acc")) σ3 { σ3 with out := σ3.out ++ [σ3.vars "mp_acc"] }
      (1 + (W "mp_acc").size) := Run.write (evalB_var (by rw [hacc]; omega))
  refine ⟨_, r1.seq ((r2.seq r3).seq r4), ?_⟩
  show σ3.out ++ [σ3.vars "mp_acc"] = [D.φ.size]
  rw [ho3 (by decide), hacc]
  simp [ho1, ho]

theorem prog_run (D : Dec) {B : ℕ} (hB : VOk D.word B) :
    ∃ σ', Run B prog
      (initEnv (fun a => if a = "a" then D.word.length else 0) (D.word.length :: D.word)) σ'
      (Kp D) ∧ σ'.out = [D.φ.size] := by
  have hl := hB.len
  set σ0 := initEnv (fun a => if a = "a" then D.word.length else 0) (D.word.length :: D.word)
    with hσ0
  obtain ⟨σ1, r1, ha, hn, -, ho, -, -⟩ :=
    readTape_spec D.word σ0 hB.entries (by omega) rfl (by simp [σ0, initEnv]) σ0 rfl
  obtain ⟨σ2, r2, ho2⟩ := tail_run D hB ha hn (by rw [ho]; rfl)
  exact ⟨σ2, r1.seq r2, ho2⟩

/-! ### Polynomial time -/

/-- The largest entry of a word. -/
def Mmax (x : List ℕ) : ℕ := x.foldr max 0

theorem le_Mmax {x : List ℕ} {v : ℕ} (hv : v ∈ x) : v ≤ Mmax x := by
  induction x with
  | nil => simp at hv
  | cons a t ih =>
    simp only [Mmax, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp hv with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem Mmax_lt (x : List ℕ) : Mmax x < 2 ^ bitSize x := by
  induction x with
  | nil => simp [Mmax, bitSize, encode]
  | cons a t ih =>
    simp only [Mmax, List.foldr_cons] at ih ⊢
    have h1 := Lax496464Proofs.WHierarchy.Machine.SizeFacts.lt_two_pow_bitSize (x := a :: t) (v := a)
      (by simp)
    have h2 : 2 ^ bitSize t ≤ 2 ^ bitSize (a :: t) := Nat.pow_le_pow_right (by norm_num)
      (by rw [Lax496464Proofs.WHierarchy.Machine.SizeFacts.bitSize_cons]; omega)
    exact max_lt h1 (by omega)

/-- The value bound of the program. -/
def Bm (x : List ℕ) : ℕ := (x.length + 2) * (x.length + 2) + Mmax x + 9

theorem vOk_Bm (x : List ℕ) : VOk x (Bm x) :=
  ⟨fun v hv => by have := le_Mmax hv; unfold Bm; omega, by unfold Bm; nlinarith⟩

theorem Bm_add_le (x : List ℕ) : Bm x + 100 ≤ 2 ^ (200 * (bitSize x + 1)) := by
  have hL := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
  have hM := Mmax_lt x
  set b := bitSize x
  have h1 : x.length + 2 ≤ 2 ^ (b + 1) := by
    have : b + 2 ≤ 2 ^ (b + 1) := Nat.lt_two_pow_self (n := b + 1)
    omega
  have h2 : (x.length + 2) * (x.length + 2) ≤ 2 ^ (2 * b + 2) := by
    have := Nat.mul_le_mul h1 h1
    rw [← pow_add] at this
    rw [show 2 * b + 2 = b + 1 + (b + 1) by ring]; exact this
  have h3 : 2 ^ b ≤ 2 ^ (2 * b + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ 7 ≤ 2 ^ (2 * b + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ^ (2 * b + 2) * 32 = 2 ^ (2 * b + 7) := by
    rw [show 2 * b + 7 = (2 * b + 2) + 5 by ring, Nat.pow_add 2 (2 * b + 2) 5]
  have h6 : 2 ^ (2 * b + 9) ≤ 2 ^ (200 * (b + 1)) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h7 : 2 ^ (2 * b + 9) = 2 ^ (2 * b + 7) * 4 := by
    rw [show 2 * b + 9 = (2 * b + 7) + 2 by ring, Nat.pow_add 2 (2 * b + 7) 2]
  unfold Bm
  omega

/-- The layout of the program. -/
def layout : Layout := ⟨progVars, ["a"], 8⟩

set_option maxHeartbeats 4000000 in
theorem prog_ok : Com.Ok layout prog := by
  simp [layout, progVars, prog, readTape, readLoop, readBody, headSkip, headLoop, headBody,
    scanLoop, scanBody, tagCase, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

/-- The value bound, as a function of the tape. -/
def Btape (y : List ℕ) : ℕ := Bm y.tail

/-- The cost bound, as a function of the tape. -/
def Ktape (y : List ℕ) : ℕ := 150 * (y.tail.length + 1)

theorem Kp_le (D : Dec) : Kp D ≤ 150 * (D.word.length + 1) := by
  have := D.s_lt
  unfold Kp; omega

theorem solves (Φ : Set Formula) :
    Solves layout prog (Tapes (pMC Φ).Domain) (fun y => [(pMC Φ).param y.tail]) Btape Ktape := by
  refine ⟨prog_ok, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩ v hv
    have hB := vOk_Bm x
    simp only [Btape, List.tail_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · have := hB.len; omega
    · exact hB.entries v hv
  · rintro y ⟨x, ⟨A, φ, h, -, -⟩, rfl⟩
    obtain ⟨D, rfl, -, -⟩ := Dec.exists_of h
    obtain ⟨σ', hr, ho⟩ := prog_run D (vOk_Bm D.word)
    refine ⟨_, σ', hr.mono (Kp_le D), ?_⟩
    rw [ho]
    show [D.φ.size] = [mcParam D.word]
    rw [D.mcParam_eq]

/--
---
conclusion: Lax496464.WH_B5_HierarchyFacts.pMC_isParameterized
---
**The parameter of `p-MC(Φ)` is computable in polynomial time.** An IMP+ program reads the word,
skips the structure using its header (the number of symbols, the arities, the size, then per symbol
the number of tuples, each block being that number times the arity long), and walks the prefix code
of the formula to the end of the word, adding up the contribution of each tag; it runs in
`O(|x|)` steps.
-/
theorem pMC_isParameterized (Φ : Set Formula) : IsParameterized (pMC Φ) := by
  refine polyTimeOn_of_solves (c₀ := 2000) (d := 1) (solves Φ) (fun x hx => ?_)
    (fun x hx => ?_) (fun x hx v hv => ?_)
  · have h := Bm_add_le x
    have hmono : 2 ^ (200 * (bitSize x + 1)) ≤ 2 ^ (2000 * (bitSize x + 1) ^ 1) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [pow_one]; omega)
    refine ⟨?_, ?_⟩
    · simp only [Btape, List.tail_cons, Bm]; omega
    · simp only [Btape, List.tail_cons, Layout.span, layout, progVars, List.length_cons,
        List.length_nil]
      omega
  · have hL := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
    simp only [Ktape, List.tail_cons, Layout.const, pow_one]
    omega
  · simp only [List.mem_singleton] at hv
    subst hv
    obtain ⟨A, φ, h, -, -⟩ := hx
    obtain ⟨D, rfl, -, -⟩ := Dec.exists_of h
    show mcParam D.word < _
    rw [D.mcParam_eq]
    have h1 : D.φ.size ≤ D.word.length :=
      (Lax496464Proofs.WHierarchy.Logic.FormulaCode.size_le_length_encode D.φ).trans (by
        have := D.start_eq; omega)
    have h2 := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize D.word
    have h3 : bitSize D.word < 2 ^ bitSize D.word := Nat.lt_two_pow_self
    have h4 : 2 ^ bitSize D.word ≤ 2 ^ (2000 * (bitSize D.word + 1) ^ 1) :=
      Nat.pow_le_pow_right (by norm_num) (by rw [pow_one]; omega)
    omega

end Lax496464Proofs.WHierarchy.Logic.McParam.Final
