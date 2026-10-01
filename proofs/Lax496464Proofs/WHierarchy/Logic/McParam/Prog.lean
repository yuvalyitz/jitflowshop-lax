import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Machine.ReadTape
import Lax496464Proofs.WHierarchy.Logic.McParam.Math

/-!
# The parameter of a model-checking word, computed by a scan: the program

After `readTape` (array `a` = the word, `rt_n` = its length), `headSkip` moves `mp_p` over the
structure using its header, and `scanLoop` walks the formula, adding up the contributions of its
tags into `mp_acc`, which is written. All scalars are prefixed `mp_`.
-/

namespace Lax496464Proofs.WHierarchy.Logic.McParam.Prog

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Logic.McParam.Math

abbrev W (s : String) : Expr := .var s

/-! ### The program -/

/-- Skip one block: `p := p + 1 + a[p] · a[1 + i]`. -/
def headBody : Com :=
  .seq (.assign "mp_c" (.get "a" (W "mp_p")))
  (.seq (.assign "mp_ar" (.get "a" (.add (.lit 1) (W "mp_i"))))
  (.seq (.assign "mp_p" (.add (.add (W "mp_p") (.lit 1)) (.mul (W "mp_c") (W "mp_ar"))))
        (.assign "mp_i" (.add (W "mp_i") (.lit 1)))))

/-- The loop over the blocks. -/
def headLoop : Com := .seq (.assign "mp_i" (.lit 0)) (.while (.lt (W "mp_i") (W "mp_s")) headBody)

/-- **Skip the structure.** -/
def headSkip : Com :=
  .seq (.assign "mp_s" (.get "a" (.lit 0)))
  (.seq (.assign "mp_p" (.add (W "mp_s") (.lit 2))) headLoop)

/-- The five cases of a tag. -/
def tagCase : Com :=
  .ite (.eq (W "mp_t") (.lit 0))
    (.seq (.assign "mp_l" (.get "a" (.add (W "mp_p") (.lit 2))))
      (.seq (.assign "mp_acc" (.add (.add (W "mp_acc") (W "mp_l")) (.lit 1)))
        (.assign "mp_p" (.add (.add (W "mp_p") (.lit 3)) (W "mp_l")))))
  (.ite (.eq (W "mp_t") (.lit 1))
    (.seq (.assign "mp_l" (.get "a" (.add (W "mp_p") (.lit 1))))
      (.seq (.assign "mp_acc" (.add (.add (W "mp_acc") (W "mp_l")) (.lit 1)))
        (.assign "mp_p" (.add (.add (W "mp_p") (.lit 2)) (W "mp_l")))))
  (.ite (.eq (W "mp_t") (.lit 2))
    (.seq (.assign "mp_acc" (.add (W "mp_acc") (.lit 3))) (.assign "mp_p" (.add (W "mp_p") (.lit 3))))
  (.ite (.lt (W "mp_t") (.lit 6))
    (.seq (.assign "mp_acc" (.add (W "mp_acc") (.lit 1))) (.assign "mp_p" (.add (W "mp_p") (.lit 1))))
    (.seq (.assign "mp_acc" (.add (W "mp_acc") (.lit 2)))
      (.assign "mp_p" (.add (W "mp_p") (.lit 2)))))))

/-- One step of the scan. -/
def scanBody : Com := .seq (.assign "mp_t" (.get "a" (W "mp_p"))) tagCase

/-- **The scan of the formula.** -/
def scanLoop : Com := .seq (.assign "mp_acc" (.lit 0)) (.while (.lt (W "mp_p") (W "rt_n")) scanBody)

/-- **The program.** -/
def prog : Com :=
  .seq Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape (.seq headSkip (.seq scanLoop (.write (W "mp_acc"))))

/-- The scalars of the program. -/
def progVars : List String :=
  ["rt_n", "rt_i", "rt_v", "mp_s", "mp_p", "mp_i", "mp_c", "mp_ar", "mp_t", "mp_l", "mp_acc"]

/-! ### The scan -/

/-- The bounds a step of the scan needs, in terms of the state. -/
def StepOk (B : ℕ) (σ : Env) : Prop :=
  σ.vars "mp_p" < (σ.arrs "a").length ∧ σ.vars "mp_p" + 3 < B ∧ σ.vars "mp_acc" + 3 < B ∧
    6 < B ∧ (σ.arrs "a").getD (σ.vars "mp_p") 0 < B ∧
    ((σ.arrs "a").getD (σ.vars "mp_p") 0 = 0 → σ.vars "mp_p" + 2 < (σ.arrs "a").length ∧
      σ.vars "mp_acc" + (σ.arrs "a").getD (σ.vars "mp_p" + 2) 0 + 1 < B ∧
      σ.vars "mp_p" + 3 + (σ.arrs "a").getD (σ.vars "mp_p" + 2) 0 < B) ∧
    ((σ.arrs "a").getD (σ.vars "mp_p") 0 = 1 → σ.vars "mp_p" + 1 < (σ.arrs "a").length ∧
      σ.vars "mp_acc" + (σ.arrs "a").getD (σ.vars "mp_p" + 1) 0 + 1 < B ∧
      σ.vars "mp_p" + 2 + (σ.arrs "a").getD (σ.vars "mp_p" + 1) 0 < B)

/-- A specification proved one starting state at a time. -/
theorem spec_of_point {B : ℕ} {P : Env → Prop} {c : Com} {Q : Env → Env → Prop} {K : ℕ}
    (h : ∀ σ, P σ → Spec B (fun τ => τ = σ) c Q K) : Spec B P c Q K :=
  fun σ hσ => h σ hσ σ rfl

/-- The postcondition of a step. -/
def StepPost (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.vars "rt_n" = σ.vars "rt_n" ∧
    σ'.vars "mp_acc" = σ.vars "mp_acc" + dAcc ((σ.arrs "a").getD (σ.vars "mp_p") 0)
      ((σ.arrs "a").getD (σ.vars "mp_p" + 1) 0) ((σ.arrs "a").getD (σ.vars "mp_p" + 2) 0) ∧
    σ'.vars "mp_p" = σ.vars "mp_p" + dP ((σ.arrs "a").getD (σ.vars "mp_p") 0)
      ((σ.arrs "a").getD (σ.vars "mp_p" + 1) 0) ((σ.arrs "a").getD (σ.vars "mp_p" + 2) 0) ∧
    σ'.out = σ.out

set_option maxHeartbeats 2000000 in
theorem scanBody_spec {B : ℕ} : Spec B (StepOk B) scanBody StepPost 60 := by
  refine spec_of_point fun σ hσ => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hσ
  unfold scanBody tagCase StepPost
  by_cases c0 : (σ.arrs "a").getD (σ.vars "mp_p") 0 = 0
  · obtain ⟨g1, g2, g3⟩ := h6 c0
    run_vcg
    all_goals subst_vars
    all_goals
      try simp only [vars_setVar, arrs_setVar, out_setVar, String.reduceEq,
        ↓reduceIte] at *
    all_goals first | omega | (simp only [dAcc, dP, true_and, and_true]; (split_ifs; omega))
  · by_cases c1 : (σ.arrs "a").getD (σ.vars "mp_p") 0 = 1
    · obtain ⟨g1, g2, g3⟩ := h7 c1
      run_vcg
      all_goals subst_vars
      all_goals
        try simp only [vars_setVar, arrs_setVar, out_setVar, String.reduceEq,
          ↓reduceIte] at *
      all_goals first | omega | (simp only [dAcc, dP, true_and, and_true]; (split_ifs; omega))
    · run_vcg
      all_goals subst_vars
      all_goals
        try simp only [vars_setVar, arrs_setVar, out_setVar, String.reduceEq,
          ↓reduceIte] at *
      all_goals first | omega | (simp only [dAcc, dP, true_and, and_true]; (split_ifs; omega))

/-! ### The scan loop -/

/-- The invariant of the scan: the pending formulas begin at `mp_p`, and `mp_acc` plus their size
is the size of `φ`. -/
def SI (w : List ℕ) (φ : Formula) (σ : Env) : Prop :=
  σ.arrs "a" = w ∧ σ.vars "rt_n" = w.length ∧ σ.vars "mp_p" ≤ w.length ∧
    ∃ fs, w.drop (σ.vars "mp_p") = pend fs ∧ σ.vars "mp_acc" + psize fs = φ.size

theorem stepOk_of_SI {w : List ℕ} {φ : Formula} {B : ℕ} (hw : ∀ v ∈ w, v < B)
    (hφ : φ.size ≤ w.length) (hB : w.length + 6 < B) {σ : Env} (hI : SI w φ σ)
    (hp : σ.vars "mp_p" < w.length) : StepOk B σ ∧
      ∃ fs', w.drop (σ.vars "mp_p" + dP ((σ.arrs "a").getD (σ.vars "mp_p") 0)
          ((σ.arrs "a").getD (σ.vars "mp_p" + 1) 0) ((σ.arrs "a").getD (σ.vars "mp_p" + 2) 0)) =
          pend fs' ∧
        σ.vars "mp_acc" + dAcc ((σ.arrs "a").getD (σ.vars "mp_p") 0)
          ((σ.arrs "a").getD (σ.vars "mp_p" + 1) 0) ((σ.arrs "a").getD (σ.vars "mp_p" + 2) 0) +
          psize fs' = φ.size ∧
        σ.vars "mp_p" + dP ((σ.arrs "a").getD (σ.vars "mp_p") 0)
          ((σ.arrs "a").getD (σ.vars "mp_p" + 1) 0) ((σ.arrs "a").getD (σ.vars "mp_p" + 2) 0) ≤
          w.length := by
  obtain ⟨ha, hn, hle, fs, hd, hacc⟩ := hI
  unfold StepOk
  rw [ha]
  have hfs : fs ≠ [] := by
    rintro rfl
    rw [pend_nil, List.drop_eq_nil_iff] at hd
    omega
  obtain ⟨f, fs0, rfl⟩ := List.exists_cons_of_ne_nil hfs
  obtain ⟨fs', hd', hsz, hlen, h0, h1⟩ := scan_step hd
  have hgetD : ∀ j, w.getD j 0 < B := fun j => by
    rw [List.getD_eq_getElem?_getD]
    rcases h : w[j]? with _ | v
    · simp; omega
    · exact hw v (List.mem_of_getElem? h)
  simp only [psize_cons] at hacc
  refine ⟨⟨hp, by omega, by omega, by omega, hgetD _, fun h => ⟨h0 h, ?_, ?_⟩,
    fun h => ⟨h1 h, ?_, ?_⟩⟩, fs', hd', by omega, by omega⟩
  · have : dAcc (w.getD (σ.vars "mp_p") 0) (w.getD (σ.vars "mp_p" + 1) 0)
        (w.getD (σ.vars "mp_p" + 2) 0) = w.getD (σ.vars "mp_p" + 2) 0 + 1 := by
      rw [dAcc, if_pos h]
    omega
  · have : dP (w.getD (σ.vars "mp_p") 0) (w.getD (σ.vars "mp_p" + 1) 0)
        (w.getD (σ.vars "mp_p" + 2) 0) = 3 + w.getD (σ.vars "mp_p" + 2) 0 := by
      rw [dP, if_pos h]
    omega
  · have : dAcc (w.getD (σ.vars "mp_p") 0) (w.getD (σ.vars "mp_p" + 1) 0)
        (w.getD (σ.vars "mp_p" + 2) 0) = w.getD (σ.vars "mp_p" + 1) 0 + 1 := by
      rw [dAcc, if_neg (by omega), if_pos h]
    omega
  · have : dP (w.getD (σ.vars "mp_p") 0) (w.getD (σ.vars "mp_p" + 1) 0)
        (w.getD (σ.vars "mp_p" + 2) 0) = 2 + w.getD (σ.vars "mp_p" + 1) 0 := by
      rw [dP, if_neg (by omega), if_pos h]
    omega

theorem dP_pos (t l1 l2 : ℕ) : 1 ≤ dP t l1 l2 := by
  unfold dP; split_ifs <;> omega

theorem scanWhile_spec {w : List ℕ} {φ : Formula} {B : ℕ} (hw : ∀ v ∈ w, v < B)
    (hφ : φ.size ≤ w.length) (hB : w.length + 6 < B) :
    Spec B (SI w φ) (.while (.lt (W "mp_p") (W "rt_n")) scanBody)
      (fun _ σ' => SI w φ σ' ∧ σ'.vars "mp_p" = w.length) (64 * w.length + 4) := by
  refine (Spec.while_count (b := .lt (W "mp_p") (W "rt_n")) (SI w φ)
    (fun σ => w.length - σ.vars "mp_p") 60 ?_ ?_ (fun _ h => h) ?_).post ?_
  · intro σ hI
    exact evalB_condLt_vars (by have := hI.2.2.1; omega) (by rw [hI.2.1]; omega)
  · intro σ ⟨hI, hc⟩
    have hp : σ.vars "mp_p" < w.length := by
      have := lt_of_condLt_true hc; rw [hI.2.1] at this; exact this
    obtain ⟨hok, fs', hd', hacc', hle'⟩ := stepOk_of_SI hw hφ hB hI hp
    obtain ⟨σ', hr, ha', hn', hacc, hpp, -⟩ := scanBody_spec σ hok
    have hdP := dP_pos ((σ.arrs "a").getD (σ.vars "mp_p") 0)
      ((σ.arrs "a").getD (σ.vars "mp_p" + 1) 0) ((σ.arrs "a").getD (σ.vars "mp_p" + 2) 0)
    refine ⟨σ', hr, ⟨by rw [ha']; exact hI.1, by rw [hn']; exact hI.2.1, by rw [hpp]; exact hle',
      fs', by rw [hpp]; exact hd', by rw [hacc]; exact hacc'⟩, ?_⟩
    rw [hpp]; omega
  · intro σ _
    simp only [Cond.size, Expr.size]
    have : w.length - σ.vars "mp_p" ≤ w.length := Nat.sub_le _ _
    nlinarith
  · intro σ σ' _ ⟨hI, hc⟩
    refine ⟨hI, ?_⟩
    have := le_of_condLt_false hc
    rw [hI.2.1] at this
    have := hI.2.2.1
    omega

/-- At the end of the scan the accumulator holds the size of `φ`. -/
theorem acc_of_SI_end {w : List ℕ} {φ : Formula} {σ : Env} (hI : SI w φ σ)
    (hp : σ.vars "mp_p" = w.length) : σ.vars "mp_acc" = φ.size := by
  obtain ⟨-, -, -, fs, hd, hacc⟩ := hI
  rw [hp, List.drop_length] at hd
  rw [pend_eq_nil hd.symm, psize_nil, Nat.add_zero] at hacc
  exact hacc

end Lax496464Proofs.WHierarchy.Logic.McParam.Prog
