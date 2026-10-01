import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Cost
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgOk
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Reduction
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-! # The reduction runs in fixed-parameter time

The IMP+ program `cmd d` computes `red d` on the instances of `p-WSat(d-CNF)`, with values below
`Bv` and cost at most `8000 · Pk³ · (n + 1)²`; `ImpBridge.fptTimeOn_of_solves` turns this into
`FptTimeOn` with `f(k) = 90000 · Pk(k)³` and exponent `2`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Time

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax808846Proofs.Transfer Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgMain
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgOk Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Bounds
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Cost Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Reduction

variable {d : ℕ}

/-! ### Outputs stay below the bound -/

theorem bigStepB_out {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k)
    (hσ : ∀ v ∈ σ.out, v < B) : ∀ v ∈ σ'.out, v < B := by
  induction h with
  | skip => exact hσ
  | assign _ => exact hσ
  | store _ _ _ => exact hσ
  | seq _ _ ih ih' => exact ih' (ih hσ)
  | ite_true _ _ ih => exact ih hσ
  | ite_false _ _ ih => exact ih hσ
  | while_true _ _ _ ih ih' => exact ih' (ih hσ)
  | while_false _ => exact hσ
  | read _ => exact hσ
  | write he =>
    intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact hσ v hv
    · exact (Expr.eval_and_lt_of_evalB he).2

/-! ### The run -/

/-- The array lengths of the initial environment. -/
def extOf (cl : List (List ℕ)) (d k : ℕ) (x : List ℕ) (a : String) : ℕ :=
  if a = "a" then x.length else if a = "co" then cl.length + 1 else if a = "cd" then nL cl
  else if a = "hs_mem" then sz cl d k else if a = "fp_f" then sz cl d k
  else if a = "ch" then k + 1 else 0

/-- The cost of the whole program. -/
def Kall (cl : List (List ℕ)) (d k : ℕ) : ℕ := 16 * (cl.length + nL cl + 2) + 7 + Kbody cl d k

theorem cmd_run {cl : List (List ℕ)} {k B : ℕ} (hd : ∀ C ∈ cl, C.length ≤ d)
    (hB : BB cl d k B) :
    ∃ σ', Run B (cmd d) (initEnv (extOf cl d k (wordOf' cl k)) ((wordOf' cl k).length ::
      wordOf' cl k)) σ' (Kall cl d k) ∧ σ'.out = structWord cl d k ++ (phi d k).encode := by
  set x := wordOf' cl k with hx
  have hxl : x.length = cl.length + nL cl + 2 := length_wordOf'
  have hl := hB.hl
  have h1 := Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape_spec x
    (initEnv (extOf cl d k x) (x.length :: x)) hB.hx (by omega) rfl
    (by simp [initEnv, extOf])
  have h2 := body_spec hB hd
  have h := Spec.seq (R := fun _ σ'' => σ''.out = structWord cl d k ++ (phi d k).encode) h1 h2 ?_ ?_
  · obtain ⟨σ', hr, hq⟩ := h _ rfl
    exact ⟨σ', hr.mono (by unfold Kall; rw [← hxl]), hq⟩
  · rintro σ σ' rfl ⟨ha, -, -, -, -, harr⟩
    refine ⟨ha, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [harr _ (by decide)] <;> simp [initEnv, extOf]
  · rintro σ σ' σ'' rfl ⟨-, -, -, hout, -⟩ hq
    rw [hq, hout]
    simp [initEnv]

/-! ### The bounds -/

/-- The factor of the time bound. -/
def ff (d k : ℕ) : ℕ := 90000 * Pk d k ^ 3

theorem computable_ff (d : ℕ) : Computable (ff d) := by
  open Lax496464Proofs.WHierarchy.ComputableBounds in
  have h1 : Computable fun k : ℕ => k + 1 := computable_add Computable.id (Computable.const 1)
  have h2 : Computable fun k : ℕ => k + 2 := computable_add Computable.id (Computable.const 2)
  have hP : Computable (Pk d) :=
    computable_mul (computable_exp (d + 2) h1) (computable_pow (d + 3) h2)
  exact computable_mul (Computable.const 90000) (computable_pow 3 hP)

theorem le_two_pow (a : ℕ) : a ≤ 2 ^ a := (Nat.lt_two_pow_self).le

/-- The bound in binary. -/
theorem Bv_le (d n k : ℕ) : 8 * Bv d n k ≤ 2 ^ (7 + n + (n + 4) * (d + k + 5) + Pk d k) := by
  unfold Bv
  have h1 : (n + 4) ^ (d + k + 5) ≤ 2 ^ ((n + 4) * (d + k + 5)) := by
    calc (n + 4) ^ (d + k + 5) ≤ (2 ^ (n + 4)) ^ (d + k + 5) := Nat.pow_le_pow_left (le_two_pow _) _
      _ = 2 ^ ((n + 4) * (d + k + 5)) := by rw [← pow_mul]
  have h2 := le_two_pow (Pk d k)
  have e : 2 ^ (7 + n + (n + 4) * (d + k + 5) + Pk d k) =
      128 * 2 ^ n * 2 ^ ((n + 4) * (d + k + 5)) * 2 ^ Pk d k := by
    rw [pow_add, pow_add, pow_add]; ring
  rw [e]
  have := Nat.mul_le_mul (Nat.mul_le_mul (le_refl (128 * 2 ^ n)) h1) h2
  nlinarith

theorem exp_le (d n k : ℕ) : 7 + n + (n + 4) * (d + k + 5) + Pk d k ≤ ff d k * (n + 1) ^ 2 := by
  unfold ff
  have hP1 := one_le_Pk d k
  have hdP := d_le_Pk d k
  have hkP := k_le_Pk d k
  set P := Pk d k
  have h1 : (n + 4) * (d + k + 5) ≤ (4 * (n + 1)) * (3 * P) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : P ≤ P ^ 3 := by
    calc P = P ^ 1 := (pow_one P).symm
      _ ≤ P ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : n + 1 ≤ (n + 1) ^ 2 := by nlinarith
  have h4 : P * (n + 1) ≤ P ^ 3 * (n + 1) ^ 2 := Nat.mul_le_mul h2 h3
  have h5 : 1 ≤ P * (n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have e : 90000 * P ^ 3 * (n + 1) ^ 2 = 90000 * (P ^ 3 * (n + 1) ^ 2) := by ring
  rw [e]
  nlinarith

theorem span_le (B : ℕ) (hB : 59 ≤ B) : layout.span B ≤ 7 * B := by
  simp [Layout.span, layout, progVars]; omega

theorem Bv_ge' (d n k : ℕ) : 59 ≤ Bv d n k := by
  unfold Bv
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 4 ≤ (n + 4) ^ (d + k + 5) := by
    calc 4 ≤ n + 4 := by omega
      _ = (n + 4) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 := one_le_Pk d k
  have : 4 ≤ 2 ^ n * (n + 4) ^ (d + k + 5) * Pk d k := by
    have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3; simpa using this
  nlinarith

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Time
