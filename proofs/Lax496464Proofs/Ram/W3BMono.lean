import Lax496464Proofs.Ram.Imp

/-!
# A run below a bound is a run below every larger bound
-/

namespace Lax496464Proofs.Ram.W3BMono

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem evalB_mono {B B' : ℕ} (hB : B ≤ B') {σ : Env} :
    ∀ (e : Expr) {v : ℕ}, e.evalB B σ = some v → e.evalB B' σ = some v := by
  intro e
  induction e with
  | lit n => intro v h; simp only [evalB_lit_iff] at h ⊢; omega
  | var x => intro v h; simp only [evalB_var_iff] at h ⊢; omega
  | get a i ih =>
    intro v h
    simp only [evalB_get_iff] at h ⊢
    obtain ⟨k, hk, hv, hlt⟩ := h
    exact ⟨k, ih hk, hv, by omega⟩
  | bin op e f ihe ihf =>
    intro v h
    simp only [evalB_bin_iff] at h ⊢
    obtain ⟨m, n, hm, hn, hv, hlt⟩ := h
    exact ⟨m, n, ihe hm, ihf hn, hv, by omega⟩

theorem condB_mono {B B' : ℕ} (hB : B ≤ B') {σ : Env} (b : Cond) {r : Bool}
    (h : b.evalB B σ = some r) : b.evalB B' σ = some r := by
  cases b with
  | eq e f =>
    simp only [evalB_condEq_iff] at h ⊢
    obtain ⟨m, n, hm, hn, hr⟩ := h
    exact ⟨m, n, evalB_mono hB e hm, evalB_mono hB f hn, hr⟩
  | lt e f =>
    simp only [evalB_condLt_iff] at h ⊢
    obtain ⟨m, n, hm, hn, hr⟩ := h
    exact ⟨m, n, evalB_mono hB e hm, evalB_mono hB f hn, hr⟩

theorem bigStepB_mono {B B' : ℕ} (hB : B ≤ B') {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) : BigStepB B' c σ σ' k := by
  induction h with
  | skip => exact .skip
  | assign h => exact .assign (evalB_mono hB _ h)
  | store hi he hk => exact .store (evalB_mono hB _ hi) (evalB_mono hB _ he) hk
  | seq _ _ ih ih' => exact .seq ih ih'
  | ite_true hb _ ih => exact .ite_true (condB_mono hB _ hb) ih
  | ite_false hb _ ih => exact .ite_false (condB_mono hB _ hb) ih
  | while_true hb _ _ ih ih' => exact .while_true (condB_mono hB _ hb) ih ih'
  | while_false hb => exact .while_false (condB_mono hB _ hb)
  | read h => exact .read h
  | write h => exact .write (evalB_mono hB _ h)

theorem Run.mono_bound {B B' : ℕ} (hB : B ≤ B') {c : Com} {σ σ' : Env} {K : ℕ}
    (h : Run B c σ σ' K) : Run B' c σ σ' K := by
  obtain ⟨k, hk, hbs⟩ := h
  exact ⟨k, hk, bigStepB_mono hB hbs⟩

end Lax496464Proofs.Ram.W3BMono
