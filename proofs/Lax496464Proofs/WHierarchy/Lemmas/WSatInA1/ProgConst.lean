import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse

/-! # Phase 2: the constants

`consts_value`: phase 2 computes `M`, `d^k`, the size of the array of numbers, `M^(d+2)`, `k+1`,
`(k+1)^(d+1)` and the other constants of the program. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs

variable {B : ℕ}

/-! ### Powers -/

def PwI (b n : ℕ) (σ : Env) : Prop :=
  σ.vars "w_pb" = b ∧ σ.vars "w_pn" = n ∧ σ.vars "w_pi" ≤ n ∧ σ.vars "w_pr" = b ^ σ.vars "w_pi"

theorem powBody_spec {b n : ℕ} (hb : ∀ i ≤ n, b ^ i < B) (hn : n + 1 < B) :
    Spec B (fun σ => PwI b n σ ∧ σ.vars "w_pi" < n)
      (.seq (.assign "w_pr" (.mul (V "w_pr") (V "w_pb"))) (bump "w_pi"))
      (fun σ σ' => PwI b n σ' ∧ σ'.vars "w_pi" = σ.vars "w_pi" + 1) 10 := by
  refine Spec.pre (P := fun σ => PwI b n σ ∧ σ.vars "w_pi" < n ∧ b ^ σ.vars "w_pi" < B ∧
    b ^ (σ.vars "w_pi" + 1) < B ∧ b < B) ?_ ?_
  · run_vcg
    all_goals (simp only [PwI] at *; simp_all [Env.setVar, pow_succ]; try omega)
  · rintro σ ⟨hI, hlt⟩
    exact ⟨hI, hlt, hb _ (by omega), hb _ (by omega), by simpa using hb 1 (by omega)⟩

/-- **A power.** -/
theorem powCom_spec {b n : ℕ} (hb : ∀ i ≤ n, b ^ i < B) (hn : n + 1 < B) :
    Spec B (fun σ => σ.vars "w_pb" = b ∧ σ.vars "w_pn" = n) powCom
      (fun σ σ' => σ'.vars "w_pr" = b ^ n ∧
        (∀ y, y ≠ "w_pr" → y ≠ "w_pi" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) (14 * n + 10) := by
  rintro σ ⟨hb', hn'⟩
  have hloop := Spec.forRangeZero (B := B) "w_pi" "w_pn" (PwI b n) n 10 (by omega)
    (fun σ h => h.2.2.1) (fun σ h => h.2.1) (powBody_spec hb hn)
  have h1 : Run B (.assign "w_pr" (.lit 1)) σ (σ.setVar "w_pr" 1) 2 :=
    Run.assign (evalB_lit (by have := hb 0 (by omega); simp at this; omega))
  obtain ⟨σ', hr, ⟨⟨-, -, -, hpr⟩, hi⟩, hv, ha, hin, hout⟩ :=
    hloop.frame.run (σ := σ.setVar "w_pr" 1)
      ⟨by simp [Env.setVar, hb'], by simp [Env.setVar, hn'], by simp [Env.setVar],
        by simp [Env.setVar]⟩
  refine ⟨σ', (h1.seq hr).mono (by omega), by rw [hpr, hi], fun y h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [hv y (by simp [Com.wvars, h1, h2])]; simp [Env.setVar, h1]
  · funext a; rw [ha a (by simp [Com.warrs])]; rfl
  · rw [hin (by simp [Com.reads])]; rfl
  · rw [hout (by simp [Com.NoWrite])]; rfl

/-! ### The constants -/

/-- The constants after `consts`. -/
def CPost (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Prop :=
  σ.vars "w_M" = MM cl ∧ σ.vars "w_dk" = d ^ k ∧ σ.vars "hs_t" = sz cl d k ∧
    σ.vars "w_md" = MM cl ^ (d + 2) ∧ σ.vars "w_K1" = k + 1 ∧ σ.vars "w_F" = FF d k ∧
    σ.vars "w_nv" = nv d k ∧ σ.vars "w_d1" = d + 1

/-- The value bounds `consts` needs. -/
structure CBound (cl : List (List ℕ)) (d k B : ℕ) : Prop where
  dk : ∀ i ≤ k, d ^ i < B
  md : ∀ i ≤ d + 2, MM cl ^ i < B
  ff : ∀ i ≤ d + 1, (k + 1) ^ i < B
  sz : sz cl d k + 1 < B
  nv : nv d k + 1 < B
  small : MM cl + d + k + 4 < B

/-- The cost of `consts`. -/
def Kconst (d k : ℕ) : ℕ := 14 * k + 14 * (d + 2) + 14 * (d + 1) + 200

set_option maxHeartbeats 4000000 in
theorem consts_value {cl : List (List ℕ)} {d k : ℕ} (hB : CBound cl d k B) :
    Spec B (fun σ => σ.vars "w_L" = nL cl ∧ σ.vars "w_k" = k ∧ σ.vars "w_m" = cl.length)
      (consts d) (fun _ σ' => CPost cl d k σ') (Kconst d k) := by
  have h1 := hB.small
  have hsz := hB.sz
  have hnv := hB.nv
  have hszE : sz cl d k = 2 * nL cl + cl.length + cl.length * d ^ k := rfl
  have hnvE : nv d k = (k + 1) + FF d k * (k + 1) := rfl
  have hFF : FF d k = (k + 1) ^ (d + 1) := rfl
  have hm1 : cl.length * d ^ k ≤ sz cl d k := by rw [hszE]; omega
  have hFk : FF d k * (k + 1) ≤ nv d k := by rw [hnvE]; omega
  have hF : FF d k < B := by rw [hFF]; exact hB.ff _ le_rfl
  have hdk : d ^ k < B := hB.dk _ le_rfl
  have hmd : MM cl ^ (d + 2) < B := hB.md _ le_rfl
  have hMM : MM cl = nL cl + 4 := rfl
  unfold consts Kconst
  run_vcg [powCom_spec hB.dk (by omega), powCom_spec hB.md (by omega),
    powCom_spec hB.ff (by omega)]
  all_goals (try simp only [CPost] at *)
  all_goals (try simp_all [Env.setVar]; try omega)

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst
