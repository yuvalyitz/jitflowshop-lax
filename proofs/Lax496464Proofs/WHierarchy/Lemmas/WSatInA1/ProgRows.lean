import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx

/-! # Phases 3, 5, 6: the numbers of the variables, of `C` and of `N`

`varRows_spec`: phase 3 stores the numbers of the variables of the occurrences; `canonRows_spec`:
phase 5 stores the numbers of the tuples of `C`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx

variable {cl : List (List ℕ)} {d k B : ℕ}

/-! ### 3. The variables -/

def VI (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.vars "w_j" ≤ nL cl ∧ σ.arrs "hs_mem" = hsS cl d k (σ.vars "w_j")

set_option maxHeartbeats 2000000 in
theorem varBody_spec (hB : BB cl d k B) :
    Spec B (fun σ => VI cl d k σ ∧ σ.vars "w_j" < nL cl)
      (.seq (.store "hs_mem" (V "w_j") (.mul (.div (.get "cd" (V "w_j")) (.lit 2)) (V "w_M")))
        (bump "w_j"))
      (fun σ σ' => VI cl d k σ' ∧ σ'.vars "w_j" = σ.vars "w_j" + 1) 20 := by
  have hsz := nL_le_sz cl d k
  have hl := hB.hl
  have hMB := hB.cb.small
  refine Spec.pre (P := fun σ => VI cl d k σ ∧ σ.vars "w_j" < nL cl ∧
      σ.vars "w_j" < (σ.arrs "hs_mem").length ∧ σ.vars "w_j" < (σ.arrs "cd").length ∧
      (σ.arrs "cd").getD (σ.vars "w_j") 0 < B ∧
      (σ.arrs "cd").getD (σ.vars "w_j") 0 / 2 * σ.vars "w_M" < B ∧
      (σ.arrs "hs_mem").set (σ.vars "w_j") ((σ.arrs "cd").getD (σ.vars "w_j") 0 / 2 * σ.vars "w_M") =
        hsS cl d k (σ.vars "w_j" + 1) ∧ σ.vars "w_j" + 1 < B) ?_ ?_
  · run_vcg
    all_goals (try simp only [VI, Ctx, CPost] at *)
    all_goals (try simp_all [Env.setVar, Env.setArr]; try omega)
  · rintro σ ⟨⟨hc, hj, hh⟩, hlt⟩
    obtain ⟨ha, hco, hcd, hm, hL, hk, hM, hrest⟩ := hc
    have hcode : (σ.arrs "cd").getD (σ.vars "w_j") 0 = code cl (σ.vars "w_j") := by rw [hcd]; rfl
    refine ⟨⟨⟨ha, hco, hcd, hm, hL, hk, hM, hrest⟩, hj, hh⟩, hlt, ?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [hh, length_hsS]; omega
    · rw [hcd]; exact hlt
    · rw [hcode]; exact code_lt hB.hx hlt
    · rw [hcode, hM]; exact hB.var _ hlt
    · rw [hh, hcode, hM, ← hs_var cl d k hlt]; exact hsS_set cl d k (by omega)

theorem varRows_spec (hB : BB cl d k B) :
    Spec B (fun σ => Ctx cl d k σ ∧ σ.arrs "hs_mem" = hsS cl d k 0) varRows
      (fun _ σ' => Ctx cl d k σ' ∧ σ'.arrs "hs_mem" = hsS cl d k (nL cl)) (24 * nL cl + 6) := by
  have hl := hB.hl
  refine Spec.post (Spec.pre (Spec.forRangeZero "w_j" "w_L" (VI cl d k) (nL cl) 20 (by omega)
    (fun σ h => h.2.1) (fun σ h => h.1.2.2.2.2.1) (varBody_spec hB)) ?_) ?_
  · rintro σ ⟨hc, hh⟩
    refine ⟨hc.keep (fun y hy => ?_) (fun a _ => rfl), by simp [Env.setVar], by simp [Env.setVar, hh]⟩
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · rintro σ σ' - ⟨⟨hc, -, hh⟩, hj⟩
    exact ⟨hc, by rw [hh, hj]⟩

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows

/-! ### 5. The tuples of `C` -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx

variable {cl : List (List ℕ)} {d k B : ℕ}

/-- The first occurrences after the first pass. -/
def F1 (cl : List (List ℕ)) (d k : ℕ) : List ℕ :=
  Lax496464Proofs.WHierarchy.HittingSet.Firsts.firsts (hsS cl d k (nL cl))

theorem WH_F1_getD {j : ℕ} (hj : j < nL cl) : (F1 cl d k).getD j 0 = fst cl j :=
  firsts_hsS_nL cl d k hj

theorem length_F1 : (F1 cl d k).length = sz cl d k := by
  simp [F1, Lax496464Proofs.WHierarchy.HittingSet.Firsts.firsts, length_hsS]

theorem MM_sq_lt (hB : BB cl d k B) : MM cl * MM cl < B := by
  have h1 := pow_le_big cl (show 2 ≤ d + k + 4 by omega)
  have := hB.big
  rw [pow_two] at h1; omega

def CI (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧ σ.vars "w_j" ≤ nL cl ∧
    σ.arrs "hs_mem" = hsS cl d k (nL cl + σ.vars "w_j")

set_option maxHeartbeats 2000000 in
theorem canonBody_spec (hB : BB cl d k B) :
    Spec B (fun σ => CI cl d k σ ∧ σ.vars "w_j" < nL cl)
      (.seq (.store "hs_mem" (.add (V "w_L") (V "w_j"))
        (.add (.lit 1) (.mul (V "w_M") (.get "fp_f" (V "w_j"))))) (bump "w_j"))
      (fun σ σ' => CI cl d k σ' ∧ σ'.vars "w_j" = σ.vars "w_j" + 1) 30 := by
  have hsz := nL_le_sz cl d k
  have hl := hB.hl
  have hMB := hB.cb.small
  have hsq := MM_sq_lt hB
  have hnM := nL_lt_MM cl
  have hszB := hB.cb.sz
  refine Spec.pre (P := fun σ => CI cl d k σ ∧ σ.vars "w_j" < nL cl ∧
      σ.vars "w_L" + σ.vars "w_j" < (σ.arrs "hs_mem").length ∧
      σ.vars "w_j" < (σ.arrs "fp_f").length ∧
      (σ.arrs "fp_f").getD (σ.vars "w_j") 0 < B ∧
      σ.vars "w_M" * (σ.arrs "fp_f").getD (σ.vars "w_j") 0 < B ∧
      1 + σ.vars "w_M" * (σ.arrs "fp_f").getD (σ.vars "w_j") 0 < B ∧
      (σ.arrs "hs_mem").set (σ.vars "w_L" + σ.vars "w_j")
        (1 + σ.vars "w_M" * (σ.arrs "fp_f").getD (σ.vars "w_j") 0) =
        hsS cl d k (nL cl + (σ.vars "w_j" + 1)) ∧ σ.vars "w_L" + σ.vars "w_j" < B ∧
        σ.vars "w_j" + 1 < B) ?_ ?_
  · run_vcg
    all_goals (try simp only [CI, Ctx, CPost] at *)
    all_goals (try simp_all [Env.setVar, Env.setArr]; try omega)
  · rintro σ ⟨⟨hc, hf, hj, hh⟩, hlt⟩
    obtain ⟨ha, hco, hcd, hm, hL, hk, hM, hrest⟩ := hc
    have hfj : (σ.arrs "fp_f").getD (σ.vars "w_j") 0 = fst cl (σ.vars "w_j") := by
      rw [hf]; exact WH_F1_getD hlt
    have hfl := fst_lt cl hlt
    have hmul : MM cl * fst cl (σ.vars "w_j") < MM cl * MM cl :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    refine ⟨⟨⟨ha, hco, hcd, hm, hL, hk, hM, hrest⟩, hf, hj, hh⟩, hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by omega⟩
    · rw [hh, length_hsS, hL]; omega
    · rw [hf, length_F1]; omega
    · rw [hfj]; omega
    · rw [hfj, hM]; omega
    · rw [hfj, hM]; omega
    · rw [hh, hfj, hM, hL, ← hs_canon cl d k hlt]; exact hsS_set cl d k (by omega)
    · rw [hL]; omega

theorem canonRows_spec (hB : BB cl d k B) :
    Spec B (fun σ => Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧
        σ.arrs "hs_mem" = hsS cl d k (nL cl)) canonRows
      (fun _ σ' => Ctx cl d k σ' ∧ σ'.arrs "fp_f" = F1 cl d k ∧
        σ'.arrs "hs_mem" = hsS cl d k (2 * nL cl)) (34 * nL cl + 6) := by
  have hl := hB.hl
  refine Spec.post (Spec.pre (Spec.forRangeZero "w_j" "w_L" (CI cl d k) (nL cl) 30 (by omega)
    (fun σ h => h.2.2.1) (fun σ h => h.1.2.2.2.2.1) (canonBody_spec hB)) ?_) ?_
  · rintro σ ⟨hc, hf, hh⟩
    refine ⟨hc.keep (fun y hy => ?_) (fun a _ => rfl), by simp [Env.setVar, hf],
      by simp [Env.setVar], by simp [Env.setVar, hh]⟩
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · rintro σ σ' - ⟨⟨hc, hf, -, hh⟩, hj⟩
    exact ⟨hc, hf, by rw [hh, hj]; ring_nf⟩

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows
