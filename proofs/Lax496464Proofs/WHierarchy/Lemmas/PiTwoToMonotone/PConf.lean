import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDec

/-!
# The Conflict Test

`cfCom_spec`: with the blocks and values `b1, v1, b2, v2` in `bd1, vd1, bd2, vd2`, `cfCom` sets
`g_cf` to `1` iff they are in `Blocks.Conflict`, by one loop over the pairs of slots.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PConf

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (Frame Frame.refl Frame.trans Frame.mono Frame.setVar)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDec

variable {B : ℕ}

set_option maxHeartbeats 8000000 in
theorem cfTest_spec :
    Spec B (fun σ => σ.vars "g_j" < (σ.arrs "bd1").length ∧ σ.vars "g_j" < (σ.arrs "vd1").length ∧
        σ.vars "g_j2" < (σ.arrs "bd2").length ∧ σ.vars "g_j2" < (σ.arrs "vd2").length ∧
        (σ.arrs "bd1").getD (σ.vars "g_j") 0 < B ∧ (σ.arrs "vd1").getD (σ.vars "g_j") 0 + 1 < B ∧
        (σ.arrs "bd2").getD (σ.vars "g_j2") 0 < B ∧ (σ.arrs "vd2").getD (σ.vars "g_j2") 0 < B ∧
        σ.vars "w_k" < B ∧ σ.vars "g_NT" < B ∧ σ.vars "g_j" < B ∧ σ.vars "g_j2" < B ∧ 1 < B)
      cfTest
      (fun σ σ' => σ'.vars "g_cf" =
          (if (σ.arrs "bd1").getD (σ.vars "g_j") 0 < σ.vars "w_k" ∧
              (σ.vars "g_NT" < (σ.arrs "vd1").getD (σ.vars "g_j") 0 + 1 ∨
                ((σ.arrs "bd2").getD (σ.vars "g_j2") 0 < σ.vars "w_k" ∧
                  (((σ.arrs "bd1").getD (σ.vars "g_j") 0 = (σ.arrs "bd2").getD (σ.vars "g_j2") 0 ∧
                      (σ.arrs "vd1").getD (σ.vars "g_j") 0 ≠ (σ.arrs "vd2").getD (σ.vars "g_j2") 0) ∨
                    ((σ.arrs "bd1").getD (σ.vars "g_j") 0 < (σ.arrs "bd2").getD (σ.vars "g_j2") 0 ∧
                      (σ.arrs "vd2").getD (σ.vars "g_j2") 0 <
                        (σ.arrs "vd1").getD (σ.vars "g_j") 0 + 1)))) then 1
            else σ.vars "g_cf") ∧ Frame ["g_cf"] [] σ σ' ∧ σ'.out = σ.out) 80 := by
  unfold cfTest setIf
  run_vcg
  all_goals try (simp [Env.setVar] at *; omega)
  all_goals refine ⟨?_, ?_, rfl⟩
  all_goals first
    | exact Frame.refl _ _ _
    | exact Frame.setVar σ (by simp) _
    | exact (Frame.setVar σ (by simp) _).trans (Frame.setVar _ (by simp) _)
    | (simp only [Env.setVar, if_true, String.reduceEq, if_false] at *; split_ifs <;> omega)
    | (split_ifs <;> omega)

/-- The arrays and scalars the test reads. -/
def CA (k N D : ℕ) (b1 v1 b2 v2 : List ℕ) (σ : Env) : Prop :=
  σ.arrs "bd1" = b1 ∧ σ.arrs "vd1" = v1 ∧ σ.arrs "bd2" = b2 ∧ σ.arrs "vd2" = v2 ∧
    σ.vars "w_k" = k ∧ σ.vars "g_NT" = N ∧ σ.vars "g_D" = D ∧ σ.vars "g_DD" = D * D

/-- The bounds the test needs. -/
structure CB (B k N D : ℕ) (b1 v1 b2 v2 : List ℕ) : Prop where
  l1 : b1.length = D
  l2 : v1.length = D
  l3 : b2.length = D
  l4 : v2.length = D
  hk : k + 1 < B
  hN : N + 1 < B
  hD : D * D + D + 1 < B
  e1 : ∀ j, b1.getD j 0 + 1 < B
  e2 : ∀ j, v1.getD j 0 + 1 < B
  e3 : ∀ j, b2.getD j 0 + 1 < B
  e4 : ∀ j, v2.getD j 0 + 1 < B

/-- The conflict at the pair of slots `i`. -/
def pC (k N D : ℕ) (b1 v1 b2 v2 : List ℕ) (i : ℕ) : Bool :=
  decide (g b1 (i / D) < k ∧ (N ≤ g v1 (i / D) ∨ (g b2 (i % D) < k ∧
    ((g b1 (i / D) = g b2 (i % D) ∧ g v1 (i / D) ≠ g v2 (i % D)) ∨
      (g b1 (i / D) < g b2 (i % D) ∧ g v2 (i % D) ≤ g v1 (i / D))))))

theorem conflict_iff (k N D : ℕ) (b1 v1 b2 v2 : List ℕ) :
    Conflict k N D b1 v1 b2 v2 ↔ anyUpTo (pC k N D b1 v1 b2 v2) (D * D) = true := by
  rw [anyUpTo_iff]
  simp only [pC, decide_eq_true_eq]
  exact (exists_pair_iff D fun j j2 => g b1 j < k ∧ (N ≤ g v1 j ∨ (g b2 j2 < k ∧
    ((g b1 j = g b2 j2 ∧ g v1 j ≠ g v2 j2) ∨ (g b1 j < g b2 j2 ∧ g v2 j2 ≤ g v1 j))))).symm

/-- The scalars the test assigns. -/
def cfVars : List String := ["g_cf", "g_i", "g_j", "g_j2"]

/-- The cost of the test. -/
def Kcf (D : ℕ) : ℕ := 100 * (D * D) + 20

set_option maxHeartbeats 4000000 in
/-- **The conflict test.** -/
theorem cfCom_spec {k N D : ℕ} {b1 v1 b2 v2 : List ℕ} (hb : CB B k N D b1 v1 b2 v2) :
    Spec B (CA k N D b1 v1 b2 v2) cfCom
      (fun σ σ' => σ'.vars "g_cf" = bn (decide (Conflict k N D b1 v1 b2 v2)) ∧
        Frame cfVars [] σ σ' ∧ σ'.out = σ.out) (Kcf D) := by
  intro σ hσ
  have hDB := hb.hD
  have hCA : ∀ τ τ' (S : List String), (∀ y ∈ S, y ∈ cfVars) → CA k N D b1 v1 b2 v2 τ →
      Frame S [] τ τ' → CA k N D b1 v1 b2 v2 τ' := by
    intro τ τ' S hS ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hf
    have hv : ∀ y, y ∉ cfVars → τ'.vars y = τ.vars y := fun y hy => hf.1 y fun hm => hy (hS y hm)
    exact ⟨by rw [hf.2.1 _ (by simp)]; exact h1, by rw [hf.2.1 _ (by simp)]; exact h2,
      by rw [hf.2.1 _ (by simp)]; exact h3, by rw [hf.2.1 _ (by simp)]; exact h4,
      by rw [hv _ (by simp [cfVars])]; exact h5, by rw [hv _ (by simp [cfVars])]; exact h6,
      by rw [hv _ (by simp [cfVars])]; exact h7, by rw [hv _ (by simp [cfVars])]; exact h8⟩
  have hr1 := RunStep.assign B σ "g_cf" (.lit 0) 0 (RunStep.eval_lit B 0 σ (by omega))
  have hL := flagLoop (B := B) (x := "g_i") (m := "g_DD") (f := "g_cf")
    (S := ["g_cf", "g_j", "g_j2"]) (by simp) (by simp) (N := D * D) (Kb := 90) (by omega)
    (CA k N D b1 v1 b2 v2) (fun τ τ' h hf => hCA τ τ' _ (by simp [cfVars]) h hf)
    (fun τ h => h.2.2.2.2.2.2.2) false (pC k N D b1 v1 b2 v2) (body := .seq splitI cfTest)
    (fun i hi => by
      intro τ ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8⟩, hj⟩
      obtain ⟨hjD, hj2D⟩ := div_mod_lt hi
      have := hb.e1 (i / D); have := hb.e2 (i / D); have := hb.e3 (i % D); have := hb.e4 (i % D)
      have := hb.hk; have := hb.hN
      obtain ⟨τ1, hr1, rfl⟩ := splitI_spec (B := B) (i := i) (D := D) (by omega) (by omega) τ ⟨hj, h7⟩
      obtain ⟨τ', hr, e, fr, o⟩ := cfTest_spec (B := B)
        ((τ.setVar "g_j" (i / D)).setVar "g_j2" (i % D)) (by
          simp only [Env.setVar, String.reduceEq, if_false, if_true]
          rw [h1, h2, h3, h4, hb.l1, hb.l2, hb.l3, hb.l4, h5, h6]
          exact ⟨hjD, hjD, hj2D, hj2D, by omega, by omega, by omega, by omega, by omega, by omega,
            by omega, by omega, by omega⟩)
      refine ⟨τ', (hr1.seq hr).mono (by omega), ?_,
        ((Frame.setVar τ (by simp) _).trans (Frame.setVar _ (by simp) _)).trans
          (fr.mono (by simp) (by simp)), o⟩
      rw [e]
      simp only [Env.setVar, String.reduceEq, if_false, if_true]
      rw [h1, h2, h3, h4, h5, h6]
      by_cases hc : g b1 (i / D) < k ∧ (N ≤ g v1 (i / D) ∨ (g b2 (i % D) < k ∧
          ((g b1 (i / D) = g b2 (i % D) ∧ g v1 (i / D) ≠ g v2 (i % D)) ∨
            (g b1 (i / D) < g b2 (i % D) ∧ g v2 (i % D) ≤ g v1 (i / D)))))
      · have hp : pC k N D b1 v1 b2 v2 i = true := by
          simp only [pC, decide_eq_true_eq]; exact hc
        rw [if_pos (by simp only [g] at hc; omega), if_pos hp]
      · have hp : pC k N D b1 v1 b2 v2 i = false := by
          simp only [pC, decide_eq_false_iff_not]; exact hc
        rw [if_neg (by simp only [g] at hc; omega), if_neg (by rw [hp]; decide)])
  obtain ⟨σ2, hr2, -, hf2, fr2, o2⟩ := hL (σ.setVar "g_cf" 0)
    ⟨hCA _ _ ["g_cf"] (by simp [cfVars]) hσ (Frame.setVar σ (by simp) 0), by simp [Env.setVar]⟩
  refine ⟨σ2, (hr1.seq hr2).mono (by simp [Kcf, Expr.size]; nlinarith), ?_,
    (Frame.setVar σ (by simp [cfVars]) 0).trans (fr2.mono (by simp [cfVars]) (by simp)),
    by rw [o2]; rfl⟩
  rw [hf2]
  have := conflict_iff k N D b1 v1 b2 v2
  by_cases hc : Conflict k N D b1 v1 b2 v2
  · rw [this.mp hc]; simp [hc]
  · have : anyUpTo (pC k N D b1 v1 b2 v2) (D * D) = false := by
      cases h : anyUpTo (pC k N D b1 v1 b2 v2) (D * D)
      · rfl
      · exact absurd (this.mpr h) hc
    rw [this]; simp [hc]

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PConf
