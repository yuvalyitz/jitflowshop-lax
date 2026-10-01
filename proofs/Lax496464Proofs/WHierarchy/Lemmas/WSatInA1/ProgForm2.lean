import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm

/-! # Phase 10: the code of the sentence, assembled

`clauseOut_spec`: the conjunct of one clause; `formOut_spec`: phase 10 writes the whole code of the
sentence (`FormEnc.encode_phi`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm2

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Formula
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.FormEnc
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm

variable {d k B : ℕ}

/-- The cost of the conjunct of one map. -/
def Kcl (d k : ℕ) : ℕ :=
  (3 * 5 + 1) + ((2 + ((20 + 4) * (d + 1) + 6)) + ((3 * 3 + 1) + (4 + ((2 + ((20 + 4) * (d + 1) + 6)) +
    (((20 + 4) * (k + 1) + 6) + ((Kyin k + 30 + 4) * (k + 1) + 6 + 10))))))

theorem clauseOut_spec (hF : FB d k B) :
    Spec B (TC d k) (clauseOut d)
      (fun σ σ' => TC d k σ' ∧ σ'.vars "w_t" = σ.vars "w_t" ∧
        σ'.out = σ.out ++ clW d k (σ.vars "w_t")) (Kcl d k) := by
  have h2 := hF.small
  intro σ hT
  obtain ⟨σ1, r1, rfl⟩ := writeLits_spec (B := B) [5, 3, 0, 2, d + 1] (by simp; omega) σ trivial
  obtain ⟨σ2, r2, hT2, ht2, ho2⟩ := vtOut_spec hF { σ with out := σ.out ++ [5, 3, 0, 2, d + 1] } hT
  obtain ⟨σ3, r3, rfl⟩ := writeLits_spec (B := B) [4, 0, 3] (by simp; omega) σ2 trivial
  have hk3 : σ2.vars "w_k" = k := hT2.1.1
  have e4 : (Expr.add (V "w_k") (.lit (d + 2))).evalB B { σ2 with out := σ2.out ++ [4, 0, 3] } =
      some (k + (d + 2)) := by
    rw [← hk3]; exact evalB_bin (evalB_var (by simp; omega)) (evalB_lit (by omega)) (by simp; omega)
  have r4 := Run.write e4
  obtain ⟨σ5, r5, hT5, ht5, ho5⟩ := vtOut_spec hF
    { σ2 with out := σ2.out ++ [4, 0, 3] ++ [k + (d + 2)] } hT2
  obtain ⟨σ6, r6, hT6, ht6, ho6⟩ := ytOut_spec hF _ hT5
  obtain ⟨σ7, r7, hT7, ht7, ho7⟩ := yOut_spec hF _ hT6
  refine ⟨σ7, r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq r7))))), hT7, ?_, ?_⟩
  · rw [ht7, ht6, ht5]; exact ht2
  · have e2 : σ2.vars "w_t" = σ.vars "w_t" := ht2
    have e5 : σ5.vars "w_t" = σ.vars "w_t" := by rw [ht5]; exact e2
    rw [ho7, ho6, ht6, e5, ho5]
    simp only at ho2 ⊢
    rw [ho2, e2, clW]
    simp

theorem eBody_spec (hF : FB d k B) (out0 : List ℕ) :
    Spec B (fun σ => (FC d k σ ∧ σ.vars "w_t" ≤ FF d k ∧
        σ.out = out0 ++ (List.range (σ.vars "w_t")).flatMap fun t => 4 :: clW d k t) ∧
        σ.vars "w_t" < FF d k)
      (.seq (.write (.lit 4)) (.seq (clauseOut d) (bump "w_t")))
      (fun σ σ' => (FC d k σ' ∧ σ'.vars "w_t" ≤ FF d k ∧
        σ'.out = out0 ++ (List.range (σ'.vars "w_t")).flatMap fun t => 4 :: clW d k t) ∧
        σ'.vars "w_t" = σ.vars "w_t" + 1) (2 + (Kcl d k + 4)) := by
  have h2 := hF.small
  have h1 := hF.nv
  have hFn := FF_le_nv d k
  rintro σ ⟨⟨hC, -, ho⟩, ht⟩
  have r1 : Run B (.write (.lit 4)) σ { σ with out := σ.out ++ [4] } 2 :=
    Run.write (evalB_lit (by omega))
  obtain ⟨σ2, r2, hT2, ht2, ho2⟩ := clauseOut_spec hF _
    (show TC d k { σ with out := σ.out ++ [4] } from ⟨hC, ht⟩)
  have e3 : (Expr.add (V "w_t") (.lit 1)).evalB B σ2 = some (σ.vars "w_t" + 1) := by
    have : σ2.vars "w_t" = σ.vars "w_t" := ht2
    rw [← this]; exact evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega)
  have r3 : Run B (bump "w_t") σ2 (σ2.setVar "w_t" (σ.vars "w_t" + 1)) 4 := Run.assign e3
  refine ⟨_, r1.seq (r2.seq r3), ⟨⟨FC_set hT2.1 (by decide) _, by simp [Env.setVar]; omega, ?_⟩,
    by simp [Env.setVar]⟩⟩
  have e2 : σ2.vars "w_t" = σ.vars "w_t" := ht2
  simp only [Env.setVar] at ho2 ⊢
  rw [ho2, ho, e2]
  simp [List.range_succ]

def KeOut (d k : ℕ) : ℕ := ((2 + (Kcl d k + 4)) + 4) * FF d k + 6 + 10

theorem eOut_spec (hF : FB d k B) :
    Spec B (FC d k) (eOut d) (fun σ σ' => FC d k σ' ∧ σ'.out = σ.out ++ eW d k) (KeOut d k) := by
  have h1 := hF.nv
  have h2 := hF.small
  have hFn := FF_le_nv d k
  intro σ hC
  obtain ⟨σ1, r1, hC1, ho1⟩ := wloop (B := B) "w_t" "w_F" (FF d k) (FC d k)
    (fun t => 4 :: clW d k t) σ.out (Kb := 2 + (Kcl d k + 4)) (by omega) (fun σ h => h.2.2.1)
    (eBody_spec hF σ.out) σ ⟨FC_set hC (by decide) 0, rfl⟩
  obtain ⟨σ2, r2, rfl⟩ := writeLits_spec (B := B) [2, 0, 0] (by simp; omega) σ1 trivial
  refine ⟨_, (r1.seq r2).mono (by unfold KeOut; simp), hC1, ?_⟩
  simp only [ho1, eW, List.append_assoc]

def KformOut (d k : ℕ) : ℕ :=
  ((10 + 4) * nv d k + 6) + (13 + (2 + (4 + (((25 + 4) * k + 6) + (13 + ((((34 * k + 6 + 8) + 4) * k
    + 6) + (10 + KeOut d k)))))))

theorem formOut_spec (hF : FB d k B) :
    Spec B (FC d k) (formOut d)
      (fun σ σ' => σ'.out = σ.out ++ (phi d k).encode) (KformOut d k) := by
  have h2 := hF.small
  intro σ hC
  obtain ⟨σ1, r1, hC1, ho1⟩ := qOut_spec hF σ.out σ ⟨hC, rfl⟩
  obtain ⟨σ2, r2, rfl⟩ := writeLits_spec (B := B) [4, 0, 0, 1] (by simp; omega) σ1 trivial
  have e3 : (V "w_k").evalB B { σ1 with out := σ1.out ++ [4, 0, 0, 1] } = some k := by
    rw [← hC1.1]; exact evalB_var (by simp; rw [hC1.1]; omega)
  have r3 := Run.write e3
  obtain ⟨σ4, r4, rfl⟩ := writeLits_spec (B := B) [4] (by simp; omega)
    { σ1 with out := σ1.out ++ [4, 0, 0, 1] ++ [k] } trivial
  obtain ⟨σ5, r5, hC5, ho5⟩ := cOut_spec hF _
    { σ1 with out := σ1.out ++ [4, 0, 0, 1] ++ [k] ++ [4] } ⟨hC1, rfl⟩
  obtain ⟨σ6, r6, rfl⟩ := writeLits_spec (B := B) [2, 0, 0, 4] (by simp; omega) σ5 trivial
  obtain ⟨σ7, r7, hC7, ho7⟩ := dOut_spec hF _ { σ5 with out := σ5.out ++ [2, 0, 0, 4] } ⟨hC5, rfl⟩
  obtain ⟨σ8, r8, rfl⟩ := writeLits_spec (B := B) [2, 0, 0] (by simp; omega) σ7 trivial
  obtain ⟨σ9, r9, -, ho9⟩ := eOut_spec hF { σ7 with out := σ7.out ++ [2, 0, 0] } hC7
  refine ⟨σ9, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq r9)))))))).mono
    (by unfold KformOut; simp), ?_⟩
  show σ9.out = σ.out ++ (phi d k).encode
  simp only at ho9 ho7 ho5
  rw [ho9, ho7, ho5, ho1, encode_phi]
  simp

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgForm2
