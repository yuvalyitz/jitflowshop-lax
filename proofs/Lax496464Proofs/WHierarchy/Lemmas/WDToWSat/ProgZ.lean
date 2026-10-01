import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgClause

/-!
# One clause, all clauses of an assignment

`clauseCom_spec`: `clauseCom C` writes `clauseWords D x ds C`; `clausesCom_spec`: the clauses of the
CNF in turn.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgZ

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgClause

variable {D : Data} {x : List ℕ} {B : ℕ}

theorem any_filter (p f : Lit → Bool) : ∀ C : List Lit, (C.filter p).any f = C.any fun l => p l && f l
  | [] => rfl
  | l :: C => by
    by_cases hp : p l = true
    · simp [hp, any_filter p f C]
    · simp [hp, any_filter p f C]

theorem sum_filter_le (p : Lit → Bool) (f : Lit → ℕ) : ∀ C : List Lit,
    ((C.filter p).map f).sum ≤ (C.map f).sum
  | [] => le_rfl
  | l :: C => by
    have := sum_filter_le p f C
    by_cases hp : p l = true
    · simp [hp]; omega
    · simp [hp]; omega

theorem writeTaut0_spec (h2 : 2 < B) :
    Spec B (fun _ => True) writeTaut0
      (fun σ σ' => σ'.out = σ.out ++ [2, 0, 1] ∧ Frame zS [] σ σ') 6 := by
  unfold writeTaut0
  run_vcg
  exact ⟨by simp, Frame.refl _ _ _⟩

theorem writeLit_spec {n : ℕ} (hn : n < B) :
    Spec B (fun _ => True) (.write (.lit n))
      (fun σ σ' => σ'.out = σ.out ++ [n] ∧ Frame zS [] σ σ') 2 := by
  run_vcg
  exact ⟨rfl, Frame.refl _ _ _⟩

/-- The cost bound of a clause. -/
def KC (x : List ℕ) (C : List Lit) : ℕ :=
  (C.map (Klit x)).sum + (C.map fun l => 7 * l.atom.idxs.length + 8).sum + 30

set_option maxHeartbeats 1000000 in
/-- **One clause.** -/
theorem clauseCom_spec (hB : BF D x B) (hg : Good x) {ds : List ℕ} (hds : DsOk D x ds)
    (C : List Lit) (hC : ∀ l ∈ C, LitOk D x l) (hnx : (C.filter isXLit).length < B) :
    Spec B (ZPre D x ds) (clauseCom C)
      (fun σ σ' => σ'.out = σ.out ++ clauseWords D x ds C ∧ Frame zS [] σ σ') (KC x C) := by
  intro σ hσ
  have hlen := hB.len
  -- `st := 0`
  have hr1 := RunStep.assign B σ "w_st" (.lit 0) 0 (RunStep.eval_lit B 0 σ (by omega))
  have f1 : Frame zS [] σ (σ.setVar "w_st" 0) := Frame.setVar σ (by simp [zS]) 0
  -- the literals without `X`
  obtain ⟨σ2, hr2, e2, f2, o2⟩ := nonXs_spec hB hg hds (C.filter fun l => !isXLit l)
    (fun l hl => by
      obtain ⟨hlC, hX⟩ := List.mem_filter.mp hl
      exact ⟨hC l hlC, by simpa using hX⟩) _ (hσ.frame f1 (by simp [zS]))
  have hsat : (C.filter fun l => !isXLit l).any (nonXVal x (epsW D x ds)) = satNonX D x ds C := by
    rw [any_filter]; rfl
  rw [hsat] at e2
  have hst : σ2.vars "w_st" = if satNonX D x ds C then 1 else 0 := by
    rw [e2]; simp [Env.setVar]
  have hZ2 : ZPre D x ds σ2 := (hσ.frame f1 (by simp [zS])).frame f2 (by simp [zS])
  have hstB : σ2.vars "w_st" < B := by rw [hst]; split_ifs <;> omega
  have hc1 : (Expr.var "w_st").evalB B σ2 = some (σ2.vars "w_st") := RunStep.eval_var B σ2 _ hstB
  have hc2 : (Expr.lit 1).evalB B σ2 = some 1 := RunStep.eval_lit B 1 σ2 (by omega)
  have hK1 := sum_filter_le (fun l => !isXLit l) (Klit x) C
  have hK2 := sum_filter_le isXLit (fun l => 7 * l.atom.idxs.length + 8) C
  by_cases hs : satNonX D x ds C = true
  · rw [if_pos hs] at hst
    obtain ⟨σ3, hr3, o3, f3⟩ := writeTaut0_spec (B := B) (by omega) σ2 trivial
    refine ⟨σ3, (hr1.seq (hr2.seq (RunStep.ite_true B _ _ _ σ2 σ3 6
      (RunStep.cond_eq_true B σ2 _ _ _ _ hc1 hc2 hst) hr3))).mono (by simp only [KC, Expr.size, Cond.size]; omega), ?_,
      (f1.trans f2).trans f3⟩
    rw [o3, o2]; simp [clauseWords, hs, Env.setVar]
  · rw [if_neg hs] at hst
    obtain ⟨σ3, hr3, o3, f3⟩ := writeLit_spec (B := B) hnx σ2 trivial
    obtain ⟨σ4, hr4, o4, f4⟩ := xLits_spec hB hds (C.filter isXLit)
      (fun l hl => ⟨hC l (List.mem_filter.mp hl).1, (List.mem_filter.mp hl).2⟩) σ3
      (hZ2.frame f3 (by simp [zS]))
    refine ⟨σ4, (hr1.seq (hr2.seq (RunStep.ite_false B _ _ _ σ2 σ4 _
      (RunStep.cond_eq_false B σ2 _ _ _ _ hc1 hc2 (by rw [hst]; omega))
      (hr3.seq hr4)))).mono (by simp only [KC, Expr.size, Cond.size]; omega), ?_, ((f1.trans f2).trans f3).trans f4⟩
    rw [o4, o3, o2]; simp [clauseWords, hs, Env.setVar]

/-- The cost bound of the clauses. -/
def Kcls (x : List ℕ) (Cs : List (List Lit)) : ℕ := (Cs.map (KC x)).sum + 1

/-- **The clauses.** -/
theorem clausesCom_spec (hB : BF D x B) (hg : Good x) {ds : List ℕ} (hds : DsOk D x ds) :
    ∀ Cs : List (List Lit), (∀ C ∈ Cs, (∀ l ∈ C, LitOk D x l) ∧ (C.filter isXLit).length < B) →
    Spec B (ZPre D x ds) (seqList (Cs.map clauseCom))
      (fun σ σ' => σ'.out = σ.out ++ Cs.flatMap (clauseWords D x ds) ∧ Frame zS [] σ σ')
      (Kcls x Cs)
  | [], _ => by
    refine Spec.mono ((Spec.skip (B := B) (P := ZPre D x ds)).post fun σ σ' _ h => ?_)
      (by simp [Kcls])
    subst h; exact ⟨by simp, Frame.refl _ _ _⟩
  | C :: Cs, h => by
    have h1 := clauseCom_spec hB hg hds C (h C (by simp)).1 (h C (by simp)).2
    have h2 := clausesCom_spec hB hg hds Cs fun C' hC' => h C' (by simp [hC'])
    refine Spec.mono (Spec.seq h1 h2 (fun σ σ' hp hq => hp.frame hq.2 (by simp [zS])) ?_)
      (by simp [Kcls]; omega)
    rintro σ σ' σ'' - ⟨o1, f1⟩ ⟨o2, f2⟩
    exact ⟨by rw [o2, o1]; simp, f1.trans f2⟩

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgZ
