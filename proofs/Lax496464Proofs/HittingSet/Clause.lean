import Lax496464Proofs.HittingSet.Sweep
import Lax496464Proofs.HittingSet.Model

/-!
# The Clause Sets

For each clause: mark the elements of its literals and count them, write the count, then
sweep the marks writing the marked elements in increasing order.
-/

namespace Lax496464Proofs.HittingSet.Clause

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax429075.CNF Lax391470Proofs.L2ScanModel Lax391470Proofs.Bits Lax496464.HittingSetFromSat
open Lax496464Proofs.HittingSet.Emit Lax496464Proofs.HittingSet.Front Lax496464Proofs.HittingSet.Arrays Lax496464Proofs.HittingSet.Mark
open Lax496464Proofs.HittingSet.Sweep Lax496464Proofs.HittingSet.Model Lax496464Proofs.HittingSet.Correct

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))

def clauseBody : Com :=
  .seq (.assign "cnt" (.lit 0))
    (.seq markLoop (.seq (setNat (V "cnt")) (.seq sweepLoop (bump "c"))))

def clauseLoop : Com := .seq (.assign "c" (.lit 0)) (.while (.lt (V "c") (V "C")) clauseBody)

variable {B : ℕ}

/-- The output of the first `c` clauses. -/
def clausesUpTo (F : Formula) (c : ℕ) : List ℕ :=
  (List.range c).flatMap fun c => setBits (memb F (vars F + c))

theorem clausesUpTo_succ (F : Formula) (c : ℕ) :
    clausesUpTo F (c + 1) = clausesUpTo F c ++ setBits (memb F (vars F + c)) := by
  simp [clausesUpTo, List.range_succ]

theorem clausesUpTo_length (F : Formula) : clausesUpTo F F.length = clausesOut F := rfl

/-- The fixed data of the clause loop. -/
structure CData (F : Formula) (vr sg cl : List ℕ) (L Lm S B : ℕ) : Prop where
  post : Post F vr sg cl
  hvr : (lits F).length ≤ vr.length
  hsg : (lits F).length ≤ sg.length
  hcl : (lits F).length ≤ cl.length
  hkL : (lits F).length ≤ L
  hnL : 2 * vars F ≤ Lm
  hn2 : 2 * vars F ≤ 2 * L + 4
  hLB : Lm + 4 < B
  hLL : L + 2 < B
  hCB : F.length < B
  hS : (2 * vars F).size ≤ S

theorem elemAt_lt {F : Formula} {vr sg cl : List ℕ} (P : Post F vr sg cl) {q : ℕ}
    (hq : q < (lits F).length) : elemAt vr sg q < 2 * vars F := by
  rw [elemAt_eq P hq]
  have hmem : (lits F).getD q dflt ∈ lits F := by
    rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq
  obtain ⟨C, hC, hl⟩ := List.mem_flatMap.mp hmem
  exact elem_lt hC hl

theorem data_of {F : Formula} {vr sg cl : List ℕ} {L Lm S : ℕ}
    (D : CData F vr sg cl L Lm S B) :
    Data (lits F).length (2 * vars F) Lm vr sg cl B where
  hvr := D.hvr
  hsg := D.hsg
  hcl := D.hcl
  hel := fun q hq => elemAt_lt D.post hq
  hbvr := fun q hq => by
    rw [D.post.hvr q hq]
    have hmem : (lits F).getD q dflt ∈ lits F := by
      rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem hq
    obtain ⟨C, hC, hl⟩ := List.mem_flatMap.mp hmem
    have := index_lt_bound hC hl
    have := bound_le_vars F
    have := D.hnL; have := D.hLB
    omega
  hbsg := fun q hq => by rw [D.post.hsg q hq]; split_ifs <;> omega
  hbcl := fun q hq => by
    rw [D.post.hcl q hq]
    have hq' : q < (cn F).length := by rw [cn_length]; exact hq
    rw [List.getD_eq_getElem _ _ hq']
    have := mem_cn_lt F (List.getElem_mem hq')
    have := D.hCB
    omega
  hnL := D.hnL
  hLB := by have := D.hLB; omega
  hkB := by have := D.hkL; have := D.hLL; omega

/-- The invariant of the clause loop, relative to the entry state `σ0`. -/
structure CInv (F : Formula) (vr sg cl : List ℕ) (Lm : ℕ) (σ0 σ : Env) : Prop where
  hC : σ.vars "C" = F.length
  hc : σ.vars "c" ≤ F.length
  hk : σ.vars "k" = (lits F).length
  hn : σ.vars "nn" = 2 * vars F
  hvr : σ.arrs "vr" = vr
  hsg : σ.arrs "sg" = sg
  hcl : σ.arrs "cl" = cl
  hmark : σ.arrs "mark" = List.replicate Lm 0
  hout : σ.out = σ0.out ++ clausesUpTo F (σ.vars "c")
  kvars : ∀ v, v ∉ "c" :: "cnt" :: "p" :: "e" :: SN → σ.vars v = σ0.vars v
  karrs : ∀ a, a ≠ "mark" → σ.arrs a = σ0.arrs a
  kinp : σ.inp = σ0.inp

/-- The cost of one clause, in terms of the length `L` of the word. -/
def Kclause (S L : ℕ) : ℕ :=
  2 + ((Kmark + 4) * L + 6) + (48 * S + 42) + ((Ksweep S + 4) * (2 * L + 4) + 6) + 4

/-- The count and the members, from the marks of a clause. -/
theorem cntOf_eq {F : Formula} {vr sg cl : List ℕ} (P : Post F vr sg cl) {c : ℕ}
    (hc : c < F.length) :
    cntOf (2 * vars F) (elemsUpTo vr sg cl c (lits F).length) = (memb F (vars F + c)).length := by
  unfold cntOf
  rw [memb_clause F hc]
  congr 1
  exact List.filter_congr fun x _ => by
    rw [decide_eq_decide]; exact mem_elemsUpTo_iff P hc x

theorem filter_eq_memb {F : Formula} {vr sg cl : List ℕ} (P : Post F vr sg cl) {c : ℕ}
    (hc : c < F.length) :
    ((List.range (2 * vars F)).filter fun x =>
      decide (x ∈ elemsUpTo vr sg cl c (lits F).length)) = memb F (vars F + c) := by
  rw [memb_clause F hc]
  exact List.filter_congr fun x _ => by
    rw [decide_eq_decide]; exact mem_elemsUpTo_iff P hc x

theorem clauseBody_spec (F : Formula) (vr sg cl : List ℕ) (L Lm S : ℕ) (σ0 : Env)
    (D : CData F vr sg cl L Lm S B) :
    Spec B (fun σ => CInv F vr sg cl Lm σ0 σ ∧ σ.vars "c" < F.length) clauseBody
      (fun σ σ' => CInv F vr sg cl Lm σ0 σ' ∧ σ'.vars "c" = σ.vars "c" + 1) (Kclause S L) := by
  intro σ ⟨I, hlt⟩
  obtain ⟨c, hcd⟩ : ∃ c, σ.vars "c" = c := ⟨_, rfl⟩
  rw [hcd] at hlt
  have hCB := D.hCB
  have hLB := D.hLB
  have hLL := D.hLL
  have hkL := D.hkL
  have hnL := D.hnL
  have hn2 := D.hn2
  obtain ⟨k, hkd⟩ : ∃ k, (lits F).length = k := ⟨_, rfl⟩
  obtain ⟨n, hnd⟩ : ∃ n, 2 * vars F = n := ⟨_, rfl⟩
  have Dm := data_of D
  rw [hkd, hnd] at Dm
  -- cnt := 0
  have r1 : Run B (.assign "cnt" (.lit 0)) σ (σ.setVar "cnt" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp [Expr.size])
  obtain ⟨σ1, hσ1⟩ : ∃ σ1, σ.setVar "cnt" 0 = σ1 := ⟨_, rfl⟩
  rw [hσ1] at r1
  have v1 : ∀ v, v ≠ "cnt" → σ1.vars v = σ.vars v := fun v h => by rw [← hσ1]; simp [Env.setVar, h]
  have a1 : σ1.arrs = σ.arrs := by rw [← hσ1]; rfl
  have o1 : σ1.out = σ.out := by rw [← hσ1]; rfl
  have i1 : σ1.inp = σ.inp := by rw [← hσ1]; rfl
  have cnt1 : σ1.vars "cnt" = 0 := by rw [← hσ1]; simp [Env.setVar]
  -- the marks
  obtain ⟨σ2, r2, M, p2⟩ := markLoop_spec (B := B) k n Lm c vr sg cl σ1 Dm (by omega) σ1
    ⟨by simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [v1 _ (by decide), I.hk, hkd],
     by simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [v1 _ (by decide), hcd],
     by simp [Env.setVar],
     by simp only [Env.setVar]; rw [a1, I.hvr],
     by simp only [Env.setVar]; rw [a1, I.hsg],
     by simp only [Env.setVar]; rw [a1, I.hcl],
     by simp only [Env.setVar]; rw [a1, I.hmark]; simp,
     fun e he => by
       simp only [Env.setVar, ↓reduceIte]
       rw [a1, I.hmark, elemsUpTo_zero]
       simp [List.getD_eq_getElem?_getD, he],
     by simp only [Env.setVar, String.reduceEq, ↓reduceIte]; rw [cnt1, elemsUpTo_zero, cntOf_zero],
     fun v hv => by
       have h1 : v ≠ "p" := fun h => hv (by rw [h]; simp)
       simp [Env.setVar, h1],
     fun a _ => rfl, rfl, rfl⟩
  have kvars2 : ∀ v, v ∉ ["p", "e", "cnt"] → σ2.vars v = σ.vars v := fun v hv => by
    rw [M.kvars v hv, v1 v (fun h => hv (h ▸ by simp))]
  have cnt2 : σ2.vars "cnt" = (memb F (vars F + c)).length := by
    rw [M.hcnt, p2, ← hkd, ← hnd, cntOf_eq D.post hlt]
  have hmemb_le : (memb F (vars F + c)).length ≤ n := by
    rw [← hnd]; unfold memb; exact le_trans (List.length_filter_le _ _) (by simp)
  -- the count
  obtain ⟨σ3, r3, o3, k3⟩ := setNat_emits (B := B) (V "cnt") (fun σ => σ.vars "cnt") S
    (fun σ => σ.vars "cnt" = (memb F (vars F + c)).length)
    (fun σ h => evalB_var_eq rfl (by rw [h]; omega))
    (fun σ h => ⟨by rw [h]; omega, by
      rw [h]; exact le_trans (Nat.size_le_size hmemb_le) (by rw [← hnd]; exact D.hS)⟩) σ2 cnt2
  have a3 : σ3.arrs = σ2.arrs := k3.2.1
  -- the sweep
  have hE : ∀ x ∈ elemsUpTo vr sg cl c k, x < n := fun x hx => mem_elemsUpTo_lt Dm le_rfl hx
  obtain ⟨σ4, r4, o4, m4, v4, a4, i4⟩ := sweepLoop_run (B := B) n Lm S (elemsUpTo vr sg cl c k) σ3
    hE (by omega) (by omega) (by omega) (by rw [← hnd]; exact D.hS)
    (by rw [k3.var (by simp [SN]), kvars2 _ (by decide), I.hn, hnd])
    (by rw [a3]; exact M.hlen)
    (fun e' he' => by rw [a3, M.hmark e' he', p2])
  -- c := c + 1
  have c4 : σ4.vars "c" = c := by
    rw [v4 _ (by simp [SN]), k3.var (by simp [SN]), kvars2 _ (by decide), hcd]
  have r5 : Run B (bump "c") σ4 (σ4.setVar "c" (c + 1)) 4 := by
    have := Run.assign (B := B) (σ := σ4) (x := "c") (e := .bin .add (V "c") (.lit 1))
      (RunStep.eval_add B σ4 (V "c") (.lit 1) c 1 (by rw [← c4]; exact evalB_var (by rw [c4]; omega))
        (evalB_lit (by omega)) (by omega))
    simpa [Expr.size] using this
  refine ⟨_, (r1.seq (r2.seq (r3.seq (r4.seq r5)))).mono ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, by simp [Env.setVar, hcd]⟩
  · unfold Kclause
    have h1 : (Kmark + 4) * k ≤ (Kmark + 4) * L := Nat.mul_le_mul_left _ (by omega)
    have h2 : (Ksweep S + 4) * n ≤ (Ksweep S + 4) * (2 * L + 4) := Nat.mul_le_mul_left _ (by omega)
    simp only [Expr.size]
    omega
  all_goals simp only [Env.setVar, String.reduceEq, ↓reduceIte]
  · rw [v4 _ (by simp [SN]), k3.var (by simp [SN]), kvars2 _ (by decide), I.hC]
  · omega
  · rw [v4 _ (by simp [SN]), k3.var (by simp [SN]), kvars2 _ (by decide), I.hk]
  · rw [v4 _ (by simp [SN]), k3.var (by simp [SN]), kvars2 _ (by decide), I.hn]
  · rw [a4 _ (by decide), a3, M.karrs _ (by decide), a1, I.hvr]
  · rw [a4 _ (by decide), a3, M.karrs _ (by decide), a1, I.hsg]
  · rw [a4 _ (by decide), a3, M.karrs _ (by decide), a1, I.hcl]
  · exact m4
  · have hfm := filter_eq_memb D.post hlt
    rw [hkd] at hfm
    rw [o4, o3, M.kout, o1, I.hout, hcd, clausesUpTo_succ, setBits, ← cnt2, ← hnd, hfm]
    beta_reduce
    simp only [List.append_assoc]
  · intro v hv
    have h1 : v ≠ "c" := fun h => hv (h ▸ by simp)
    rw [if_neg h1, v4 v (fun h => hv (by simp at h ⊢; tauto)),
      k3.var (fun h => hv (by simp [SN] at h ⊢; tauto)),
      kvars2 v (fun h => hv (by simp at h ⊢; tauto))]
    exact I.kvars v hv
  · intro a ha; rw [a4 a ha, a3, M.karrs a ha, a1]; exact I.karrs a ha
  · rw [i4, k3.2.2, M.kinp, i1]; exact I.kinp

theorem clauseLoop_spec (F : Formula) (vr sg cl : List ℕ) (L Lm S : ℕ) (σ0 : Env)
    (D : CData F vr sg cl L Lm S B) :
    Spec B (fun σ => CInv F vr sg cl Lm σ0 (σ.setVar "c" 0)) clauseLoop
      (fun _ σ' => CInv F vr sg cl Lm σ0 σ' ∧ σ'.vars "c" = F.length)
      ((Kclause S L + 4) * F.length + 6) :=
  Spec.forRangeZero "c" "C" (CInv F vr sg cl Lm σ0) F.length (Kclause S L) D.hCB
    (fun _ h => h.hc) (fun _ h => h.hC) (clauseBody_spec F vr sg cl L Lm S σ0 D)

/-- **The clause loop**, from a state holding the arrays, the dimensions and clear marks. -/
theorem clauseLoop_run (F : Formula) (vr sg cl : List ℕ) (L Lm S : ℕ) (σ : Env)
    (D : CData F vr sg cl L Lm S B)
    (hC : σ.vars "C" = F.length) (hk : σ.vars "k" = (lits F).length)
    (hn : σ.vars "nn" = 2 * vars F) (hvr : σ.arrs "vr" = vr) (hsg : σ.arrs "sg" = sg)
    (hcl : σ.arrs "cl" = cl) (hmark : σ.arrs "mark" = List.replicate Lm 0) :
    ∃ σ', Run B clauseLoop σ σ' ((Kclause S L + 4) * F.length + 6) ∧
      σ'.out = σ.out ++ clausesOut F ∧ σ'.inp = σ.inp := by
  obtain ⟨σ', r, I, hc⟩ := clauseLoop_spec (B := B) F vr sg cl L Lm S σ D σ
    ⟨by simp [Env.setVar, hC], by simp, by simp [Env.setVar, hk], by simp [Env.setVar, hn],
     by simp [Env.setVar, hvr], by simp [Env.setVar, hsg], by simp [Env.setVar, hcl],
     by simp [Env.setVar, hmark], by simp [Env.setVar, clausesUpTo],
     fun v hv => by
       have h1 : v ≠ "c" := fun h => hv (by rw [h]; simp)
       simp [Env.setVar, h1],
     fun a _ => rfl, rfl⟩
  exact ⟨σ', r, by rw [I.hout, hc, clausesUpTo_length], I.kinp⟩

end Lax496464Proofs.HittingSet.Clause
