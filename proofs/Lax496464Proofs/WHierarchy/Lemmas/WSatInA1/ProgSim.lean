import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgPick

/-! # Phase 7c: one search, over all clauses

`c2Loop_spec`: one search walks all clauses in order, keeping the chosen elements, and ends with the
state of `Search.sim` (`stN_all`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgSim

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgNRows
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgHit Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgPick

variable {cl : List (List ℕ)} {d k B : ℕ}

/-- The scalars a step of the search may change. -/
def grpVars : List String :=
  ["w_o", "w_ln", "w_hit", "w_i", "w_f", "w_q", "w_ok", "w_dg", "w_nch", "w_pw"]

theorem wvars_c2Step (d : ℕ) : ∀ y, y ∉ grpVars → y ∉ (c2Step d).wvars := by
  intro y hy
  simp only [grpVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp [c2Step, c2Grp, grpCom, grpHead, grpTail, hitLoop, hitLit, chLoop, pick, Com.wvars, hy.1,
    hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1, hy.2.2.2.2.2.2.1,
    hy.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.2]

theorem warrs_c2Step (d : ℕ) : ∀ a, a ≠ "ch" → a ∉ (c2Step d).warrs := by
  intro a ha
  simp [c2Step, c2Grp, grpCom, grpHead, grpTail, hitLoop, hitLit, chLoop, pick, Com.warrs, ha]

/-- The context of the steps of a search. -/
def C2P (cl : List (List ℕ)) (d k c b N : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧ (σ.arrs "ch").length = k + 1 ∧
    σ.arrs "hs_mem" = hsS cl d k N ∧ 2 * nL cl + cl.length ≤ N ∧ N ≤ sz cl d k ∧
    σ.vars "w_c" = c ∧ σ.vars "w_b" = b ∧ σ.vars "w_key" = nNum cl d c ∧ c < cl.length ∧
    b < d ^ k

/-- The state of the search after the clauses below `n`. -/
def stN (cl : List (List ℕ)) (d k c b n : ℕ) : Option (List ℕ) :=
  (List.range n).foldl (simStep cl d k c (bdig d b)) (some [])

theorem stN_succ (c b n : ℕ) :
    stN cl d k c b (n + 1) = simStep cl d k c (bdig d b) (stN cl d k c b n) n := by
  simp [stN, List.range_succ, List.foldl_append]

theorem stN_all (c b : ℕ) : stN cl d k c b cl.length = sim cl d k c b := rfl

theorem simStep_none (c b n : ℕ) : simStep cl d k c (bdig d b) none n = none := rfl

theorem hs_nNum {N c2 : ℕ} (hN : 2 * nL cl + cl.length ≤ N) (hNs : N ≤ sz cl d k)
    (hc2 : c2 < cl.length) : (hsS cl d k N).getD (2 * nL cl + c2) 0 = nNum cl d c2 := by
  unfold hsS
  rw [List.getD_append _ _ _ _ (by rw [List.length_take, length_hs]; omega),
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega), ← List.getD_eq_getElem?_getD]
  exact hs_n cl d k hc2

/-! ### A step at a clause -/

set_option maxHeartbeats 4000000 in
theorem c2Grp_value (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) {c b N : ℕ} :
    Spec B (fun σ => C2P cl d k c b N σ ∧ σ.vars "w_c2" < cl.length ∧
        SRel cl d k σ (some (chOf σ))) (c2Grp d)
      (fun σ σ' => SRel cl d k σ' (simStep cl d k c (bdig d b) (some (chOf σ)) (σ.vars "w_c2")) ∧
        (σ'.arrs "ch").length = k + 1) (Kgrp d k + 20) := by
  rintro σ ⟨⟨hc, hf, hchl, hh, hN1, hN2, hcv, hbv, hkey, hcm, hbk⟩, hc2, hR⟩
  have hl := hB.hl
  have hszB := hB.cb.sz
  have hL := hc.hL
  set c2 := σ.vars "w_c2" with hc2def
  have hv : (σ.arrs "hs_mem").getD (2 * σ.vars "w_L" + c2) 0 = nNum cl d c2 := by
    rw [hh, hL]; exact hs_nNum hN1 hN2 hc2
  have hcond : (Cond.eq (.get "hs_mem" (.add (.mul (.lit 2) (V "w_L")) (V "w_c2"))) (V "w_key")).evalB
      B σ = some (nNum cl d c2 == nNum cl d c) := by
    rw [← hkey]
    refine evalB_condEq (evalB_get (k := 2 * σ.vars "w_L" + c2)
      (evalB_bin (evalB_bin (evalB_lit (by omega)) (evalB_var (by omega)) (by simp; omega))
        (evalB_var (by omega)) (by simp; omega)) ?_ ?_) (evalB_var ?_)
    · rw [← hv, List.getElem?_eq_getElem (by rw [hh, length_hsS]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hh, length_hsS]; omega : 2 * σ.vars "w_L" + c2 < (σ.arrs "hs_mem").length)]
    · exact nNum_lt hB _
    · rw [hkey]; exact nNum_lt hB _
  by_cases hk : key cl d c2 = key cl d c
  · have hGP : GP cl d k σ := ⟨hc, hf, hchl, hc2, by rw [hbv]; exact hbk, hR⟩
    obtain ⟨σ', r, hR', hl'⟩ := grpCom_value hB hd σ hGP
    have ht : (nNum cl d c2 == nNum cl d c) = true := by simp [(nNum_eq_iff cl d).mpr hk]
    refine ⟨σ', (Run.ite_true (by rw [hcond, ht]) r).mono (by simp; omega), ?_, hl'⟩
    have e : simStep cl d k c (bdig d b) (some (chOf σ)) c2 =
        grpR cl d k (chOf σ) (σ.vars "w_b") c2 := by
      rw [simStep_some, hbv]; simp only [grpR, hk, true_and]
    rw [e]; exact hR'
  · have hf' : (nNum cl d c2 == nNum cl d c) = false := by
      simpa using fun h => hk ((nNum_eq_iff cl d).mp h)
    refine ⟨σ, (Run.ite_false (by rw [hcond, hf']) Run.skip).mono (by simp), ?_, hchl⟩
    have e : simStep cl d k c (bdig d b) (some (chOf σ)) c2 = some (chOf σ) := by
      rw [simStep_some, if_neg (fun h => hk h.1)]
    rw [e]; exact hR

theorem c2Step_value (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) {c b N : ℕ}
    (st : Option (List ℕ)) :
    Spec B (fun σ => C2P cl d k c b N σ ∧ σ.vars "w_c2" < cl.length ∧ SRel cl d k σ st) (c2Step d)
      (fun σ σ' => SRel cl d k σ' (simStep cl d k c (bdig d b) st (σ.vars "w_c2")) ∧
        (σ'.arrs "ch").length = k + 1) (Kgrp d k + 30) := by
  rintro σ ⟨hC, hc2, hR⟩
  have hl := hB.hl
  have hchl := hC.2.2.1
  have hok : σ.vars "w_ok" < B := by
    cases st with
    | none => simp only [SRel] at hR; omega
    | some ch => simp only [SRel] at hR; omega
  have hcond : (Cond.eq (V "w_ok") (.lit 1)).evalB B σ = some (σ.vars "w_ok" == 1) :=
    evalB_condEq (evalB_var hok) (evalB_lit (by omega))
  cases st with
  | none =>
    simp only [SRel] at hR
    refine ⟨σ, (Run.ite_false (by rw [hcond, hR]; rfl) Run.skip).mono (by simp), ?_, hchl⟩
    rw [simStep_none]; exact hR
  | some ch =>
    have hR' := hR
    simp only [SRel] at hR'
    obtain ⟨h1, hch, -⟩ := hR'
    rw [← hch] at hR ⊢
    obtain ⟨σ', r, hR2, hl2⟩ := c2Grp_value hB hd σ ⟨hC, hc2, hR⟩
    exact ⟨σ', (Run.ite_true (by rw [hcond, h1]; rfl) r).mono (by simp; omega), hR2, hl2⟩

theorem c2Step_spec (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) {c b N : ℕ}
    (st : Option (List ℕ)) :
    Spec B (fun σ => C2P cl d k c b N σ ∧ σ.vars "w_c2" < cl.length ∧ SRel cl d k σ st) (c2Step d)
      (fun σ σ' => SRel cl d k σ' (simStep cl d k c (bdig d b) st (σ.vars "w_c2")) ∧
        (σ'.arrs "ch").length = k + 1 ∧ (∀ y, y ∉ grpVars → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "ch" → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out)
      (Kgrp d k + 30) :=
  Spec.post (c2Step_value hB hd st).frame fun σ σ' _ ⟨⟨h1, h2⟩, hv, ha, hi, ho⟩ =>
    ⟨h1, h2, fun y hy => hv y (wvars_c2Step d y hy), fun a hne => ha a (warrs_c2Step d a hne),
      hi (by simp [c2Step, c2Grp, grpCom, grpHead, grpTail, hitLoop, hitLit, chLoop, pick,
        Com.reads]),
      ho (by simp [c2Step, c2Grp, grpCom, grpHead, grpTail, hitLoop, hitLit, chLoop, pick,
        Com.NoWrite])⟩

/-! ### The loop over the clauses -/

def SI (cl : List (List ℕ)) (d k c b N : ℕ) (σ : Env) : Prop :=
  C2P cl d k c b N σ ∧ σ.vars "w_c2" ≤ cl.length ∧ SRel cl d k σ (stN cl d k c b (σ.vars "w_c2"))

theorem C2P.keep {c b N : ℕ} {σ σ' : Env} (h : C2P cl d k c b N σ)
    (hv : ∀ y, y ∉ grpVars → y ≠ "w_c2" → σ'.vars y = σ.vars y)
    (ha : ∀ a, a ≠ "ch" → σ'.arrs a = σ.arrs a) (hl : (σ'.arrs "ch").length = k + 1) :
    C2P cl d k c b N σ' := by
  obtain ⟨hc, hf, -, hh, h1, h2, hcv, hbv, hkey, hcm, hbk⟩ := h
  refine ⟨hc.keep (fun y hy => hv y (by revert hy y; decide) (by revert hy y; decide))
      (fun a ha' => by rw [ha a (by revert ha' a; decide)]), by rw [ha _ (by decide)]; exact hf, hl,
    by rw [ha _ (by decide)]; exact hh, h1, h2, by rw [hv _ (by decide) (by decide)]; exact hcv,
    by rw [hv _ (by decide) (by decide)]; exact hbv, by rw [hv _ (by decide) (by decide)]; exact hkey,
    hcm, hbk⟩

set_option maxHeartbeats 2000000 in
theorem c2Body_spec (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) {c b N : ℕ} :
    Spec B (fun σ => SI cl d k c b N σ ∧ σ.vars "w_c2" < cl.length) (c2Body d)
      (fun σ σ' => SI cl d k c b N σ' ∧ σ'.vars "w_c2" = σ.vars "w_c2" + 1) (Kgrp d k + 40) := by
  rintro σ ⟨⟨hC, hn, hR⟩, hlt⟩
  have hl := hB.hl
  obtain ⟨σ1, r1, hR1, hl1, hv1, ha1, -, -⟩ := c2Step_spec hB hd _ σ ⟨hC, hlt, hR⟩
  have hc2 : σ1.vars "w_c2" = σ.vars "w_c2" := hv1 _ (by decide)
  have he : (Expr.add (V "w_c2") (.lit 1)).evalB B σ1 = some (σ.vars "w_c2" + 1) := by
    rw [← hc2]
    exact evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega)
  have r2 : Run B (bump "w_c2") σ1 (σ1.setVar "w_c2" (σ.vars "w_c2" + 1)) 4 := Run.assign he
  refine ⟨_, (r1.seq r2).mono (by omega), ⟨?_, by simp [Env.setVar]; omega, ?_⟩,
    by simp [Env.setVar]⟩
  · refine C2P.keep hC (fun y hy hne => ?_) (fun a ha => by simp [Env.setVar]; exact ha1 a ha)
      (by simp [Env.setVar]; exact hl1)
    simp [Env.setVar, hne]; exact hv1 y hy
  · have e : (σ1.setVar "w_c2" (σ.vars "w_c2" + 1)).vars "w_c2" = σ.vars "w_c2" + 1 := by
      simp [Env.setVar]
    rw [e, stN_succ, SRel_congr (σ := σ1) (by simp [Env.setVar]) (by simp [Env.setVar])
      (by simp [Env.setVar]) (by simp [Env.setVar])]
    exact hR1

theorem c2Loop_spec (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) {c b N : ℕ} :
    Spec B (fun σ => SI cl d k c b N (σ.setVar "w_c2" 0)) (loop "w_c2" "w_m" (c2Body d))
      (fun _ σ' => SI cl d k c b N σ' ∧ σ'.vars "w_c2" = cl.length)
      ((Kgrp d k + 44) * cl.length + 6) := by
  have hl := hB.hl
  exact Spec.forRangeZero "w_c2" "w_m" (SI cl d k c b N) cl.length (Kgrp d k + 40) (by omega)
    (fun σ h => h.2.1) (fun σ h => h.1.1.hm) (c2Body_spec hB hd)

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgSim
