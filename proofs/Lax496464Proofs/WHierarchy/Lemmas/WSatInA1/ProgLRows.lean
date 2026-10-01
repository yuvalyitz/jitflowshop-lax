import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRow

/-! # Phase 7: all searches

`lRows_spec`: phase 7 runs the bounded search for every clause and every branch word and stores the
numbers of the tuples found, filling the array of numbers up to its last segment (`hsS_lfull`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRows

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgNRows
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgHit Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgPick
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgSim Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRow

variable {cl : List (List ℕ)} {d k B : ℕ}

theorem simHead_spec (hB : BB cl d k B) {c N : ℕ} (hc : c < cl.length)
    (hN1 : 2 * nL cl + cl.length ≤ N) (hN2 : N ≤ sz cl d k) :
    Spec B (fun σ => Ctx cl d k σ ∧ σ.vars "w_c" = c ∧ σ.arrs "hs_mem" = hsS cl d k N) simHead
      (fun σ σ' => σ' = (((σ.setVar "w_nch" 0).setVar "w_pw" 1).setVar "w_ok" 1).setVar "w_key"
        (nNum cl d c)) 20 := by
  have hl := hB.hl
  have hszB := hB.cb.sz
  have hnk := nNum_lt hB c
  refine Spec.pre (P := fun σ => Ctx cl d k σ ∧ σ.vars "w_c" = c ∧
      σ.arrs "hs_mem" = hsS cl d k N ∧ σ.vars "w_L" = nL cl ∧
      2 * nL cl + c < (hsS cl d k N).length ∧
      (hsS cl d k N).getD (2 * nL cl + c) 0 = nNum cl d c) ?_ ?_
  · unfold simHead
    run_vcg
    all_goals (simp only [Env.setVar] at *; simp_all; try omega)
  · rintro σ ⟨hc', hcv, hh⟩
    exact ⟨hc', hcv, hh, hc'.hL, by rw [length_hsS]; omega, hs_nNum hN1 hN2 hc⟩

/-- The invariant of the loop over the branch words of clause `c`. -/
def BI (cl : List (List ℕ)) (d k c : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧ (σ.arrs "ch").length = k + 1 ∧ σ.vars "w_c" = c ∧
    σ.vars "w_b" ≤ d ^ k ∧
    σ.vars "w_cur" = 2 * nL cl + cl.length + (lPre cl d k c (σ.vars "w_b")).length ∧
    σ.arrs "hs_mem" = hsS cl d k (σ.vars "w_cur")

/-- The cost of one search. -/
def Ksim (cl : List (List ℕ)) (d k : ℕ) : ℕ :=
  20 + ((Kgrp d k + 44) * cl.length + 6) + (Kpad k + 40) + 4

theorem c2Loop_frame (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) {c b N : ℕ} :
    Spec B (fun σ => SI cl d k c b N (σ.setVar "w_c2" 0)) (loop "w_c2" "w_m" (c2Body d))
      (fun σ σ' => SI cl d k c b N σ' ∧ σ'.vars "w_c2" = cl.length ∧
        σ'.vars "w_cur" = σ.vars "w_cur") ((Kgrp d k + 44) * cl.length + 6) :=
  Spec.post (c2Loop_spec hB hd).frame (by
    rintro σ σ' - ⟨⟨h1, h2⟩, hv, -⟩
    exact ⟨h1, h2, hv _ (by simp [c2Body, c2Step, c2Grp, grpCom, grpHead, grpTail, hitLoop, hitLit,
      chLoop, pick, Com.wvars])⟩)

theorem lRow_frame (hB : BB cl d k B) {c N : ℕ} {ch : List ℕ} (hN : N < sz cl d k)
    (hval : (hs cl d k).getD N 0 = nNum cl d c + 1 + MM cl ^ (d + 2) * num (MM cl) (pad cl k ch)) :
    Spec B (LP cl d k c N ch) lRow
      (fun σ σ' => σ'.arrs "hs_mem" = hsS cl d k (N + 1) ∧ σ'.vars "w_cur" = N + 1 ∧
        (∀ y, y ∉ ["w_acc", "w_pw2", "w_q", "w_e", "w_cur"] → σ'.vars y = σ.vars y) ∧
        (∀ a, a ≠ "hs_mem" → σ'.arrs a = σ.arrs a)) (Kpad k + 30) :=
  Spec.post (lRow_value hB hN hval).frame (by
    rintro σ σ' - ⟨⟨h1, h2⟩, hv, ha, -⟩
    refine ⟨h1, h2, fun y hy => hv y ?_, fun a hne => ha a (by simp [lRow, padBody, Com.warrs, hne])⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [lRow, padBody, Com.wvars, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2])

set_option maxHeartbeats 4000000 in
theorem simBody_spec (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) {c : ℕ}
    (hc : c < cl.length) :
    Spec B (fun σ => BI cl d k c σ ∧ σ.vars "w_b" < d ^ k) (simBody d)
      (fun σ σ' => BI cl d k c σ' ∧ σ'.vars "w_b" = σ.vars "w_b" + 1) (Ksim cl d k) := by
  rintro σ ⟨⟨hC, hf, hchl, hcv, hbd, hcur, hh⟩, hb⟩
  have hl := hB.hl
  have hMB := hB.cb.small
  have hdk := hB.cb.dk k le_rfl
  set b := σ.vars "w_b" with hbdef
  set N := σ.vars "w_cur" with hNdef
  have hlp := length_lPre_le cl d k hc hbd
  have hlt := length_lTuples cl d k
  have hN1 : 2 * nL cl + cl.length ≤ N := by omega
  have hN2 : N ≤ sz cl d k := by unfold sz; omega
  -- the head
  obtain ⟨σ1, r1, rfl⟩ := simHead_spec hB hc hN1 hN2 σ ⟨hC, hcv, hh⟩
  set σ1 := (((σ.setVar "w_nch" 0).setVar "w_pw" 1).setVar "w_ok" 1).setVar "w_key" (nNum cl d c)
    with hσ1
  -- the loop over the clauses
  have hSI : SI cl d k c b N (σ1.setVar "w_c2" 0) := by
    refine ⟨⟨hC.keep (fun y hy => ?_) (fun a _ => rfl), by simp [hσ1, Env.setVar, hf],
      by simp [hσ1, Env.setVar, hchl], by simp [hσ1, Env.setVar, hh], hN1, hN2,
      by simp [hσ1, Env.setVar, hcv], by simp [hσ1, Env.setVar, hbdef],
      by simp [hσ1, Env.setVar], hc, hb⟩, by simp [Env.setVar], ?_⟩
    · simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
      simp only [hσ1, Env.setVar]
      rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
    · simp [SRel, stN, chOf, hσ1, Env.setVar]
  obtain ⟨σ2, r2, ⟨hC2, -, hR2⟩, hc2, hcur2⟩ := c2Loop_frame hB hd σ1 hSI
  rw [hc2, stN_all] at hR2
  have hcur2' : σ2.vars "w_cur" = N := by rw [hcur2]; simp [hσ1, Env.setVar, hNdef]
  obtain ⟨hC2', hf2, hchl2, hh2, -, -, hcv2, hbv2, hkey2, -, -⟩ := hC2
  have hok : σ2.vars "w_ok" < B := by
    cases hsim : sim cl d k c b with
    | none => rw [hsim] at hR2; simp only [SRel] at hR2; omega
    | some ch => rw [hsim] at hR2; simp only [SRel] at hR2; omega
  have hcond : (Cond.eq (V "w_ok") (.lit 1)).evalB B σ2 = some (σ2.vars "w_ok" == 1) :=
    evalB_condEq (evalB_var hok) (evalB_lit (by omega))
  -- the tail
  obtain ⟨σ3, r3, hC3, hf3, hchl3, hcv3, hbv3, hcur3, hh3⟩ : ∃ σ3, Run B simTail σ2 σ3 (Kpad k + 40) ∧
      Ctx cl d k σ3 ∧ σ3.arrs "fp_f" = F1 cl d k ∧ (σ3.arrs "ch").length = k + 1 ∧
      σ3.vars "w_c" = c ∧ σ3.vars "w_b" = b ∧
      σ3.vars "w_cur" = 2 * nL cl + cl.length + (lPre cl d k c (b + 1)).length ∧
      σ3.arrs "hs_mem" = hsS cl d k (σ3.vars "w_cur") := by
    cases hsim : sim cl d k c b with
    | none =>
      rw [hsim] at hR2
      simp only [SRel] at hR2
      have hg : gT cl d k c b = none := by simp [gT, hsim]
      refine ⟨σ2, (Run.ite_false (by rw [hcond, hR2]; rfl) Run.skip).mono (by simp),
        hC2', hf2, hchl2, hcv2, hbv2, ?_, ?_⟩
      · rw [hcur2', lPre_succ, hg]; simp [hcur]
      · rw [hcur2', hh2]
    | some ch =>
      rw [hsim] at hR2
      have hR2' := hR2
      simp only [SRel] at hR2'
      obtain ⟨hlnum, hlval⟩ := lNums_at cl d k hc hb hsim
      have hNr : N = 2 * nL cl + cl.length + (lPre cl d k c b).length := hcur
      have hN : N < sz cl d k := by
        have := length_lNums cl d k; unfold sz; omega
      have hval : (hs cl d k).getD N 0 =
          nNum cl d c + 1 + MM cl ^ (d + 2) * num (MM cl) (pad cl k ch) := by
        rw [hNr, hs_l cl d k hlnum, hlval, lval]
      obtain ⟨σ3, r3, hh3, hcur3, hv3, ha3⟩ := lRow_frame hB hN hval σ2
        ⟨hC2', hkey2, hR2, hcur2', hh2, hchl2⟩
      have hg : gT cl d k c b = some (key cl d c ++ pad cl k ch) := by simp [gT, hsim]
      refine ⟨σ3, (Run.ite_true (by rw [hcond, hR2'.1]; rfl) r3).mono (by simp; omega),
        hC2'.keep (fun y hy => hv3 y (by revert hy y; decide)) (fun a ha => ha3 a (by
          revert ha a; decide)), by rw [ha3 _ (by decide)]; exact hf2,
        by rw [ha3 _ (by decide)]; exact hchl2, by rw [hv3 _ (by decide)]; exact hcv2,
        by rw [hv3 _ (by decide)]; exact hbv2, ?_, by rw [hcur3, hh3]⟩
      rw [hcur3, lPre_succ, hg, hNr]; simp; omega
  -- the next branch word
  have he : (Expr.add (V "w_b") (.lit 1)).evalB B σ3 = some (b + 1) := by
    rw [← hbv3]
    exact evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega)
  have r4 : Run B (bump "w_b") σ3 (σ3.setVar "w_b" (b + 1)) 4 := Run.assign he
  refine ⟨_, (r1.seq (r2.seq (r3.seq r4))).mono (by unfold Ksim; omega), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by simp [Env.setVar, hbdef]⟩
  · refine hC3.keep (fun y hy => ?_) (fun a _ => rfl)
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]
    rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · simp [Env.setVar, hf3]
  · simp [Env.setVar, hchl3]
  · simp [Env.setVar, hcv3]
  · simp [Env.setVar]; omega
  · simp [Env.setVar, hcur3]
  · simp [Env.setVar, hh3]

/-- The cost of the loop over the branch words. -/
def KbLoop (cl : List (List ℕ)) (d k : ℕ) : ℕ := (Ksim cl d k + 4) * d ^ k + 6

theorem bLoop_spec (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) {c : ℕ}
    (hc : c < cl.length) :
    Spec B (fun σ => BI cl d k c (σ.setVar "w_b" 0)) (loop "w_b" "w_dk" (simBody d))
      (fun _ σ' => BI cl d k c σ' ∧ σ'.vars "w_b" = d ^ k) (KbLoop cl d k) :=
  Spec.forRangeZero "w_b" "w_dk" (BI cl d k c) (d ^ k) (Ksim cl d k)
    (by have := hB.cb.dk k le_rfl; omega) (fun σ h => h.2.2.2.2.1) (fun σ h => h.1.hdk)
    (simBody_spec hB hd hc)

/-- The invariant of the loop over the clauses. -/
def CI2 (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧ (σ.arrs "ch").length = k + 1 ∧
    σ.vars "w_c" ≤ cl.length ∧
    σ.vars "w_cur" = 2 * nL cl + cl.length + (lPre cl d k (σ.vars "w_c") 0).length ∧
    σ.arrs "hs_mem" = hsS cl d k (σ.vars "w_cur")

theorem lBody_spec (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) :
    Spec B (fun σ => CI2 cl d k σ ∧ σ.vars "w_c" < cl.length) (lBody d)
      (fun σ σ' => CI2 cl d k σ' ∧ σ'.vars "w_c" = σ.vars "w_c" + 1) (KbLoop cl d k + 4) := by
  rintro σ ⟨⟨hC, hf, hchl, hcm, hcur, hh⟩, hlt⟩
  have hl := hB.hl
  set c := σ.vars "w_c" with hcdef
  have hBI : BI cl d k c (σ.setVar "w_b" 0) := by
    refine ⟨hC.keep (fun y hy => ?_) (fun a _ => rfl), by simp [Env.setVar, hf],
      by simp [Env.setVar, hchl], by simp [Env.setVar, hcdef], by simp [Env.setVar],
      by simp [Env.setVar, hcur], by simp [Env.setVar, hh]⟩
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ1, r1, ⟨hC1, hf1, hchl1, hc1, -, hcur1, hh1⟩, hb1⟩ := bLoop_spec hB hd hlt σ hBI
  have he : (Expr.add (V "w_c") (.lit 1)).evalB B σ1 = some (c + 1) := by
    rw [← hc1]
    exact evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega)
  have r2 : Run B (bump "w_c") σ1 (σ1.setVar "w_c" (c + 1)) 4 := Run.assign he
  refine ⟨_, r1.seq r2, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [Env.setVar, hcdef]⟩
  · refine hC1.keep (fun y hy => ?_) (fun a _ => rfl)
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · simp [Env.setVar, hf1]
  · simp [Env.setVar, hchl1]
  · simp [Env.setVar]; omega
  · simp only [Env.setVar, if_pos]
    simp [hcur1, hb1, lPre_next]
  · simp [Env.setVar, hh1]

/-- The cost of `lRows`. -/
def KlRows (cl : List (List ℕ)) (d k : ℕ) : ℕ := (KbLoop cl d k + 8) * cl.length + 20

theorem hsS_lfull : hsS cl d k (2 * nL cl + cl.length + (lTuples cl d k).length) = hs cl d k := by
  have h1 := length_hs cl d k
  have h2 := length_lTuples cl d k
  have e : hs cl d k = (varNums cl ++ canonNums cl ++ nNums cl d ++ lNums cl d k) ++
      List.replicate (sz cl d k - (2 * nL cl + cl.length + (lNums cl d k).length)) 0 := rfl
  have hl : (varNums cl ++ canonNums cl ++ nNums cl d ++ lNums cl d k).length =
      2 * nL cl + cl.length + (lTuples cl d k).length := by
    simp [length_varNums, length_canonNums, length_nNums, length_lNums]; ring
  unfold hsS
  conv_lhs => rw [e]
  rw [List.take_append_of_le_length (by rw [hl]), List.take_of_length_le (by rw [hl]), ← e, h1,
    e, length_lNums]

theorem lRows_spec (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) :
    Spec B (fun σ => Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧ (σ.arrs "ch").length = k + 1 ∧
        σ.arrs "hs_mem" = hsS cl d k (2 * nL cl + cl.length)) (lRows d)
      (fun _ σ' => Ctx cl d k σ' ∧ σ'.arrs "hs_mem" = hs cl d k) (KlRows cl d k) := by
  rintro σ ⟨hC, hf, hchl, hh⟩
  have hl := hB.hl
  have hszB := hB.cb.sz
  have hsz := nL_le_sz cl d k
  have he : (Expr.add (.mul (.lit 2) (V "w_L")) (V "w_m")).evalB B σ =
      some (2 * nL cl + cl.length) := by
    rw [← hC.hL, ← hC.hm]
    exact evalB_bin (evalB_bin (evalB_lit (by omega)) (evalB_var (by rw [hC.hL]; omega))
      (by simp; rw [hC.hL]; omega)) (evalB_var (by rw [hC.hm]; omega)) (by simp; rw [hC.hL, hC.hm]; omega)
  have r1 : Run B (.assign "w_cur" (.add (.mul (.lit 2) (V "w_L")) (V "w_m"))) σ
      (σ.setVar "w_cur" (2 * nL cl + cl.length)) 6 := Run.assign he
  have hloop := Spec.forRangeZero (B := B) "w_c" "w_m" (CI2 cl d k) cl.length (KbLoop cl d k + 4)
    (by omega) (fun σ h => h.2.2.2.1) (fun σ h => h.1.hm) (lBody_spec hB hd)
  have hCI : CI2 cl d k ((σ.setVar "w_cur" (2 * nL cl + cl.length)).setVar "w_c" 0) := by
    refine ⟨hC.keep (fun y hy => ?_) (fun a _ => rfl), by simp [Env.setVar, hf],
      by simp [Env.setVar, hchl], by simp [Env.setVar], by simp [Env.setVar, lPre],
      by simp [Env.setVar, hh]⟩
    simp only [ctxVars, List.mem_cons, List.not_mem_nil, or_false] at hy
    simp only [Env.setVar]; rcases hy with h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  obtain ⟨σ2, r2, ⟨hC2, -, -, -, hcur2, hh2⟩, hc2⟩ := hloop _ hCI
  refine ⟨σ2, (r1.seq r2).mono (by unfold KlRows; nlinarith), hC2, ?_⟩
  rw [hh2, hcur2, hc2, lPre_all, hsS_lfull]

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgLRows
