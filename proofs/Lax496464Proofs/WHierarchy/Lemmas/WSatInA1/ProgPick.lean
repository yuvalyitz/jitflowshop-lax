import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgHit

/-! # Phase 7b: one step of the search

`pick_value`: one step of the bounded search chooses the element named by the next digit of the
branch word; `grpCom_value`: a step of the search at a clause with the key of the current one. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgPick

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgHit

variable {cl : List (List ℕ)} {d k B : ℕ}

/-- The state of the search in the scalars `w_ok`, `w_nch`, `w_pw` and the array `ch`. -/
def SRel (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Option (List ℕ) → Prop
  | none => σ.vars "w_ok" = 0
  | some ch => σ.vars "w_ok" = 1 ∧ chOf σ = ch ∧ σ.vars "w_nch" = ch.length ∧
      σ.vars "w_pw" = d ^ ch.length ∧ ch.length ≤ k ∧ ∀ e ∈ ch, e ≤ nL cl

/-- The outcome of a step at an unhit clause `c2` of the group. -/
def pickR (cl : List (List ℕ)) (d k : ℕ) (ch : List ℕ) (b c2 : ℕ) : Option (List ℕ) :=
  if ch.length = k then none
  else if bdig d b ch.length < len cl c2 ∧ code cl (off cl c2 + bdig d b ch.length) % 2 = 0 then
    some (ch ++ [fst cl (off cl c2 + bdig d b ch.length)])
  else none

theorem simStep_some (c b c2 : ℕ) (ch : List ℕ) :
    simStep cl d k c (bdig d b) (some ch) c2 =
      if key cl d c2 = key cl d c ∧ hitB cl ch c2 = false then pickR cl d k ch b c2
      else some ch := rfl

theorem take_set_succ {A : List ℕ} {n : ℕ} (hn : n < A.length) (v : ℕ) :
    (A.set n v).take (n + 1) = A.take n ++ [v] := by
  rw [List.take_add_one, List.getElem?_set_self (by simpa using hn), Option.toList_some,
    List.take_set_of_le (le_refl n)]

/-- The facts a step reads. -/
def PKP (cl : List (List ℕ)) (d k : ℕ) (ch : List ℕ) (b c2 : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧ (σ.arrs "ch").length = k + 1 ∧ c2 < cl.length ∧
    σ.vars "w_o" = off cl c2 ∧ σ.vars "w_ln" = len cl c2 ∧ σ.vars "w_b" = b ∧ b < d ^ k ∧
    SRel cl d k σ (some ch)

theorem fst_le_nL (cl : List (List ℕ)) (j : ℕ) : fst cl j ≤ nL cl := by
  unfold fst; rw [← length_varList]; exact List.idxOf_le_length

theorem mod_eq_sub (a d : ℕ) : a - a / d * d = a % d := by
  rw [Nat.mod_def, Nat.mul_comm]

set_option maxHeartbeats 8000000 in
theorem pick_value (hB : BB cl d k B) {ch : List ℕ} {b c2 : ℕ} (hbk : b < d ^ k) :
    Spec B (PKP cl d k ch b c2) (pick d)
      (fun _ σ' => SRel cl d k σ' (pickR cl d k ch b c2) ∧ (σ'.arrs "ch").length = k + 1) 60 := by
  have hl := hB.hl
  have hMB := hB.cb.small
  have hdk := hB.cb.dk
  have hsz := nL_le_sz cl d k
  have hbB : b < B := lt_of_lt_of_le hbk (hdk k le_rfl).le
  have hfl := fst_le_nL cl
  set n := ch.length with hn
  set dg := bdig d b n with hdg
  refine Spec.pre (P := fun σ => PKP cl d k ch b c2 σ ∧
      σ.vars "w_nch" = n ∧ σ.vars "w_k" = k ∧ σ.vars "w_pw" = d ^ n ∧ σ.vars "w_b" = b ∧
      σ.vars "w_ln" = len cl c2 ∧ n ≤ k ∧
      b / d ^ n - b / d ^ n / d * d = dg ∧ b / d ^ n < B ∧ b / d ^ n / d < B ∧
      b / d ^ n / d * d < B ∧ dg < B ∧ d < B ∧ σ.vars "w_ln" < B ∧ σ.vars "w_nch" < B ∧
      σ.vars "w_k" < B ∧ 1 < B ∧
      (dg < len cl c2 → σ.vars "w_o" + dg < (σ.arrs "cd").length ∧
        σ.vars "w_o" + dg < (σ.arrs "fp_f").length ∧ σ.vars "w_o" + dg < B ∧
        (σ.arrs "cd").getD (σ.vars "w_o" + dg) 0 = code cl (off cl c2 + dg) ∧
        (σ.arrs "fp_f").getD (σ.vars "w_o" + dg) 0 = fst cl (off cl c2 + dg) ∧
        code cl (off cl c2 + dg) < B ∧ fst cl (off cl c2 + dg) < B) ∧
      (n < k → n < (σ.arrs "ch").length ∧ n + 1 < B ∧ d ^ n * d = d ^ (n + 1) ∧
        d ^ n * d < B ∧ (σ.arrs "ch").take n = ch)) ?_ ?_
  · unfold pick
    run_vcg
    all_goals (try simp only [PKP, SRel, pickR, Ctx, CPost, chOf] at *)
    all_goals (try simp_all [Env.setVar, Env.setArr, take_set_succ]; try omega)
    all_goals (try (refine ⟨by ring, by omega, fun e he => ?_⟩; rcases he with he | rfl <;> simp_all))
    all_goals (split_ifs with hh)
    · exact absurd hh.1 (Nat.not_lt.mpr ‹_›)
    · trivial
  · intro σ hσ
    obtain ⟨hc, hf, hchl, hc2, ho, hln, hb, -, hR⟩ := id hσ
    simp only [SRel] at hR
    obtain ⟨-, hch, hnch, hpw, hlk, -⟩ := hR
    have hol := off_len_le cl hc2
    have h1 : b / d ^ n ≤ b := Nat.div_le_self _ _
    have h2 : b / d ^ n / d ≤ b / d ^ n := Nat.div_le_self _ _
    have h3 : b / d ^ n / d * d ≤ b / d ^ n := Nat.div_mul_le_self _ _
    have h4 : dg ≤ b / d ^ n := Nat.mod_le _ _
    refine ⟨hσ, hnch, hc.hk, hpw, hb, hln, hlk, mod_eq_sub _ _, by omega, by omega, by omega,
      by omega, by omega, by rw [hln]; omega, by rw [hnch]; omega, by rw [hc.hk]; omega, by omega,
      fun hlt => ?_, fun hlt => ?_⟩
    · have hj : off cl c2 + dg < nL cl := off_lt cl hc2 hlt
      refine ⟨by rw [hc.hcd, ho]; exact hj, by rw [hf, length_F1, ho]; omega, by rw [ho]; omega,
        by rw [hc.hcd, ho]; rfl, by rw [hf, ho]; exact WH_F1_getD hj, code_lt hB.hx hj,
        by have := hfl (off cl c2 + dg); omega⟩
    · refine ⟨by rw [hchl]; omega, by omega, by ring, ?_, ?_⟩
      · rw [← pow_succ]; exact hdk _ (by omega)
      · rw [← hch]; unfold chOf; rw [hnch]

/-- The facts a step of the search reads, relative to the state. -/
def GP (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Prop :=
  Ctx cl d k σ ∧ σ.arrs "fp_f" = F1 cl d k ∧ (σ.arrs "ch").length = k + 1 ∧
    σ.vars "w_c2" < cl.length ∧ σ.vars "w_b" < d ^ k ∧ SRel cl d k σ (some (chOf σ))

/-- The outcome of a step at a clause of the group. -/
def grpR (cl : List (List ℕ)) (d k : ℕ) (ch : List ℕ) (b c2 : ℕ) : Option (List ℕ) :=
  if hitB cl ch c2 = false then pickR cl d k ch b c2 else some ch

theorem SRel_congr {σ σ' : Env} (h1 : σ'.vars "w_ok" = σ.vars "w_ok")
    (h2 : σ'.vars "w_nch" = σ.vars "w_nch") (h3 : σ'.vars "w_pw" = σ.vars "w_pw")
    (h4 : σ'.arrs "ch" = σ.arrs "ch") (st : Option (List ℕ)) :
    SRel cl d k σ' st ↔ SRel cl d k σ st := by
  have hc : chOf σ' = chOf σ := by unfold chOf; rw [h2, h4]
  cases st <;> simp only [SRel, h1, h2, h3, hc]

set_option maxHeartbeats 2000000 in
theorem grpHead_spec (hB : BB cl d k B) :
    Spec B (GP cl d k) grpHead
      (fun σ σ' => σ' = ((σ.setVar "w_o" (off cl (σ.vars "w_c2"))).setVar "w_ln"
        (len cl (σ.vars "w_c2"))).setVar "w_hit" 0) 20 := by
  have hl := hB.hl
  refine Spec.pre (P := fun σ => GP cl d k σ ∧
      σ.vars "w_c2" + 1 < (σ.arrs "co").length ∧
      (σ.arrs "co").getD (σ.vars "w_c2") 0 = off cl (σ.vars "w_c2") ∧
      (σ.arrs "co").getD (σ.vars "w_c2" + 1) 0 - off cl (σ.vars "w_c2") = len cl (σ.vars "w_c2") ∧
      (σ.arrs "co").getD (σ.vars "w_c2") 0 < B ∧ (σ.arrs "co").getD (σ.vars "w_c2" + 1) 0 < B ∧
      σ.vars "w_c2" + 1 < B ∧ 1 < B ∧ len cl (σ.vars "w_c2") < B) ?_ ?_
  · unfold grpHead
    run_vcg
    all_goals (simp only [Env.setVar] at *; simp_all)
  · intro σ hσ
    have hco := hσ.1.hco
    have hc2 := hσ.2.2.2.1
    have hol := off_len_le cl hc2
    have hsucc := off_succ cl hc2
    refine ⟨hσ, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by omega⟩
    · rw [hco, length_coList]; omega
    · rw [hco, coList_getD (by omega)]
    · rw [hco, coList_getD (by omega)]; omega
    · rw [hco, coList_getD (by omega)]; omega
    · rw [hco, coList_getD (by omega)]; omega

/-- The cost of a step at a clause of the group. -/
def Kgrp (d k : ℕ) : ℕ := 20 + (Khit d k + 70)

set_option maxHeartbeats 4000000 in
theorem grpCom_value (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) :
    Spec B (GP cl d k) (grpCom d)
      (fun σ σ' => SRel cl d k σ' (grpR cl d k (chOf σ) (σ.vars "w_b") (σ.vars "w_c2")) ∧
        (σ'.arrs "ch").length = k + 1) (Kgrp d k) := by
  intro σ hσ
  have hl := hB.hl
  have hMB := hB.cb.small
  obtain ⟨hc, hf, hchl, hc2, hbk, hR⟩ := id hσ
  set c2 := σ.vars "w_c2" with hc2def
  set b := σ.vars "w_b" with hbdef
  set ch := chOf σ with hchdef
  obtain ⟨σ1, r1, rfl⟩ := grpHead_spec hB σ hσ
  have hR' := hR
  simp only [SRel] at hR'
  obtain ⟨hok, -, hnch, hpw, hlk, hent⟩ := hR'
  have hch1 : chOf (((σ.setVar "w_o" (off cl c2)).setVar "w_ln" (len cl c2)).setVar "w_hit" 0) =
      ch := by simp [chOf, Env.setVar, hchdef]
  have hHP : HP cl d k c2 (((σ.setVar "w_o" (off cl c2)).setVar "w_ln" (len cl c2)).setVar "w_hit" 0)
      ∧ (((σ.setVar "w_o" (off cl c2)).setVar "w_ln" (len cl c2)).setVar "w_hit" 0).vars "w_hit" = 0 := by
    refine ⟨⟨by simp [Env.setVar, hc.hcd], by simp [Env.setVar, hf], hc2, by simp [Env.setVar],
      by simp [Env.setVar], by simp [Env.setVar, hnch, hlk], by simp [Env.setVar, hnch, hchl]; omega,
      by rw [hch1]; exact hent⟩, by simp [Env.setVar]⟩
  obtain ⟨σ2, r2, hhit, hhit1, hv2, ha2, hi2, ho2⟩ := hitLoop_spec hB hd _ hHP
  rw [hch1] at hhit
  -- the facts that survive the scan
  have hv2' : ∀ y, y ∉ ["w_i", "w_f", "w_q", "w_hit", "w_o", "w_ln"] → σ2.vars y = σ.vars y := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [hv2 y (by simp [hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1])]
    simp [Env.setVar, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]
  have ha2' : σ2.arrs = σ.arrs := by rw [ha2]; rfl
  have hRel2 : SRel cl d k σ2 (some ch) := by
    rw [SRel_congr (σ := σ) (hv2' _ (by decide)) (hv2' _ (by decide)) (hv2' _ (by decide))
      (by rw [ha2'])]
    exact hR
  have hcond : ∀ v, σ2.vars "w_hit" = v → (Cond.eq (V "w_hit") (.lit 0)).evalB B σ2 =
      some (v == 0) := by
    intro v hv; rw [← hv]; exact evalB_condEq (evalB_var (by omega)) (evalB_lit (by omega))
  by_cases hh : hitB cl ch c2 = true
  · have h1 : σ2.vars "w_hit" = 1 := hhit.mpr hh
    have r3 : Run B (grpTail d) σ2 σ2 (1 + 3 + 1) :=
      Run.ite_false (by rw [hcond 1 h1]; rfl) Run.skip
    have hg : grpR cl d k ch b c2 = some ch := by simp only [grpR, hh]; rfl
    refine ⟨σ2, (r1.seq (r2.seq r3)).mono (by unfold Kgrp; omega), ?_, by rw [ha2']; exact hchl⟩
    rw [show grpR cl d k (chOf σ) (σ.vars "w_b") (σ.vars "w_c2") = some ch from hg]
    exact hRel2
  · have h0 : σ2.vars "w_hit" = 0 := by
      have : σ2.vars "w_hit" ≠ 1 := fun h => hh (hhit.mp h)
      omega
    have hPKP : PKP cl d k ch b c2 σ2 := by
      refine ⟨hc.keep (fun y hy => hv2' y (by revert hy y; decide))
        (fun a _ => by rw [ha2']), by rw [ha2']; exact hf,
        by rw [ha2']; exact hchl, hc2, ?_, ?_, hv2' _ (by decide), hbk, hRel2⟩
      · rw [hv2 "w_o" (by decide)]; simp [Env.setVar]
      · rw [hv2 "w_ln" (by decide)]; simp [Env.setVar]
    obtain ⟨σ3, r3, hR3, hl3⟩ := pick_value hB hbk σ2 hPKP
    have r3' : Run B (grpTail d) σ2 σ3 (1 + 3 + 60) :=
      Run.ite_true (by rw [hcond 0 h0]; rfl) r3
    have hg : grpR cl d k ch b c2 = pickR cl d k ch b c2 := by
      simp only [grpR, show hitB cl ch c2 = false by simpa using hh]; rfl
    refine ⟨σ3, (r1.seq (r2.seq r3')).mono (by unfold Kgrp; omega), ?_, hl3⟩
    rw [show grpR cl d k (chOf σ) (σ.vars "w_b") (σ.vars "w_c2") = pickR cl d k ch b c2 from hg]
    exact hR3

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgPick
