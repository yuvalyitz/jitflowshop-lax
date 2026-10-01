import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutS

/-! # Phases 8–9: the fresh quantifiers and the translated formula

`qOut_spec`: the block of fresh existential quantifiers; `relOut_value`: the translation of a
relation atom, its argument conjuncts (`argLoop_spec`) and its symbol `P_i` (`pComp_spec`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutF

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Syntax Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutS

variable {x : List ℕ} {φ : Formula} {B : ℕ}

/-! ### The quantifiers of the fresh variables -/

/-- What `qOut` writes. -/
def qList (x : List ℕ) (q : ℕ) : List ℕ := (List.range q).flatMap fun j => [6, fOf x + j]

theorem qOut_value (hd : Dom x φ) (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x φ σ ∧ σ.out = out0) qOut
      (fun _ σ' => σ'.out = out0 ++ qList x (nrel φ)) ((20 + 4) * nrel φ + 6) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have hq := hz.q_le
  have hbody : Spec B (fun σ => (Ctx x φ σ ∧ σ.vars "ic_j" ≤ nrel φ ∧
        σ.out = out0 ++ qList x (σ.vars "ic_j")) ∧ σ.vars "ic_j" < nrel φ) qBody
      (fun σ σ' => (Ctx x φ σ' ∧ σ'.vars "ic_j" ≤ nrel φ ∧
        σ'.out = out0 ++ qList x (σ'.vars "ic_j")) ∧ σ'.vars "ic_j" = σ.vars "ic_j" + 1) 20 := by
    unfold qBody
    refine Spec.pre (P := fun σ => (Ctx x φ σ ∧ σ.vars "ic_j" ≤ nrel φ ∧
        σ.out = out0 ++ qList x (σ.vars "ic_j")) ∧ σ.vars "ic_j" < nrel φ ∧
        fOf x + σ.vars "ic_j" < B) ?_ ?_
    · run_vcg
      all_goals (simp only [Ctx, qList] at *; simp_all [Env.setVar, List.range_succ]; try omega)
    · rintro σ ⟨h1, h2⟩
      exact ⟨h1, h2, by unfold fOf; omega⟩
  refine Spec.post (Spec.pre (Spec.forRangeZero "ic_j" "ic_q" _ (nrel φ) 20 (by omega)
    (fun σ h => h.2.1) (fun σ h => h.1.2.2.2.2.2.2.2.1) hbody) ?_) ?_
  · rintro σ ⟨hc, ho⟩
    simp only [Ctx, Env.setVar] at hc ⊢
    simp_all [qList]
  · rintro σ σ' - ⟨⟨-, -, ho⟩, hj⟩
    rw [ho, hj]

theorem qOut_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (Ctx x φ) qOut
      (fun σ σ' => σ'.out = σ.out ++ qList x (nrel φ) ∧ Keep ["ic_j"] σ σ')
      ((20 + 4) * nrel φ + 6) := by
  intro σ hσ
  have h := Spec.keep (qOut_value hd hB σ.out) ["ic_j"]
    (by intro y hy; simpa [qOut, qBody, bump, Com.wvars] using hy)
    (by simp [qOut, qBody, bump, Com.warrs]) (by simp [qOut, qBody, bump, Com.reads])
  exact h σ ⟨hσ, rfl⟩

/-! ### The arguments of an atom -/

/-- What `argLoop` writes. -/
def argList (x : List ℕ) (s p zz k : ℕ) : List ℕ :=
  (List.range k).flatMap fun l => [4, 0, s + l, 2, x.getD (p + 3 + l) 0, zz]

theorem argList_succ (x : List ℕ) (s p zz k : ℕ) :
    argList x s p zz (k + 1) = argList x s p zz k ++ [4, 0, s + k, 2, x.getD (p + 3 + k) 0, zz] := by
  simp [argList, List.range_succ]

theorem argLoop_value (hB : BOK x B) (s p zz k : ℕ) (hk : p + 3 + k ≤ x.length)
    (hs : s + k < B) (hzz : zz < B) (out0 : List ℕ) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_s" = s ∧ σ.vars "ic_p" = p ∧
        σ.vars "ic_zz" = zz ∧ σ.vars "ic_k" = k ∧ σ.out = out0) argLoop
      (fun _ σ' => σ'.out = out0 ++ argList x s p zz k) ((60 + 4) * k + 6) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hbody : Spec B (fun σ => (σ.arrs "a" = x ∧ σ.vars "ic_s" = s ∧ σ.vars "ic_p" = p ∧
        σ.vars "ic_zz" = zz ∧ σ.vars "ic_k" = k ∧ σ.vars "ic_l" ≤ k ∧
        σ.out = out0 ++ argList x s p zz (σ.vars "ic_l")) ∧ σ.vars "ic_l" < k) argBody
      (fun σ σ' => (σ'.arrs "a" = x ∧ σ'.vars "ic_s" = s ∧ σ'.vars "ic_p" = p ∧
        σ'.vars "ic_zz" = zz ∧ σ'.vars "ic_k" = k ∧ σ'.vars "ic_l" ≤ k ∧
        σ'.out = out0 ++ argList x s p zz (σ'.vars "ic_l")) ∧
        σ'.vars "ic_l" = σ.vars "ic_l" + 1) 60 := by
    unfold argBody
    refine Spec.pre (P := fun σ => ((σ.arrs "a" = x ∧ σ.vars "ic_s" = s ∧ σ.vars "ic_p" = p ∧
        σ.vars "ic_zz" = zz ∧ σ.vars "ic_k" = k ∧ σ.vars "ic_l" ≤ k ∧
        σ.out = out0 ++ argList x s p zz (σ.vars "ic_l")) ∧ σ.vars "ic_l" < k) ∧
        p + 3 + σ.vars "ic_l" < (σ.arrs "a").length ∧
        (σ.arrs "a").getD (p + 3 + σ.vars "ic_l") 0 < B ∧ p + 3 + σ.vars "ic_l" < B) ?_ ?_
    · run_vcg
      all_goals (simp_all [Env.setVar, argList_succ]; try omega)
    · rintro σ ⟨⟨ha, h1, h2, h3, h4, h5, h6⟩, h7⟩
      exact ⟨⟨⟨ha, h1, h2, h3, h4, h5, h6⟩, h7⟩, by rw [ha]; omega, by rw [ha]; exact getD_lt hB _,
        by omega⟩
  refine Spec.post (Spec.pre (Spec.forRangeZero "ic_l" "ic_k" _ k 60 (by omega)
    (fun σ h => h.2.2.2.2.2.1) (fun σ h => h.2.2.2.2.1) hbody) ?_) ?_
  · rintro σ ⟨ha, h1, h2, h3, h4, h5⟩
    simp [Env.setVar, ha, h1, h2, h3, h4, h5, argList]
  · rintro σ σ' - ⟨⟨-, -, -, -, -, -, ho⟩, hl⟩
    rw [ho, hl]

theorem argLoop_spec (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_p" + 3 + σ.vars "ic_k" ≤ x.length ∧
        σ.vars "ic_s" + σ.vars "ic_k" < B ∧ σ.vars "ic_zz" < B)
      argLoop
      (fun σ σ' => σ'.out = σ.out ++
        argList x (σ.vars "ic_s") (σ.vars "ic_p") (σ.vars "ic_zz") (σ.vars "ic_k") ∧
        Keep ["ic_l"] σ σ') ((60 + 4) * x.length + 6) := by
  intro σ hσ
  have h := Spec.keep (argLoop_value hB (σ.vars "ic_s") (σ.vars "ic_p") (σ.vars "ic_zz")
    (σ.vars "ic_k") hσ.2.1 hσ.2.2.1 hσ.2.2.2 σ.out) ["ic_l"]
    (by intro y hy; simpa [argLoop, argBody, bump, Com.wvars] using hy)
    (by simp [argLoop, argBody, bump, Com.warrs]) (by simp [argLoop, argBody, bump, Com.reads])
  obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ.1, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨σ', hr.mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _), hq, hk⟩

/-! ### The symbol replacing `R_i` -/

set_option maxHeartbeats 2000000 in
theorem pComp_value (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_r" ≤ x.length ∧
        σ.vars "ic_i2" < B ∧ σ.vars "ic_k" < B)
      pComp
      (fun σ σ' => (σ.vars "ic_i2" < sOf x ∧ σ.vars "ic_k" = arOf x (σ.vars "ic_i2") →
          σ'.vars "ic_P" = σ.vars "ic_i2") ∧
        (¬ (σ.vars "ic_i2" < sOf x ∧ σ.vars "ic_k" = arOf x (σ.vars "ic_i2")) →
          σ'.vars "ic_P" = sOf x + σ.vars "ic_r")) 30 := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hh := hdr_lt hd
  unfold pComp
  refine Spec.pre (P := fun σ => (σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧
      σ.vars "ic_r" ≤ x.length ∧ σ.vars "ic_i2" < B ∧ σ.vars "ic_k" < B) ∧
      (σ.vars "ic_i2" < sOf x → 1 + σ.vars "ic_i2" < (σ.arrs "a").length ∧
        (σ.arrs "a").getD (1 + σ.vars "ic_i2") 0 = arOf x (σ.vars "ic_i2") ∧
        arOf x (σ.vars "ic_i2") < B ∧ 1 + σ.vars "ic_i2" < B)) ?_ ?_
  · run_vcg
    all_goals (simp_all [Env.setVar]; try omega)
  · rintro σ ⟨ha, hs, hr, hi2, hk⟩
    exact ⟨⟨ha, hs, hr, hi2, hk⟩, fun hi => ⟨by rw [ha]; omega, by rw [ha]; rfl, getD_lt hB _,
      by omega⟩⟩

theorem pComp_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_r" ≤ x.length ∧
        σ.vars "ic_i2" < B ∧ σ.vars "ic_k" < B)
      pComp
      (fun σ σ' => ((σ.vars "ic_i2" < sOf x ∧ σ.vars "ic_k" = arOf x (σ.vars "ic_i2") →
          σ'.vars "ic_P" = σ.vars "ic_i2") ∧
        (¬ (σ.vars "ic_i2" < sOf x ∧ σ.vars "ic_k" = arOf x (σ.vars "ic_i2")) →
          σ'.vars "ic_P" = sOf x + σ.vars "ic_r")) ∧ Keep ["ic_P"] σ σ' ∧ σ'.out = σ.out) 30 :=
  Spec.keepOut (pComp_value hd hB) _ (by intro y hy; simpa [pComp, Com.wvars] using hy)
    (by simp [pComp, Com.warrs]) (by simp [pComp, Com.reads]) (by simp [pComp, Com.NoWrite])

/-! ### An atom -/

theorem tokAt_rel {p i : ℕ} {ys : List ℕ} (h : TokAt x p (.rel i ys)) :
    p + 3 + ys.length ≤ x.length ∧ x.getD p 0 = 0 ∧ x.getD (p + 1) 0 = i ∧
      x.getD (p + 2) 0 = ys.length ∧ ∀ l < ys.length, x.getD (p + 3 + l) 0 = ys.getD l 0 := by
  obtain ⟨h1, h2⟩ := h
  simp only [Token.code, List.length_cons] at h1 h2
  refine ⟨by omega, by simpa using h2 0 (by omega), by simpa using h2 1 (by omega),
    by simpa using h2 2 (by omega), fun l hl => ?_⟩
  have := h2 (3 + l) (by omega)
  rw [show p + (3 + l) = p + 3 + l by omega] at this
  rw [this, show 3 + l = l + 1 + 1 + 1 by omega]
  simp

set_option maxHeartbeats 4000000 in
theorem relOut_value (hd : Dom x φ) (hB : BOK x B) (p i : ℕ) (ys : List ℕ) (z : ℕ) :
    Spec B (fun σ => Ctx x φ σ ∧ σ.vars "ic_p" = p ∧ σ.vars "ic_z" = z ∧
        TokAt x p (.rel i ys) ∧ z < x.length) relOut
      (fun σ σ' => (i < sOf x ∧ ys.length = arOf x i → σ'.vars "ic_P" = i) ∧
        (¬ (i < sOf x ∧ ys.length = arOf x i) → σ'.vars "ic_P" = sOf x + rOf φ) ∧
        σ'.out = σ.out ++ argList x (sOf x) p (fOf x + z) ys.length ++
          [0, σ'.vars "ic_P", 1, fOf x + z] ∧
        σ'.vars "ic_p" = p + 3 + ys.length ∧ σ'.vars "ic_z" = z + 1 ∧ Ctx x φ σ')
      ((60 + 4) * x.length + 200) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h1 := hz.s_le; have h2 := hz.r_le
  unfold relOut relTail
  refine Spec.pre (P := fun σ => (Ctx x φ σ ∧ σ.vars "ic_p" = p ∧ σ.vars "ic_z" = z ∧
      TokAt x p (.rel i ys) ∧ z < x.length) ∧
      p + 3 + ys.length ≤ x.length ∧ p + 2 < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (p + 1) 0 = i ∧ (σ.arrs "a").getD (p + 2) 0 = ys.length ∧
      i < B ∧ ys.length < B ∧ fOf x + z < B ∧ z + 1 < B ∧ p + 3 + ys.length < B ∧
      sOf x + ys.length < B) ?_ ?_
  · run_vcg [argLoop_spec (B := B) hB, pComp_spec hd hB]
    all_goals (simp only [Ctx, Keep] at *; simp_all [Env.setVar]; try omega)
  · rintro σ ⟨hc, hp, hzz, ht, hzl⟩
    obtain ⟨t1, -, t3, t4, -⟩ := tokAt_rel ht
    have ha := hc.1
    have hi : i < B := by rw [← t3]; exact getD_lt hB _
    refine ⟨⟨hc, hp, hzz, ht, hzl⟩, t1, by rw [ha]; omega, by rw [ha]; exact t3,
      by rw [ha]; exact t4, hi, by omega, by unfold fOf; omega, by omega, by omega, by omega⟩

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutF
