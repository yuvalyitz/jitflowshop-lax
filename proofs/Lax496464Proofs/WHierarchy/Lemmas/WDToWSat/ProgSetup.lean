import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop

/-! # The setup: header, fit test, block positions, `L`, powers

`headCom_spec`: the header of the word; `fitCom_spec`: the test whether the formula fits the
vocabulary; `boCom_spec`: the block positions; `LCom_spec`: the number `L`; `powCom_spec`: the
powers of `n`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgSetup

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop

variable {D : Data} {x : List ℕ} {B : ℕ}

/-! ### The header -/

set_option maxHeartbeats 1000000 in
theorem headCom_spec (hB : BF D x B) (hg : Good x) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) headCom
      (fun σ σ' => σ'.vars "w_sp" = spW x ∧ σ'.vars "w_N" = NW x ∧ σ'.vars "w_k" = kW x ∧
        Frame ["w_sp", "w_N", "w_k"] [] σ σ' ∧ σ'.out = σ.out) 20 := by
  have hh := hg.head
  have hlen := hB.len
  refine Spec.pre (P := fun σ => (σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) ∧
      (σ.arrs "a").length = x.length ∧ (σ.arrs "a").getD 0 0 = spW x ∧
      (σ.arrs "a").getD (1 + spW x) 0 = NW x ∧
      (σ.arrs "a").getD (x.length - 1) 0 = kW x ∧
      spW x < B ∧ NW x < B ∧ kW x < B) ?_ ?_
  · unfold headCom
    run_vcg
    all_goals try (simp [Env.setVar] at *; omega)
    all_goals try (simp_all [Env.setVar]; done)
    have e0 := ‹(σ.arrs "a").getD 0 0 = spW x›
    have e1 := ‹(σ.arrs "a").getD (1 + spW x) 0 = NW x›
    have e2 := ‹(σ.arrs "a").getD (x.length - 1) 0 = kW x›
    have hn := ‹σ.vars "rt_n" = x.length›
    simp only [List.getD_eq_getElem?_getD] at e0 e1 e2
    refine ⟨?_, ?_, ?_, ((Frame.setVar σ (by simp) _).trans (Frame.setVar _ (by simp) _)).trans
      (Frame.setVar _ (by simp) _), rfl⟩ <;> simp [Env.setVar, e0, e1, e2, hn]
  · rintro σ ⟨ha, hn⟩
    exact ⟨⟨ha, hn⟩, by rw [ha], by rw [ha]; rfl, by rw [ha]; rfl, by rw [ha]; rfl,
      hB.getD_lt _, hB.getD_lt _, hB.getD_lt _⟩

/-! ### The fit test -/

/-- One relation atom fits the word. -/
def RelOk (x : List ℕ) (p : ℕ × ℕ) : Prop := p.1 < spW x ∧ x.getD (1 + p.1) 0 = p.2

instance (x : List ℕ) (p : ℕ × ℕ) : Decidable (RelOk x p) := by unfold RelOk; infer_instance

set_option maxHeartbeats 1000000 in
theorem relCheck_spec (hB : BF D x B) (hg : Good x) (p : ℕ × ℕ) (hp : p.1 + p.2 + 1 < B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "w_sp" = spW x) (relCheck p)
      (fun σ σ' => σ'.vars "w_ft" = (if RelOk x p then σ.vars "w_ft" else 0) ∧
        Frame ["w_ft"] [] σ σ' ∧ σ'.out = σ.out) 12 := by
  have hh := hg.head
  have hlen := hB.len
  have hv := hB.getD_lt (1 + p.1)
  refine Spec.pre (P := fun σ => (σ.arrs "a" = x ∧ σ.vars "w_sp" = spW x) ∧
      (σ.arrs "a").length = x.length ∧ (σ.arrs "a").getD (1 + p.1) 0 = x.getD (1 + p.1) 0 ∧
      σ.vars "w_sp" < B) ?_ ?_
  · unfold relCheck
    run_vcg
    · have hs := ‹σ.vars "w_sp" = spW x›
      have hg' := ‹(σ.arrs "a").getD (1 + p.1) 0 = x.getD (1 + p.1) 0›
      have h1 := ‹p.1 < σ.vars "w_sp"›
      have h2 := ‹(σ.arrs "a").getD (1 + p.1) 0 = p.2›
      rw [hs] at h1; rw [hg'] at h2
      exact ⟨by rw [if_pos (show RelOk x p from ⟨h1, h2⟩)], Frame.refl _ _ _, rfl⟩
    · have hg' := ‹(σ.arrs "a").getD (1 + p.1) 0 = x.getD (1 + p.1) 0›
      have h2 := ‹¬(σ.arrs "a").getD (1 + p.1) 0 = p.2›
      rw [hg'] at h2
      exact ⟨by rw [if_neg (show ¬ RelOk x p from fun h => h2 h.2)]; simp [Env.setVar],
        Frame.setVar σ (by simp) _, rfl⟩
    · have hs := ‹σ.vars "w_sp" = spW x›
      have h1 := ‹¬p.1 < σ.vars "w_sp"›
      rw [hs] at h1
      exact ⟨by rw [if_neg (show ¬ RelOk x p from fun h => h1 h.1)]; simp [Env.setVar],
        Frame.setVar σ (by simp) _, rfl⟩
  · rintro σ ⟨ha, hs⟩
    exact ⟨⟨ha, hs⟩, by rw [ha], by rw [ha], by rw [hs]; omega⟩

theorem relChecks_spec (hB : BF D x B) (hg : Good x) : ∀ ps : List (ℕ × ℕ),
    (∀ p ∈ ps, p.1 + p.2 + 1 < B) →
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "w_sp" = spW x) (seqList (ps.map relCheck))
      (fun σ σ' => σ'.vars "w_ft" = (if ∀ p ∈ ps, RelOk x p then σ.vars "w_ft" else 0) ∧
        Frame ["w_ft"] [] σ σ' ∧ σ'.out = σ.out) (12 * ps.length + 1)
  | [], _ => by
    refine (Spec.skip (B := B)).post fun σ σ' _ h => ?_
    subst h; exact ⟨by simp, Frame.refl _ _ _, rfl⟩
  | p :: ps, h => by
    have h1 := relCheck_spec hB hg p (h p (by simp))
    have h2 := relChecks_spec hB hg ps fun q hq => h q (by simp [hq])
    refine Spec.mono (Spec.seq h1 h2 (fun σ σ' hp hq => ⟨by rw [hq.2.1.2.1 _ (by simp)]; exact hp.1,
      by rw [hq.2.1.1 _ (by simp)]; exact hp.2⟩) ?_) (by simp; omega)
    rintro σ σ' σ'' - ⟨e1, f1, o1⟩ ⟨e2, f2, o2⟩
    refine ⟨?_, f1.trans f2, o2.trans o1⟩
    rw [e2, e1]
    by_cases ha : RelOk x p
    · rw [if_pos ha]
      by_cases hb : ∀ q ∈ ps, RelOk x q
      · have hall : ∀ q ∈ p :: ps, RelOk x q := fun q hq => by
          rcases List.mem_cons.mp hq with rfl | hq
          · exact ha
          · exact hb q hq
        rw [if_pos hb, if_pos hall]
      · have hn : ¬ ∀ q ∈ p :: ps, RelOk x q := fun h' => hb fun q hq =>
          h' q (List.mem_cons.mpr (Or.inr hq))
        rw [if_neg hb, if_neg hn]
    · have hn : ¬ ∀ q ∈ p :: ps, RelOk x q := fun h' => ha (h' p (List.mem_cons.mpr (Or.inl rfl)))
      rw [if_neg ha, if_neg hn]; split_ifs <;> rfl

theorem rels_lt (hB : BF D x B) : ∀ p ∈ D.rels, p.1 + p.2 + 1 < B := by
  intro p hp
  have h1 : p.1 + p.2 + 1 ≤ (D.rels.map fun p => p.1 + p.2 + 1).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hp)
  have := hB.const; unfold cD at this; omega

set_option maxHeartbeats 1000000 in
/-- **The fit test.** -/
theorem fitCom_spec (hB : BF D x B) (hg : Good x) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "w_sp" = spW x) (fitCom D)
      (fun σ σ' => σ'.vars "w_ft" = (if fitW D x then 1 else 0) ∧
        Frame ["w_ft"] [] σ σ' ∧ σ'.out = σ.out) (12 * D.rels.length + 4) := by
  have hlen := hB.len
  have h1 : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "w_sp" = spW x)
      (.assign "w_ft" (.lit (if D.sfit then 1 else 0)))
      (fun σ σ' => σ' = σ.setVar "w_ft" (if D.sfit then 1 else 0)) 2 :=
    Spec.assign (f := fun _ => if D.sfit then 1 else 0) fun σ _ =>
      evalB_lit (by split_ifs <;> omega)
  have h2 := relChecks_spec hB hg D.rels (rels_lt hB)
  refine Spec.mono (Spec.seq h1 h2 (fun σ σ' hp hq => by subst hq; exact ⟨hp.1, by simp [Env.setVar, hp.2]⟩) ?_) (by omega)
  rintro σ σ' σ'' - rfl ⟨e2, f2, o2⟩
  refine ⟨?_, (Frame.setVar σ (by simp) _).trans f2, by rw [o2]; rfl⟩
  rw [e2]
  simp only [Env.setVar, if_pos]
  show _ = if (D.sfit = true ∧ ∀ p ∈ D.rels, RelOk x p) then 1 else 0
  by_cases hc : D.sfit = true ∧ ∀ p ∈ D.rels, RelOk x p
  · rw [if_pos hc, if_pos hc.2, if_pos hc.1]
  · rw [if_neg hc]
    by_cases hr : ∀ p ∈ D.rels, RelOk x p
    · rw [if_pos hr, if_neg (fun h => hc ⟨h, hr⟩)]
    · rw [if_neg hr]

/-! ### The block positions -/

/-- The invariant of the loop over the blocks. -/
def BI (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "w_sp" = spW x ∧ σ.vars "w_i" ≤ spW x ∧
    σ.vars "w_p" = boW x (σ.vars "w_i") ∧ (σ.arrs "bo").length = spW x ∧
    ∀ q < σ.vars "w_i", (σ.arrs "bo").getD q 0 = boW x q

set_option maxHeartbeats 2000000 in
theorem boBody_spec (hB : BF D x B) (hg : Good x) :
    Spec B (fun σ => BI x σ ∧ σ.vars "w_i" < spW x) boBody
      (fun σ σ' => BI x σ' ∧ σ'.vars "w_i" = σ.vars "w_i" + 1) 30 := by
  have hh := hg.head
  have hbl := hg.blocks
  have hlen := hB.len
  refine Spec.pre (P := fun σ => (BI x σ ∧ σ.vars "w_i" < spW x) ∧
      σ.vars "w_p" + 1 + (σ.arrs "a").getD (σ.vars "w_p") 0 *
        (σ.arrs "a").getD (1 + σ.vars "w_i") 0 < x.length ∧
      σ.vars "w_p" < (σ.arrs "a").length ∧ 1 + σ.vars "w_i" < (σ.arrs "a").length ∧
      (σ.arrs "a").length < B ∧ (σ.arrs "a").getD (σ.vars "w_p") 0 < B ∧
      (σ.arrs "a").getD (1 + σ.vars "w_i") 0 < B ∧ σ.vars "w_i" < (σ.arrs "bo").length ∧
      σ.vars "w_i" + 1 < B) ?_ ?_
  · unfold boBody
    run_vcg
    all_goals try (simp [Env.setVar, Env.setArr] at *; omega)
    obtain ⟨ha, hs, hle, hp, hbo, hq⟩ := ‹BI x σ›
    have hlt := ‹σ.vars "w_i" < spW x›
    refine ⟨⟨by simp [Env.setVar, Env.setArr, ha], by simp [Env.setVar, Env.setArr, hs],
      by simp [Env.setVar, Env.setArr]; omega, ?_, by simp [Env.setVar, Env.setArr, hbo], ?_⟩,
      by simp [Env.setVar, Env.setArr]⟩
    · simp only [Env.setVar, Env.setArr, if_pos]
      simp [boW, hp, ha]
    · intro q hq'
      simp only [Env.setVar, Env.setArr] at hq' ⊢
      simp only [↓reduceIte] at hq' ⊢
      rcases Nat.lt_or_ge q (σ.vars "w_i") with h | h
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
        exact hq q h
      · have : q = σ.vars "w_i" := by simp at hq'; omega
        subst this
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]
        simp [hp]
  · rintro σ ⟨⟨ha, hs, hle, hp, hbo, hq⟩, hlt⟩
    have hmono := boW_mono x (show σ.vars "w_i" + 1 ≤ spW x by omega)
    have hstep : boW x (σ.vars "w_i" + 1) = boW x (σ.vars "w_i") + 1 +
        x.getD (boW x (σ.vars "w_i")) 0 * x.getD (1 + σ.vars "w_i") 0 := rfl
    refine ⟨⟨⟨ha, hs, hle, hp, hbo, hq⟩, hlt⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha, hp]; omega
    · rw [ha, hp]; omega
    · rw [ha]; omega
    · rw [ha]; omega
    · rw [ha]; exact hB.getD_lt _
    · rw [ha]; exact hB.getD_lt _
    · rw [hbo]; exact hlt
    · omega

theorem boLoop_spec (hB : BF D x B) (hg : Good x) :
    Spec B (fun σ => BI x (σ.setVar "w_i" 0)) boLoop
      (fun _ σ' => BI x σ' ∧ σ'.vars "w_i" = spW x) ((30 + 4) * spW x + 6) := by
  have hh := hg.head
  have hlen := hB.len
  exact Spec.forRangeZero "w_i" "w_sp" (BI x) _ _ (by omega) (fun _ h => h.2.2.1)
    (fun _ h => h.2.1) (boBody_spec hB hg)

set_option maxHeartbeats 1000000 in
/-- **The block positions.** -/
theorem boCom_spec (hB : BF D x B) (hg : Good x) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "w_sp" = spW x ∧ (σ.arrs "bo").length = spW x)
      boCom
      (fun σ σ' => σ'.arrs "bo" = (List.range (spW x)).map (boW x) ∧
        Frame ["w_p", "w_i"] ["bo"] σ σ' ∧ σ'.out = σ.out) (34 * spW x + 12) := by
  have hh := hg.head
  have hlen := hB.len
  have h1 : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "w_sp" = spW x ∧
      (σ.arrs "bo").length = spW x) (.assign "w_p" (.add (.lit 2) (V "w_sp")))
      (fun σ σ' => σ' = σ.setVar "w_p" (2 + spW x)) 4 :=
    Spec.assign (f := fun _ => 2 + spW x) fun σ h => by
      rw [← h.2.1]; exact evalB_bin (evalB_lit (by omega)) (evalB_var (by rw [h.2.1]; omega))
        (by simp; omega)
  have hval : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "w_sp" = spW x ∧
      (σ.arrs "bo").length = spW x) boCom
      (fun _ σ' => σ'.arrs "bo" = (List.range (spW x)).map (boW x)) (34 * spW x + 12) := by
    refine Spec.mono (Spec.seq h1 (boLoop_spec hB hg) (fun σ σ' hp hq => by
      subst hq
      exact ⟨by simp [Env.setVar, hp.1], by simp [Env.setVar, hp.2.1], by simp [Env.setVar],
        by simp [Env.setVar, boW], by simp [Env.setVar, hp.2.2], by simp [Env.setVar]⟩) ?_)
      (by omega)
    rintro σ σ' σ'' - - ⟨⟨-, -, -, -, hbo, hq⟩, hi⟩
    refine List.ext_getElem (by rw [hbo]; simp) fun q h1 h2 => ?_
    have := hq q (by rw [hi]; simpa using h2)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at this
    rw [this]; simp
  exact Spec.framedOut hval _ _ (by simp [boCom, boLoop, boBody, Com.wvars])
    (by simp [boCom, boLoop, boBody, Com.warrs]) (by simp [boCom, boLoop, boBody, Com.reads])
    (by simp [boCom, boLoop, boBody, Com.NoWrite])

/-! ### `L` and the powers -/

set_option maxHeartbeats 1000000 in
theorem LCom_spec (hB : BF D x B) :
    Spec B (fun σ => σ.vars "rt_n" = x.length ∧ σ.vars "w_k" = kW x ∧ σ.vars "w_N" = NW x)
      (LCom D)
      (fun σ σ' => σ'.vars "w_L" = LW D.s D.r x ∧ Frame ["w_t", "w_L"] [] σ σ' ∧
        σ'.out = σ.out) 20 := by
  have ht0 := hB.t0
  have hsB : D.s < B := by have := hB.const; unfold cD at this; omega
  have hrB : D.r < B := by have := hB.const; unfold cD at this; omega
  have hNB := hB.getD_lt (1 + spW x)
  refine Spec.pre (P := fun σ => (σ.vars "rt_n" = x.length ∧ σ.vars "w_k" = kW x ∧
      σ.vars "w_N" = NW x) ∧ σ.vars "rt_n" + D.s * σ.vars "w_k" + D.r < B ∧ σ.vars "w_N" < B ∧
      σ.vars "w_k" < B) ?_ ?_
  · unfold LCom
    run_vcg
    · have hn := ‹σ.vars "rt_n" = x.length›
      have hk := ‹σ.vars "w_k" = kW x›
      have hN := ‹σ.vars "w_N" = NW x›
      refine ⟨?_, (Frame.setVar σ (by simp) _).trans (Frame.setVar _ (by simp) _), rfl⟩
      have hc := ‹σ.vars "rt_n" + D.s * σ.vars "w_k" + D.r < σ.vars "w_N"›
      rw [hn, hk, hN] at hc
      simp [Env.setVar, LW, hn, hk, min_eq_right hc.le]
    · have hn := ‹σ.vars "rt_n" = x.length›
      have hk := ‹σ.vars "w_k" = kW x›
      have hN := ‹σ.vars "w_N" = NW x›
      refine ⟨?_, (Frame.setVar σ (by simp) _).trans (Frame.setVar _ (by simp) _), rfl⟩
      have hc := ‹¬σ.vars "rt_n" + D.s * σ.vars "w_k" + D.r < σ.vars "w_N"›
      rw [hn, hk, hN] at hc
      simp [Env.setVar, LW, hN, min_eq_left (not_lt.mp hc)]
  · rintro σ ⟨hn, hk, hN⟩
    refine ⟨⟨hn, hk, hN⟩, by rw [hn, hk]; exact ht0, by rw [hN]; unfold NW; exact hNB,
      by rw [hk]; unfold kW; exact hB.getD_lt _⟩

theorem powSteps_spec (hB : BF D x B) (v : String) (hv : v ≠ "w_n") : ∀ e, e ≤ D.r + D.s →
    Spec B (fun σ => σ.vars "w_n" = nW D x ∧ σ.vars v = 1) (powSteps v e)
      (fun σ σ' => σ'.vars v = nW D x ^ e ∧ Frame [v] [] σ σ' ∧ σ'.out = σ.out) (6 * e + 1)
  | 0, _ => by
    refine (Spec.skip (B := B)).post fun σ σ' h e => ?_
    subst e; exact ⟨by simp [h.2], Frame.refl _ _ _, rfl⟩
  | e + 1, he => by
    have ih := powSteps_spec hB v hv e (by omega)
    have hlt := hB.npow_lt (e := e + 1) he
    have hnB := hB.n
    have h2 : Spec B (fun σ => σ.vars "w_n" = nW D x ∧ σ.vars v = nW D x ^ e)
        (.assign v (.mul (V v) (V "w_n")))
        (fun σ σ' => σ' = σ.setVar v (nW D x ^ (e + 1))) 4 :=
      Spec.assign (f := fun _ => nW D x ^ (e + 1)) fun σ h => by
        have hle : nW D x ^ e ≤ nW D x ^ (e + 1) ∨ nW D x = 0 := by
          rcases Nat.eq_zero_or_pos (nW D x) with h0 | h0
          · right; exact h0
          · left; exact Nat.pow_le_pow_right h0 (by omega)
        have hvB : nW D x ^ e < B := hB.npow_lt (by omega)
        have := evalB_bin (op := .mul) (evalB_var (x := v) (σ := σ) (B := B) (by rw [h.2]; exact hvB))
          (evalB_var (x := "w_n") (σ := σ) (B := B) (by rw [h.1]; omega)) (by rw [h.1, h.2, Bop.apply_mul, ← pow_succ]; exact hlt)
        rw [h.1, h.2, Bop.apply_mul, ← pow_succ] at this
        exact this
    refine Spec.mono (Spec.seq ih h2 (fun σ σ' hp hq => ⟨by rw [hq.2.1.1 _ (by simp [hv.symm])]; exact hp.1, hq.1⟩) ?_) (by omega)
    rintro σ σ' σ'' - ⟨-, f1, o1⟩ rfl
    exact ⟨by simp [Env.setVar], f1.trans (Frame.setVar σ' (by simp) _), by rw [← o1]; rfl⟩

theorem powCom_spec (hB : BF D x B) (v : String) (hv : v ≠ "w_n") {e : ℕ} (he : e ≤ D.r + D.s) :
    Spec B (fun σ => σ.vars "w_n" = nW D x) (powCom v e)
      (fun σ σ' => σ'.vars v = nW D x ^ e ∧ Frame [v] [] σ σ' ∧ σ'.out = σ.out) (6 * e + 3) := by
  have hlen := hB.len
  have h1 : Spec B (fun σ => σ.vars "w_n" = nW D x) (.assign v (.lit 1))
      (fun σ σ' => σ' = σ.setVar v 1) 2 := Spec.assign (f := fun _ => 1) fun σ _ => evalB_lit (by omega)
  refine Spec.mono (Spec.seq h1 (powSteps_spec hB v hv e he) (fun σ σ' hp hq => by
    subst hq; exact ⟨by simp [Env.setVar, hv.symm, hp], by simp [Env.setVar]⟩) ?_) (by omega)
  rintro σ σ' σ'' - rfl ⟨e2, f2, o2⟩
  exact ⟨e2, (Frame.setVar σ (by simp) _).trans f2, by rw [o2]; rfl⟩

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgSetup
