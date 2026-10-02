import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok3

/-!
# Σ₁[2] Model Checking to Clique: the Tokenizer Loop

After `|x|` turns the machine holds `tok x` (`tokz_spec`).
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTokLoop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok1 Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok2
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTok3

/-! ### Shape of the tokenizer states -/

/-- The shape facts every tokenizer state has. -/
def Shape (st : TS) : Prop :=
  st.ab.length ≤ st.nd.length ∧ st.vs.length = 2 * st.ab.length ∧ st.ar.length = st.ab.length

theorem shape_step (x : List ℕ) {st : TS} (h : Shape st) :
    Shape (tokStep x st) ∧ (tokStep x st).nd.length ≤ st.nd.length + 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold tokStep
  split_ifs
  · exact ⟨⟨h1, h2, h3⟩, by simp⟩
  · simp only [Shape, relStep, List.length_append, List.length_cons, List.length_nil]; omega
  · simp only [Shape, eqStep, List.length_append, List.length_cons, List.length_nil]; omega
  · simp only [Shape, otherStep, List.length_append, List.length_cons, List.length_nil]; omega
  · exact ⟨⟨h1, h2, h3⟩, le_refl _ |>.trans (by omega)⟩

theorem shape_iter (x : List ℕ) : ∀ n, Shape ((tokStep x)^[n] (tokInit x)) ∧
    ((tokStep x)^[n] (tokInit x)).nd.length ≤ n
  | 0 => by simp [Shape, tokInit]
  | n + 1 => by
    obtain ⟨h1, h2⟩ := shape_iter x n
    rw [Function.iterate_succ_apply']
    obtain ⟨h3, h4⟩ := shape_step x h1
    exact ⟨h3, by omega⟩

theorem p_step (x : List ℕ) {st : TS} (h : st.p ≤ 2 * x.length + 2) :
    (tokStep x st).p ≤ 2 * x.length + 2 := by
  unfold tokStep
  split_ifs
  · simp; omega
  · simp only [relStep]; split_ifs <;> omega
  · simp only [eqStep]; omega
  · simp only [otherStep]; omega
  · exact h

theorem p_iter (x : List ℕ) : ∀ n, ((tokStep x)^[n] (tokInit x)).p ≤ 2 * x.length + 2
  | 0 => by simp [tokInit]; have := hp_le x (sX x); omega
  | n + 1 => by rw [Function.iterate_succ_apply']; exact p_step x (p_iter x n)

theorem tok_shape (x : List ℕ) : Shape (tok x) ∧ (tok x).nd.length ≤ x.length :=
  shape_iter x x.length

/-! ### The loop -/

theorem corr_setVar {x : List ℕ} {st : TS} {σ : Env} (h : Corr x st σ) (y : String) (v : ℕ)
    (hy : y ∉ ["rt_n", "zs", "zp", "zT", "zq", "zfl"]) : Corr x st (σ.setVar y v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  refine ⟨h1, ?_, ?_, h4, ?_, ?_, ?_, ?_, h9, h10, h11, h12, h13⟩ <;>
    simp [Ne.symm hy.1, Ne.symm hy.2.1, Ne.symm hy.2.2.1, Ne.symm hy.2.2.2.1,
      Ne.symm hy.2.2.2.2.1, Ne.symm hy.2.2.2.2.2, *]

/-- The loop invariant. -/
def TI (x : List ℕ) (σ : Env) : Prop :=
  σ.vars "ztt" ≤ x.length ∧ Corr x ((tokStep x)^[σ.vars "ztt"] (tokInit x)) σ

set_option maxHeartbeats 2000000 in
theorem tokBody_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => TI x σ ∧ σ.vars "ztt" < x.length) tokBody
      (fun σ σ' => TI x σ' ∧ σ'.vars "ztt" = σ.vars "ztt" + 1) 280 := by
  have hL := HB.len hB
  intro σ ⟨⟨hle, hc⟩, hlt⟩
  set st := (tokStep x)^[σ.vars "ztt"] (tokInit x) with hst
  obtain ⟨hsh, hndl⟩ := shape_iter x (σ.vars "ztt")
  rw [← hst] at hsh hndl
  have hn : σ.vars "rt_n" = x.length := hc.2.1
  have hp : σ.vars "zp" = st.p := hc.2.2.2.2.1
  have hnext : (tokStep x)^[σ.vars "ztt" + 1] (tokInit x) = tokStep x st := by
    rw [Function.iterate_succ_apply']
  have hcond : (Cond.lt (V "zp") (V "rt_n")).evalB B σ = some (decide (st.p < x.length)) := by
    have := evalB_condLt (B := B) (evalB_var (x := "zp") (σ := σ) (B := B)
        (by rw [hp]; have := p_iter x (σ.vars "ztt"); rw [← hst] at this; omega))
      (evalB_var (x := "rt_n") (σ := σ) (by omega))
    rw [this, hp, hn]
  have hbump : ∀ τ : Env, τ.vars "ztt" = σ.vars "ztt" →
      Run B (bump "ztt") τ (τ.setVar "ztt" (σ.vars "ztt" + 1)) 4 := by
    intro τ hτ
    have hv : (Expr.add (V "ztt") (.lit 1)).evalB B τ = some (σ.vars "ztt" + 1) := by
      have := evalB_bin (op := .add) (evalB_var (x := "ztt") (σ := τ) (B := B) (by omega))
        (evalB_lit (n := 1) (σ := τ) (B := B) (by omega)) (by simp; omega)
      rw [hτ] at this; exact this
    have := Run.assign (x := "ztt") hv
    simpa using this
  by_cases hpL : st.p < x.length
  · obtain ⟨σ1, r1, h1⟩ := tokStepC_spec hB st σ (corrX_of hc hpL ⟨by omega, hsh.1, hsh.2.1, hsh.2.2⟩)
    have hz1 : σ1.vars "ztt" = σ.vars "ztt" := by
      have := r1.frame_var "ztt" (by simp [tokStepC, relC, eqC, otherC, relVars, relSym, pushNode,
        pushVars, rdV, bump, Com.wvars])
      exact this
    refine ⟨_, ((Run.ite_true (by rw [hcond]; simp [hpL]) r1).seq (hbump σ1 hz1)).mono
      (by simp), ⟨by simp; omega, ?_⟩, by simp⟩
    simp only [vars_setVar, ↓reduceIte]
    rw [hnext]
    exact corr_setVar h1 "ztt" _ (by decide)
  · have hst' : tokStep x st = st := by simp only [tokStep, if_neg hpL]
    refine ⟨_, ((Run.ite_false (by rw [hcond]; simp [hpL]) Run.skip).seq (hbump σ rfl)).mono
      (by simp), ⟨by simp; omega, ?_⟩, by simp⟩
    simp only [vars_setVar, ↓reduceIte]
    rw [hnext, hst']
    exact corr_setVar hc "ztt" _ (by decide)

theorem tokLoop_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => TI x (σ.setVar "ztt" 0)) tokLoop
      (fun _ σ' => TI x σ' ∧ σ'.vars "ztt" = x.length) ((280 + 4) * x.length + 6) := by
  have hL := HB.len hB
  exact Spec.forRangeZero "ztt" "rt_n" (TI x) x.length 280 (by omega) (fun _ h => h.1)
    (fun _ h => h.2.2.1) (tokBody_spec hB)

set_option maxHeartbeats 2000000 in
/-- **The tokenizer.** From the header's state, the machine ends holding `tok x`. -/
theorem tokz_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zs" = sX x ∧
        σ.arrs "bs" = pad (bsL x (sX x)) (sX x) ∧ σ.vars "zp" = hp x (sX x) ∧
        σ.arrs "nt" = List.replicate (x.length + 1) 0 ∧
        σ.arrs "na" = List.replicate (x.length + 1) 0 ∧
        σ.arrs "vs" = List.replicate (2 * x.length + 2) 0 ∧
        σ.arrs "ab" = List.replicate (x.length + 1) 0 ∧
        σ.arrs "ar" = List.replicate (x.length + 1) 0) tokz
      (fun _ σ' => Corr x (tok x) σ') ((280 + 4) * x.length + 20) := by
  have hL := HB.len hB
  unfold tokz
  have h1 : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zs" = sX x ∧
        σ.arrs "bs" = pad (bsL x (sX x)) (sX x) ∧ σ.vars "zp" = hp x (sX x) ∧
        σ.arrs "nt" = List.replicate (x.length + 1) 0 ∧
        σ.arrs "na" = List.replicate (x.length + 1) 0 ∧
        σ.arrs "vs" = List.replicate (2 * x.length + 2) 0 ∧
        σ.arrs "ab" = List.replicate (x.length + 1) 0 ∧
        σ.arrs "ar" = List.replicate (x.length + 1) 0)
      (.seq (.assign "zT" (.lit 0)) (.seq (.assign "zq" (.lit 0)) (.assign "zfl" (.lit 1))))
      (fun σ σ' => σ' = ((σ.setVar "zT" 0).setVar "zq" 0).setVar "zfl" 1) 12 := by
    run_vcg
    simp_all
  have h3 := Spec.seq (R := fun _ σ' => TI x σ' ∧ σ'.vars "ztt" = x.length) h1 (tokLoop_spec hB)
    (by
      rintro σ σ' ⟨ha, hn, hs, hbs, hp, hnt, hna, hvs, hab, har⟩ rfl
      refine ⟨by simp, ?_⟩
      simp only [vars_setVar, ↓reduceIte, Function.iterate_zero, id]
      refine ⟨by simp [ha], by simp [hn], by simp [hs], by simp [hbs], by simp [hp, tokInit],
        by simp [tokInit], by simp [tokInit], by simp [tokInit], ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [tokInit, pad_nil, hnt, hna, hvs, hab, har])
    (fun _ _ _ _ _ h => h)
  refine Spec.mono (K := 12 + ((280 + 4) * x.length + 6)) (h3.post ?_) (by omega)
  rintro σ σ' - ⟨hI, htt⟩
  have := hI.2
  rw [htt] at this
  exact this

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTokLoop
