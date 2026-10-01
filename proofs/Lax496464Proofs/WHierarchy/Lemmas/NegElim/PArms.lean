import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PNeg

/-! # The arms of the walk over the formula

Each arm of `dispatch` handles one kind of token of the pending formula at position `p`, with
polarity `pl`: it writes the start of the translation, moves `p` past the token, and pushes the
polarities of the children onto the stack `st`. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PArms

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLex
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PNeg

variable {x : List ℕ} {p i r c : ℕ}

/-! ### Atoms of relation symbols -/

theorem posRelC_spec (hcode : p + 3 + r ≤ x.length) (hb : 5 * i + 5 < Bv x)
    (hb2 : p + 3 + r + 1 < Bv x) :
    Spec (Bv x) (NC x p i r c) posRelC
      (fun σ σ' => σ'.out = σ.out ++ (Formula.rel (rI i) (ysOf x p r)).encode ∧ Keep negVars σ σ')
      (28 * r + 100) := by
  have hl := len_lt_Bv x
  have h1 : Spec (Bv x) (NC x p i r c) (writes [L 0, RI 1, V "ln"])
      (fun σ σ' => σ'.out = σ.out ++ [0, 5 * i + 1, r] ∧ Keep negVars σ σ') 40 := by
    refine keep_neg ?_ (by intro y hy; simp [writes, Com.wvars] at hy) (by simp [writes, Com.warrs])
      (by simp [writes, Com.reads])
    unfold writes
    run_vcg
    all_goals
      (try simp only [NC, Env.setVar] at *)
      simp_all
    all_goals (try omega)
  have h2 : Spec (Bv x) (NC x p i r c) (wseqOf 0 Y0 (V "ln"))
      (fun σ σ' => σ'.out = σ.out ++ ysOf x p r ∧ Keep negVars σ σ') (28 * r + 40) := by
    obtain ⟨f1, f2, f3⟩ := wseqOf_frame 0 Y0 (V "ln")
    refine keep_neg ?_ f1 f2 f3
    unfold wseqOf
    run_vcg [wseq_spec (x := x) (n := r)]
    all_goals
      (try simp only [NC, Env.setVar] at *)
      simp_all
    all_goals (try omega)
  refine (Spec.seq_out h1 h2 (fun _ _ h hk => h.keep hk)).mono (by omega) |>.post ?_
  rintro σ σ' - ⟨ho, hk⟩
  refine ⟨?_, hk⟩
  rw [ho]; simp [Formula.encode, rI]

/-- The scalars the atom arms assign. -/
def armVars : List String := "fc" :: negVars

theorem fc_step (hbc : c + 2 * r + 1 < Bv x) :
    Spec (Bv x) (NC x p i r c) (.assign "fc" (.add (V "fc") (.mul (L 2) (V "ln"))))
      (fun σ σ' => σ' = σ.setVar "fc" (c + 2 * r)) 6 := by
  have hl := len_lt_Bv x
  have h := Spec.assign (B := Bv x) (P := NC x p i r c) (x := "fc")
    (e := .add (V "fc") (.mul (L 2) (V "ln"))) (f := fun _ => c + 2 * r) (by
      rintro σ ⟨-, -, -, hr, hc⟩
      rw [evalB_bin (evalB_var (by rw [hc]; omega))
        (evalB_bin (evalB_lit (by omega)) (evalB_var (by rw [hr]; omega)) (by simp [hr]; omega))
        (by simp [hc, hr]; omega)]
      simp [hc, hr])
  exact h.mono (by simp)

theorem negRelC_spec (hcode : p + 3 + r ≤ x.length) (hb : 5 * i + 5 < Bv x)
    (hbc : c + 2 * r + 1 < Bv x) (hb2 : p + 3 + r + 1 < Bv x) :
    Spec (Bv x) (NC x p i r c) negRelC
      (fun σ σ' => σ'.out = σ.out ++ (negRel i (ysOf x p r) c).encode ∧
        σ'.vars "fc" = c + 2 * r ∧ Keep armVars σ σ') (Kneg r + 60) := by
  have hl := len_lt_Bv x
  have hcond : ∀ σ, NC x p i r c σ → (Cond.eq (V "ln") (L 0)).evalB (Bv x) σ = some (r == 0) :=
    fun σ h => by rw [evalB_eq_lit (by rw [h.2.2.2.1]; omega) (by omega), h.2.2.2.1]
  have hite : Spec (Bv x) (NC x p i r c) (.ite (.eq (V "ln") (L 0)) (writes [L 0, RI 2, L 0]) negBig)
      (fun σ σ' => σ'.out = σ.out ++ (negRel i (ysOf x p r) c).encode ∧ Keep negVars σ σ')
      (1 + (Cond.eq (V "ln") (L 0)).size + Kneg r) := by
    by_cases hr : r = 0
    · subst hr
      refine Spec.ite_pos (fun σ h => by rw [hcond σ h]; rfl) ?_
      have h1 : Spec (Bv x) (NC x p i 0 c) (writes [L 0, RI 2, L 0])
          (fun σ σ' => σ'.out = σ.out ++ [0, 5 * i + 2, 0] ∧ Keep negVars σ σ') 40 := by
        refine keep_neg ?_ (by intro y hy; simp [writes, Com.wvars] at hy)
          (by simp [writes, Com.warrs]) (by simp [writes, Com.reads])
        unfold writes
        run_vcg
        all_goals
          (try simp only [NC, Env.setVar] at *)
          simp_all
        all_goals (try omega)
      refine (h1.mono (by unfold Kneg; omega)).post ?_
      rintro σ σ' - ⟨ho, hk⟩
      refine ⟨?_, hk⟩
      rw [ho]; simp [negRel, ysOf, seqL, Formula.encode, fI]
    · refine Spec.ite_neg (fun σ h => by rw [hcond σ h]; simp [hr]) ?_
      exact negBig_spec ⟨by omega, hcode, hb, hbc, hb2⟩
  have h := Spec.seq hite (fc_step (p := p) (i := i) hbc) (fun _ _ h hq => h.keep hq.2)
    (fun σ σ' σ'' hσ ⟨ho, hk⟩ h'' => (⟨by rw [h'']; exact ho, by rw [h'']; simp [Env.setVar],
      ⟨fun y hy => by
        rw [h'']; simp only [Env.setVar]
        rw [if_neg (by intro e; exact hy (by simp [armVars, e]))]
        exact hk.1 y (fun hm => hy (by simp [armVars, hm])),
       by rw [h'']; exact hk.2.1, by rw [h'']; exact hk.2.2⟩⟩ :
      σ''.out = σ.out ++ (negRel i (ysOf x p r) c).encode ∧ σ''.vars "fc" = c + 2 * r ∧
        Keep armVars σ σ''))
  exact h.mono (by simp; omega)

/-! ### The arm context -/

/-- The state an arm starts in. -/
def AC (x : List ℕ) (p pl c hh : ℕ) (st : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "p" = p ∧ σ.vars "pl" = pl ∧ σ.vars "fc" = c ∧ σ.vars "h" = hh ∧
    σ.arrs "st" = st

/-- What an arm leaves: the word, the new position, fresh counter, stack height and stack. -/
def AP (x : List ℕ) (p c hh : ℕ) (st : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "p" = p ∧ σ.vars "fc" = c ∧ σ.vars "h" = hh ∧ σ.arrs "st" = st

variable {pl hh : ℕ} {st : List ℕ}

set_option maxHeartbeats 4000000 in
theorem relBr_spec (pol : Bool) (hpl : pl = pb pol) (hi : x.getD (p + 1) 0 = i)
    (hr : x.getD (p + 2) 0 = r) (hcode : p + 3 + r ≤ x.length) (hb : 5 * i + 5 < Bv x)
    (hbc : c + 2 * r + 1 < Bv x) (hb2 : p + 3 + r + 1 < Bv x) :
    Spec (Bv x) (AC x p pl c hh st) relBr
      (fun σ σ' => σ'.out = σ.out ++ (tr pol (.rel i (ysOf x p r)) c).encode ∧
        AP x (p + 3 + r) (c + cnt pol (.rel i (ysOf x p r))) hh st σ')
      (Kneg r + 28 * r + 200) := by
  have hl := len_lt_Bv x
  have hi' : i < Bv x := by omega
  have hsp := posRelC_spec (c := c) hcode hb hb2
  have hsn := negRelC_spec hcode hb hbc hb2
  refine Spec.pre (P := fun σ => AC x p pl c hh st σ ∧ p + 2 < (σ.arrs "a").length ∧
    (σ.arrs "a").getD (p + 1) 0 = i ∧ (σ.arrs "a").getD (p + 2) 0 = r) ?_ ?_
  · unfold relBr
    run_vcg [hsp, hsn]
    all_goals
      (try simp only [AC, AP, NC, Env.setVar] at *)
    all_goals first
      | (find_hyp hK : _ ∧ Keep negVars _ _
         obtain ⟨ho, hkv, hka, -⟩ := hK
         have e1 := hkv "p" (by decide)
         have e2 := hkv "h" (by decide)
         have e3 := hkv "fc" (by decide)
         have e4 := hkv "ln" (by decide)
         have e5 := hkv "pl" (by decide)
         have e6 := congrFun hka "a"
         have e7 := congrFun hka "st"
         clear hkv hka
         simp_all [tr, cnt, pb]
         all_goals (try omega))
      | (find_hyp hK : _ ∧ _ ∧ Keep armVars _ _
         obtain ⟨ho, hfc, hkv, hka, -⟩ := hK
         have e1 := hkv "p" (by decide)
         have e2 := hkv "h" (by decide)
         have e4 := hkv "ln" (by decide)
         have e5 := hkv "pl" (by decide)
         have e6 := congrFun hka "a"
         have e7 := congrFun hka "st"
         clear hkv hka
         simp_all [tr, cnt, pb]
         all_goals (try omega))
      | (simp_all [pb]; try omega)
    all_goals (try omega)
    all_goals (try (cases pol <;> simp_all [pb] <;> omega))
  · rintro σ ⟨ha, hp, hpl', hc, hh', hst⟩
    exact ⟨⟨ha, hp, hpl', hc, hh', hst⟩, by rw [ha]; omega, by rw [ha]; exact hi,
      by rw [ha]; exact hr⟩

set_option maxHeartbeats 4000000 in
theorem svBr_spec (hr : x.getD (p + 1) 0 = r) (hcode : p + 2 + r ≤ x.length)
    (hb2 : p + 2 + r + 1 < Bv x) :
    Spec (Bv x) (AC x p pl c hh st) svBr
      (fun σ σ' => σ'.out = σ.out ++ (Formula.setVar (seqL x 0 (p + 2) r)).encode ∧
        AP x (p + 2 + r) c hh st σ') (28 * r + 100) := by
  have hl := len_lt_Bv x
  refine Spec.pre (P := fun σ => AC x p pl c hh st σ ∧ p + 1 < (σ.arrs "a").length ∧
    (σ.arrs "a").getD (p + 1) 0 = r) ?_ ?_
  · unfold svBr wseqOf writes
    run_vcg [wseq_spec (x := x) (n := r)]
    all_goals
      (try simp only [AC, AP, Env.setVar] at *)
    all_goals first
      | (find_hyp hK : _ ∧ Keep ["wl"] _ _
         obtain ⟨ho, hkv, hka, -⟩ := hK
         have e1 := hkv "p" (by decide)
         have e2 := hkv "h" (by decide)
         have e3 := hkv "fc" (by decide)
         have e4 := hkv "ln" (by decide)
         have e6 := congrFun hka "a"
         have e7 := congrFun hka "st"
         clear hkv hka
         simp_all [Formula.encode]
         all_goals (try omega))
      | (simp_all; try omega)
    all_goals (try omega)
  · rintro σ ⟨ha, hp, hpl', hc, hh', hst⟩
    exact ⟨⟨ha, hp, hpl', hc, hh', hst⟩, by rw [ha]; omega, by rw [ha]; exact hr⟩

set_option maxHeartbeats 4000000 in
theorem eqBr_spec (pol : Bool) (hpl : pl = pb pol) (u v : ℕ) (hu : x.getD (p + 1) 0 = u)
    (hv : x.getD (p + 2) 0 = v) (hcode : p + 3 ≤ x.length) :
    Spec (Bv x) (AC x p pl c hh st) eqBr
      (fun σ σ' => σ'.out = σ.out ++ (tr pol (.eq u v) c).encode ∧ AP x (p + 3) c hh st σ') 100 := by
  have hl := len_lt_Bv x
  have hu' : u < Bv x := by rw [← hu]; exact getD_lt_Bv x _
  have hv' : v < Bv x := by rw [← hv]; exact getD_lt_Bv x _
  refine Spec.pre (P := fun σ => AC x p pl c hh st σ ∧ p + 2 < (σ.arrs "a").length ∧
    (σ.arrs "a").getD (p + 1) 0 = u ∧ (σ.arrs "a").getD (p + 2) 0 = v) ?_ ?_
  · unfold eqBr writes
    run_vcg
    all_goals
      (try simp only [AC, AP, Env.setVar] at *)
      simp_all [tr, Formula.encode, pb]
    all_goals (try omega)
    all_goals (try (cases pol <;> simp_all [pb, tr, Formula.encode] <;> omega))
  · rintro σ ⟨ha, hp, hpl', hc, hh', hst⟩
    exact ⟨⟨ha, hp, hpl', hc, hh', hst⟩, by rw [ha]; omega, by rw [ha]; exact hu, by rw [ha]; exact hv⟩

theorem negBr_spec (hpl : pl ≤ 1) (hst : hh < st.length) (hb : hh + 1 < Bv x) (hbp : p + 1 < Bv x) :
    Spec (Bv x) (AC x p pl c hh st) negBr
      (fun σ σ' => σ'.out = σ.out ∧ AP x (p + 1) c (hh + 1) (st.set hh (1 - pl)) σ') 30 := by
  have hl := len_lt_Bv x
  unfold negBr
  run_vcg
  all_goals
    (try simp only [AC, AP, Env.setVar, Env.setArr] at *)
    simp_all
  all_goals (try omega)

theorem conBr_spec (e : Expr) (ev : ℕ) (he : ∀ σ, AC x p pl c hh st σ → e.evalB (Bv x) σ = some ev)
    (hpl : pl ≤ 1) (hst : hh + 1 < st.length) (hb : hh + 2 < Bv x) (hbp : p + 1 < Bv x) :
    Spec (Bv x) (AC x p pl c hh st) (conBr e)
      (fun σ σ' => σ'.out = σ.out ++ [ev] ∧
        AP x (p + 1) c (hh + 2) ((st.set hh pl).set (hh + 1) pl) σ') (40 + e.size) := by
  have hl := len_lt_Bv x
  unfold conBr
  refine Spec.pre (P := fun σ => AC x p pl c hh st σ ∧ e.evalB (Bv x) σ = some ev) ?_
    (fun σ h => ⟨h, he σ h⟩)
  have hw : Spec (Bv x) (fun σ => AC x p pl c hh st σ ∧ e.evalB (Bv x) σ = some ev) (.write e)
      (fun σ σ' => σ' = { σ with out := σ.out ++ [ev] }) (1 + e.size) :=
    Spec.write (fun σ h => h.2)
  run_vcg [hw]
  all_goals
    (try simp only [AC, AP, Env.setVar, Env.setArr] at *)
    simp_all
  all_goals (try omega)

theorem qBr_spec (tg y : ℕ) (hy : x.getD (p + 1) 0 = y) (hcode : p + 2 ≤ x.length)
    (htg : tg < Bv x) (hpl : pl ≤ 1) (hst : hh < st.length) (hb : hh + 1 < Bv x)
    (hbp : p + 2 < Bv x) :
    Spec (Bv x) (fun σ => AC x p pl c hh st σ ∧ σ.vars "tg" = tg) qBr
      (fun σ σ' => σ'.out = σ.out ++ [tg, y] ∧ AP x (p + 2) c (hh + 1) (st.set hh pl) σ') 40 := by
  have hl := len_lt_Bv x
  have hy' : y < Bv x := by rw [← hy]; exact getD_lt_Bv x _
  refine Spec.pre (P := fun σ => (AC x p pl c hh st σ ∧ σ.vars "tg" = tg) ∧
    p + 1 < (σ.arrs "a").length ∧ (σ.arrs "a").getD (p + 1) 0 = y) ?_ ?_
  · unfold qBr writes
    run_vcg
    all_goals
      (try simp only [AC, AP, Env.setVar, Env.setArr] at *)
      simp_all
    all_goals (try omega)
  · rintro σ ⟨⟨ha, hp, hpl', hc, hh', hst'⟩, htg'⟩
    exact ⟨⟨⟨ha, hp, hpl', hc, hh', hst'⟩, htg'⟩, by rw [ha]; omega, by rw [ha]; exact hy⟩

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PArms
