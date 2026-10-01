import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok

/-! # Phases 5–6: the header of the incidence structure and the blocks of the `P_i`

`headOut_spec`: the vocabulary and the size of the incidence structure; `pOut_spec`: the blocks of
the unary symbols `P_i`, listing the new element of every tuple. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutS

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok

variable {x : List ℕ} {φ : Formula} {B : ℕ}

/-- The values every output phase reads. -/
def Ctx (x : List ℕ) (φ : Formula) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "ic_s" = sOf x ∧ σ.vars "ic_N" = nOf x ∧
    σ.vars "ic_b" = fsOf x ∧ σ.vars "ic_g" = tOf x ∧ σ.vars "ic_F" = fOf x ∧
    σ.vars "ic_q" = nrel φ ∧ σ.vars "ic_r" = rOf φ

/-- The scalars `Ctx` reads. -/
def globals : List String := ["rt_n", "ic_s", "ic_N", "ic_b", "ic_g", "ic_F", "ic_q", "ic_r"]

theorem Ctx.keep {S : List String} {σ σ' : Env} (h : Ctx x φ σ) (hk : Keep S σ σ')
    (hS : ∀ y ∈ globals, y ∉ S) : Ctx x φ σ' := by
  obtain ⟨hv, ha, -⟩ := hk
  have hg : ∀ y ∈ globals, σ'.vars y = σ.vars y := fun y hy => hv y (hS y hy)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨by rw [ha]; exact h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg "rt_n" (by simp [globals])]; exact h2
  · rw [hg "ic_s" (by simp [globals])]; exact h3
  · rw [hg "ic_N" (by simp [globals])]; exact h4
  · rw [hg "ic_b" (by simp [globals])]; exact h5
  · rw [hg "ic_g" (by simp [globals])]; exact h6
  · rw [hg "ic_F" (by simp [globals])]; exact h7
  · rw [hg "ic_q" (by simp [globals])]; exact h8
  · rw [hg "ic_r" (by simp [globals])]; exact h9

/-- The sizes the output phases need. -/
structure Sizes (x : List ℕ) (φ : Formula) : Prop where
  s_le : sOf x + 2 ≤ x.length
  r_le : rOf φ ≤ x.length
  q_le : nrel φ ≤ x.length
  t_le : tOf x + 2 + sOf x ≤ x.length
  n_le : nOf x ≤ maxEntry x

theorem sizes (hd : Dom x φ) : Sizes x φ := by
  have h1 := hd.fs_eq
  have h2 := T_le hd 0
  rw [T_dataOf] at h2
  have h3 := rOf_le_length φ
  have h4 := nrel_le_length φ
  exact ⟨by have := hdr_lt hd; omega, by omega, by omega, by have := fs_le hd; omega,
    getD_le_maxEntry x _⟩

/-! ### A loop writing one number several times -/

/-- `ic_i := 0; while ic_i < m do (write v; ic_i := ic_i + 1)`. -/
def constLoop (m : String) (v : ℕ) : Com :=
  .seq (.assign "ic_i" (.lit 0)) (.while (.lt (V "ic_i") (V m)) (.seq (.write (.lit v)) (bump "ic_i")))

theorem constLoop_value (m : String) (hm : m ≠ "ic_i") (v N : ℕ) (hN : N + 1 < B) (hv : v < B)
    (out0 : List ℕ) :
    Spec B (fun σ => σ.vars m = N ∧ σ.out = out0) (constLoop m v)
      (fun _ σ' => σ'.out = out0 ++ List.replicate N v) ((10 + 4) * N + 6) := by
  have hbody : Spec B (fun σ => (σ.vars m = N ∧ σ.vars "ic_i" ≤ N ∧
        σ.out = out0 ++ List.replicate (σ.vars "ic_i") v) ∧ σ.vars "ic_i" < N)
      (.seq (.write (.lit v)) (bump "ic_i"))
      (fun σ σ' => (σ'.vars m = N ∧ σ'.vars "ic_i" ≤ N ∧
        σ'.out = out0 ++ List.replicate (σ'.vars "ic_i") v) ∧
        σ'.vars "ic_i" = σ.vars "ic_i" + 1) 10 := by
    run_vcg
    all_goals (simp_all [Env.setVar, List.replicate_succ']; try omega)
  refine Spec.post (Spec.pre (Spec.forRangeZero "ic_i" m _ N 10 (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1) hbody) ?_) ?_
  · rintro σ ⟨h1, h2⟩
    simp [Env.setVar, hm, h1, h2]
  · rintro σ σ' - ⟨⟨-, -, ho⟩, hi⟩
    rw [ho, hi]

theorem constLoop_spec (m : String) (hm : m ≠ "ic_i") (v N : ℕ) (hN : N + 1 < B) (hv : v < B) :
    Spec B (fun σ => σ.vars m = N) (constLoop m v)
      (fun σ σ' => σ'.out = σ.out ++ List.replicate N v ∧ Keep ["ic_i"] σ σ')
      ((10 + 4) * N + 6) := by
  intro σ hσ
  have h := Spec.keep (constLoop_value (B := B) m hm v N hN hv σ.out) ["ic_i"]
    (by intro y hy; simpa [constLoop, bump, Com.wvars] using hy)
    (by simp [constLoop, bump, Com.warrs]) (by simp [constLoop, bump, Com.reads])
  obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
  exact ⟨σ', hr, hq, hk⟩

/-! ### The header of the incidence structure -/

/-- What `headOut` writes. -/
def headList (x : List ℕ) (φ : Formula) : List ℕ :=
  [sOf x + rOf φ] ++ List.replicate (sOf x) 1 ++ List.replicate (rOf φ) 2 ++ [nOf x + tOf x]

/-- The cost of `headOut`. -/
def Khead (x : List ℕ) : ℕ := 40 * x.length + 40

set_option maxHeartbeats 2000000 in
theorem headOut_value (hd : Dom x φ) (hB : BOK x B) :
    Spec B (Ctx x φ) headOut (fun σ σ' => σ'.out = σ.out ++ headList x φ) (Khead x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h1 := hz.s_le; have h2 := hz.r_le; have h3 := hz.t_le; have h4 := hz.n_le
  have hs := constLoop_spec (B := B) "ic_s" (by decide) 1 (sOf x) (by omega) (by omega)
  have hr := constLoop_spec (B := B) "ic_r" (by decide) 2 (rOf φ) (by omega) (by omega)
  refine Spec.mono (c := headOut) (K := 3 + (14 * sOf x + 6) + ((14 * rOf φ + 6) + 5)) ?_ ?_
  · unfold headOut
    run_vcg [(show onesLoop = constLoop "ic_s" 1 from rfl) ▸ hs,
      (show twosLoop = constLoop "ic_r" 2 from rfl) ▸ hr]
    all_goals (simp only [Ctx, Keep, headList] at *; simp_all; try omega)
  · unfold Khead; omega

theorem headOut_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (Ctx x φ) headOut (fun σ σ' => σ'.out = σ.out ++ headList x φ ∧ Keep ["ic_i"] σ σ')
      (Khead x) :=
  Spec.keep (headOut_value hd hB) _
    (by intro y hy; simpa [headOut, onesLoop, twosLoop, bump, Com.wvars] using hy)
    (by simp [headOut, onesLoop, twosLoop, bump, Com.warrs])
    (by simp [headOut, onesLoop, twosLoop, bump, Com.reads])

/-! ### The blocks of the `P_i` -/

/-- The entries of the block of `P_i`. -/
def pf (x : List ℕ) (i : ℕ) : List ℕ := (List.range (cntOf x i)).map fun j => nOf x + poOf x i + j

/-- What `pOut` writes. -/
def pList' (x : List ℕ) (k : ℕ) : List ℕ := (List.range k).flatMap fun i => cntOf x i :: pf x i

theorem pElemLoop_value (N g c : ℕ) (hc : N + g + c + 1 < B) (out0 : List ℕ) :
    Spec B (fun σ => σ.vars "ic_N" = N ∧ σ.vars "ic_g2" = g ∧ σ.vars "ic_c" = c ∧ σ.out = out0)
      pElemLoop (fun _ σ' => σ'.out = out0 ++ (List.range c).map fun j => N + g + j)
      ((20 + 4) * c + 6) := by
  have hbody : Spec B (fun σ => (σ.vars "ic_N" = N ∧ σ.vars "ic_g2" = g ∧ σ.vars "ic_c" = c ∧
        σ.vars "ic_j" ≤ c ∧ σ.out = out0 ++ (List.range (σ.vars "ic_j")).map fun j => N + g + j) ∧
        σ.vars "ic_j" < c) pElemBody
      (fun σ σ' => (σ'.vars "ic_N" = N ∧ σ'.vars "ic_g2" = g ∧ σ'.vars "ic_c" = c ∧
        σ'.vars "ic_j" ≤ c ∧ σ'.out = out0 ++ (List.range (σ'.vars "ic_j")).map fun j => N + g + j) ∧
        σ'.vars "ic_j" = σ.vars "ic_j" + 1) 20 := by
    unfold pElemBody
    run_vcg
    all_goals (simp_all [Env.setVar, List.range_succ]; try omega)
  refine Spec.post (Spec.pre (Spec.forRangeZero "ic_j" "ic_c" _ c 20 (by omega)
    (fun σ h => h.2.2.2.1) (fun σ h => h.2.2.1) hbody) ?_) ?_
  · rintro σ ⟨h1, h2, h3, h4⟩
    simp [Env.setVar, h1, h2, h3, h4]
  · rintro σ σ' - ⟨⟨-, -, -, -, ho⟩, hj⟩
    rw [ho, hj]

theorem pElemLoop_spec (L : ℕ) :
    Spec B (fun σ => σ.vars "ic_N" + σ.vars "ic_g2" + σ.vars "ic_c" + 1 < B ∧ σ.vars "ic_c" ≤ L)
      pElemLoop
      (fun σ σ' => σ'.out = σ.out ++
        ((List.range (σ.vars "ic_c")).map fun j => σ.vars "ic_N" + σ.vars "ic_g2" + j) ∧
        Keep ["ic_j"] σ σ')
      ((20 + 4) * L + 6) := by
  intro σ hσ
  have h := Spec.keep (pElemLoop_value (B := B) (σ.vars "ic_N") (σ.vars "ic_g2") (σ.vars "ic_c")
    hσ.1 σ.out) ["ic_j"]
    (by intro y hy; simpa [pElemLoop, pElemBody, bump, Com.wvars] using hy)
    (by simp [pElemLoop, pElemBody, bump, Com.warrs]) (by simp [pElemLoop, pElemBody, bump, Com.reads])
  obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨rfl, rfl, rfl, rfl⟩
  exact ⟨σ', hr.mono (Nat.add_le_add_right (Nat.mul_le_mul_left _ hσ.2) _), hq, hk⟩

/-- The invariant of the walk writing the blocks of the `P_i`. -/
def PO (x : List ℕ) (φ : Formula) (out0 : List ℕ) (σ : Env) : Prop :=
  Ctx x φ σ ∧ σ.vars "ic_i" ≤ sOf x ∧ σ.vars "ic_b2" = bo x (σ.vars "ic_i") ∧
    σ.vars "ic_g2" = poOf x (σ.vars "ic_i") ∧ σ.out = out0 ++ pList' x (σ.vars "ic_i")

theorem pList'_succ (x : List ℕ) (i : ℕ) :
    pList' x (i + 1) = pList' x i ++ (cntOf x i :: pf x i) := by
  simp [pList', List.range_succ]

set_option maxHeartbeats 4000000 in
theorem pBody_spec (hd : Dom x φ) (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => PO x φ out0 σ ∧ σ.vars "ic_i" < sOf x) pBody
      (fun σ σ' => PO x φ out0 σ' ∧ σ'.vars "ic_i" = σ.vars "ic_i" + 1)
      ((20 + 4) * x.length + 60) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h1 := hz.s_le; have h3 := hz.t_le; have h4 := hz.n_le
  unfold pBody
  refine Spec.pre (P := fun σ => PO x φ out0 σ ∧ σ.vars "ic_i" < sOf x ∧
      σ.vars "ic_b2" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (σ.vars "ic_b2") 0 = cntOf x (σ.vars "ic_i") ∧
      1 + σ.vars "ic_i" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (1 + σ.vars "ic_i") 0 = arOf x (σ.vars "ic_i") ∧
      cntOf x (σ.vars "ic_i") < B ∧ arOf x (σ.vars "ic_i") < B ∧
      nOf x + poOf x (σ.vars "ic_i") + cntOf x (σ.vars "ic_i") + 1 < B ∧
      σ.vars "ic_b2" + 1 < B ∧ cntOf x (σ.vars "ic_i") * arOf x (σ.vars "ic_i") < B ∧
      σ.vars "ic_b2" + 1 + cntOf x (σ.vars "ic_i") * arOf x (σ.vars "ic_i") < B ∧
      1 + σ.vars "ic_i" < B ∧ σ.vars "ic_i" + 1 < B ∧ cntOf x (σ.vars "ic_i") ≤ x.length) ?_ ?_
  · run_vcg [pElemLoop_spec (B := B) x.length]
    all_goals (simp only [PO, Ctx, Keep] at *; simp_all [Env.setVar, bo_succ, poOf_succ, pList'_succ, pf]; try omega)
  · rintro σ ⟨⟨hc, hi, hbo, hg, ho⟩, hlt⟩
    have ha := hc.1
    have hh1 := bo_lt hd (i := σ.vars "ic_i") (by omega)
    have hh2 := bo_succ_le hd (i := σ.vars "ic_i") (by omega)
    have hh3 := po_le_bo hd 0 (σ.vars "ic_i" + 1) (by omega)
    have hh4 := po_le_bo hd 0 (sOf x) le_rfl
    rw [po_dataOf, poOf_succ] at hh3
    rw [po_dataOf] at hh4
    have hmono := bo_mono x (show σ.vars "ic_i" + 1 ≤ sOf x by omega)
    have hpm : poOf x (σ.vars "ic_i" + 1) ≤ poOf x (sOf x) :=
      (dataOf x 0).po_mono (show σ.vars "ic_i" + 1 ≤ sOf x by omega)
    rw [poOf_succ] at hpm
    rw [bo_succ] at hh2
    have hfs := fs_le hd
    have hcn := getD_lt hB (bo x (σ.vars "ic_i"))
    have har := getD_lt hB (1 + σ.vars "ic_i")
    unfold tOf at h3
    refine ⟨⟨hc, hi, hbo, hg, ho⟩, hlt, ?_, ?_, ?_, ?_, hcn, har, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ha, hbo]; exact hh1
    · rw [ha, hbo]; rfl
    · rw [ha]; omega
    · rw [ha]; rfl
    · omega
    · rw [hbo]; omega
    · omega
    · rw [hbo]; omega
    · omega
    · omega
    · omega

/-- The cost of `pOut`. -/
def Kp (x : List ℕ) : ℕ := 10 + (((20 + 4) * x.length + 60) + 4) * sOf x + 6

theorem pOut_value (hd : Dom x φ) (hB : BOK x B) (out0 : List ℕ) :
    Spec B (fun σ => Ctx x φ σ ∧ σ.out = out0) pOut
      (fun _ σ' => Ctx x φ σ' ∧ σ'.out = out0 ++ pList' x (sOf x)) (Kp x) := by
  have hb : maxEntry x + 2 * x.length + 8 < B := hB
  have hz := sizes hd
  have h1 := hz.s_le
  have hloop := Spec.forRangeZero (B := B) (c := pBody) "ic_i" "ic_s" (PO x φ out0) (sOf x)
    ((20 + 4) * x.length + 60) (by omega) (fun σ h => h.2.1) (fun σ h => h.1.2.2.1) (pBody_spec hd hB out0)
  unfold pOut Kp
  run_vcg [hloop]
  all_goals (simp only [PO, Ctx] at *; simp_all [Env.setVar, bo_zero]; try omega)
  all_goals (simp [pList', poOf])

theorem pOut_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (Ctx x φ) pOut
      (fun σ σ' => σ'.out = σ.out ++ pList' x (sOf x) ∧
        Keep ["ic_g2", "ic_b2", "ic_i", "ic_c", "ic_j"] σ σ') (Kp x) := by
  intro σ hσ
  have h := Spec.keep (pOut_value hd hB σ.out) ["ic_g2", "ic_b2", "ic_i", "ic_c", "ic_j"]
    (by intro y hy; simp [pOut, pLoop, pBody, pElemLoop, pElemBody, bump, Com.wvars] at hy
        simp; tauto)
    (by simp [pOut, pLoop, pBody, pElemLoop, pElemBody, bump, Com.warrs])
    (by simp [pOut, pLoop, pBody, pElemLoop, pElemBody, bump, Com.reads])
  obtain ⟨σ', hr, hq, hk⟩ := h σ ⟨hσ, rfl⟩
  exact ⟨σ', hr, hq.2, hk⟩

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutS
