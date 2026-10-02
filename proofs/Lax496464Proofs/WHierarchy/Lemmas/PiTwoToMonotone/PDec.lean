import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PCtx

/-!
# The Decision on an `X`-Atom and the Conflict Test

`decCom_spec`: with the block `bl` and values `vl` in `bd1, vd1` and the code `u` in `w_c`,
`decCom` sets `w_f` to `1` if `Blocks.dec` decides `u ∈ t`, to `0` otherwise, and sets `g_und` if it
decides nothing. `cfCom_spec`: `g_cf` is `1` iff the blocks with values in `bd1, vd1, bd2, vd2` are
in `Blocks.Conflict`. Each existential over slots is a loop setting a flag; one over pairs of slots
runs over `i < D·D` with `j = i / D`, `j2 = i % D`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDec

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx (Frame Frame.refl Frame.trans Frame.mono Frame.setVar)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PGen

variable {B : ℕ}

/-- Some `i < n` satisfies `p`, as a recursion the loops follow step by step. -/
def anyUpTo (p : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | i + 1 => anyUpTo p i || p i

theorem anyUpTo_iff (p : ℕ → Bool) : ∀ n, anyUpTo p n = true ↔ ∃ i < n, p i = true
  | 0 => by simp [anyUpTo]
  | n + 1 => by
    rw [anyUpTo, Bool.or_eq_true, anyUpTo_iff p n]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

/-- A flag as a number. -/
abbrev bn (b : Bool) : ℕ := if b then 1 else 0

theorem exists_pair_iff (D : ℕ) (P : ℕ → ℕ → Prop) :
    (∃ i < D * D, P (i / D) (i % D)) ↔ ∃ j < D, ∃ j2 < D, P j j2 := by
  constructor
  · rintro ⟨i, hi, h⟩
    have hD : 0 < D := by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · subst h0; simp at hi
      · exact h0
    exact ⟨i / D, (Nat.div_lt_iff_lt_mul hD).mpr hi, i % D, Nat.mod_lt _ hD, h⟩
  · rintro ⟨j, hj, j2, hj2, h⟩
    refine ⟨j * D + j2, ?_, ?_⟩
    · have : (j + 1) * D ≤ D * D := by rw [Nat.mul_comm D D]; exact Nat.mul_le_mul_right _ hj
      rw [Nat.succ_mul] at this; omega
    · have hD : 0 < D := by omega
      have e1 : (j * D + j2) / D = j := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hD, Nat.div_eq_of_lt hj2, zero_add]
      have e2 : (j * D + j2) % D = j2 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj2]
      rw [e1, e2]; exact h

theorem div_mod_lt {i D : ℕ} (h : i < D * D) : i / D < D ∧ i % D < D := by
  have hD : 0 < D := by
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · subst h0; simp at h
    · exact h0
  exact ⟨(Nat.div_lt_iff_lt_mul hD).mpr h, Nat.mod_lt _ hD⟩

theorem bn_le_one (b : Bool) : bn b ≤ 1 := by unfold bn; split <;> omega

/-! ### The context of the decision -/

/-- The arrays and scalars the decision reads. -/
def DA (k D u : ℕ) (bl vl : List ℕ) (σ : Env) : Prop :=
  σ.arrs "bd1" = bl ∧ σ.arrs "vd1" = vl ∧ σ.vars "w_k" = k ∧ σ.vars "w_c" = u ∧
    σ.vars "g_D" = D ∧ σ.vars "g_DD" = D * D

/-- A used slot with the value `u`. -/
def pT (k u : ℕ) (bl vl : List ℕ) (j : ℕ) : Bool := decide (g bl j < k ∧ g vl j = u)

/-- A slot showing `u` below index `0` or above index `k-1`. -/
def pF1 (k u : ℕ) (bl vl : List ℕ) (j : ℕ) : Bool :=
  decide (g bl j = 0 ∧ u < g vl j) || decide (g bl j + 1 = k ∧ g vl j < u)

/-- Two slots, the pair `i`, showing `u` between consecutive indices. -/
def pF2 (k u D : ℕ) (bl vl : List ℕ) (i : ℕ) : Bool :=
  decide (g bl (i / D) + 1 = g bl (i % D) ∧ g bl (i % D) < k ∧ g vl (i / D) < u ∧
    u < g vl (i % D))

/-- The bounds the decision needs. -/
structure DB (B k D u : ℕ) (bl vl : List ℕ) : Prop where
  hbl : bl.length = D
  hvl : vl.length = D
  hk : k + 1 < B
  hu : u + 1 < B
  hD : D * D + D + 1 < B
  hb : ∀ j, bl.getD j 0 + 1 < B
  hv : ∀ j, vl.getD j 0 + 1 < B

/-! ### The bodies, relative to the state -/

set_option maxHeartbeats 2000000 in
theorem tBody_spec :
    Spec B (fun σ => σ.vars "g_j" < (σ.arrs "bd1").length ∧ σ.vars "g_j" < (σ.arrs "vd1").length ∧
        (σ.arrs "bd1").getD (σ.vars "g_j") 0 < B ∧ (σ.arrs "vd1").getD (σ.vars "g_j") 0 < B ∧
        σ.vars "w_k" < B ∧ σ.vars "w_c" < B ∧ 1 < B ∧ σ.vars "g_j" < B)
      tBody
      (fun σ σ' => σ'.vars "g_fT" =
          (if (σ.arrs "bd1").getD (σ.vars "g_j") 0 < σ.vars "w_k" ∧ (σ.arrs "vd1").getD (σ.vars "g_j") 0 = σ.vars "w_c" then 1
            else σ.vars "g_fT") ∧ Frame ["g_fT"] [] σ σ' ∧ σ'.out = σ.out) 20 := by
  unfold tBody setIf
  run_vcg
  all_goals refine ⟨?_, ?_, rfl⟩
  all_goals first
    | exact Frame.refl _ _ _
    | exact Frame.setVar σ (by simp) _
    | (simp only [Env.setVar, if_true]; split_ifs <;> omega)
    | (split_ifs <;> omega)

set_option maxHeartbeats 2000000 in
theorem f1Body_spec :
    Spec B (fun σ => σ.vars "g_j" < (σ.arrs "bd1").length ∧ σ.vars "g_j" < (σ.arrs "vd1").length ∧
        (σ.arrs "bd1").getD (σ.vars "g_j") 0 + 1 < B ∧ (σ.arrs "vd1").getD (σ.vars "g_j") 0 < B ∧
        σ.vars "w_k" < B ∧ σ.vars "w_c" < B ∧ σ.vars "g_j" < B)
      f1Body
      (fun σ σ' => σ'.vars "g_fF" =
          (if ((σ.arrs "bd1").getD (σ.vars "g_j") 0 = 0 ∧ σ.vars "w_c" < (σ.arrs "vd1").getD (σ.vars "g_j") 0) ∨
              ((σ.arrs "bd1").getD (σ.vars "g_j") 0 + 1 = σ.vars "w_k" ∧ (σ.arrs "vd1").getD (σ.vars "g_j") 0 < σ.vars "w_c") then 1
            else σ.vars "g_fF") ∧ Frame ["g_fF"] [] σ σ' ∧ σ'.out = σ.out) 40 := by
  unfold f1Body setIf
  run_vcg
  all_goals try (simp [Env.setVar] at *; omega)
  all_goals refine ⟨?_, ?_, rfl⟩
  all_goals first
    | exact Frame.refl _ _ _
    | exact Frame.setVar σ (by simp) _
    | (simp only [Env.setVar, if_true, String.reduceEq, if_false] at *; split_ifs <;> omega)
    | (split_ifs <;> omega)

set_option maxHeartbeats 4000000 in
theorem f2Test_spec :
    Spec B (fun σ => σ.vars "g_j" < (σ.arrs "bd1").length ∧ σ.vars "g_j" < (σ.arrs "vd1").length ∧
        σ.vars "g_j2" < (σ.arrs "bd1").length ∧ σ.vars "g_j2" < (σ.arrs "vd1").length ∧
        (σ.arrs "bd1").getD (σ.vars "g_j") 0 + 1 < B ∧ (σ.arrs "vd1").getD (σ.vars "g_j") 0 < B ∧ (σ.arrs "bd1").getD (σ.vars "g_j2") 0 < B ∧
        (σ.arrs "vd1").getD (σ.vars "g_j2") 0 < B ∧ σ.vars "w_k" < B ∧ σ.vars "w_c" < B ∧
        σ.vars "g_j" < B ∧ σ.vars "g_j2" < B)
      f2Test
      (fun σ σ' => σ'.vars "g_fF" =
          (if (σ.arrs "bd1").getD (σ.vars "g_j") 0 + 1 = (σ.arrs "bd1").getD (σ.vars "g_j2") 0 ∧ (σ.arrs "bd1").getD (σ.vars "g_j2") 0 < σ.vars "w_k" ∧
              (σ.arrs "vd1").getD (σ.vars "g_j") 0 < σ.vars "w_c" ∧ σ.vars "w_c" < (σ.arrs "vd1").getD (σ.vars "g_j2") 0 then 1
            else σ.vars "g_fF") ∧ Frame ["g_fF"] [] σ σ' ∧ σ'.out = σ.out) 40 := by
  unfold f2Test setIf
  run_vcg
  all_goals refine ⟨?_, ?_, rfl⟩
  all_goals first
    | exact Frame.refl _ _ _
    | exact Frame.setVar σ (by simp) _
    | (simp only [Env.setVar, if_true]; split_ifs <;> omega)
    | (split_ifs <;> omega)

set_option maxHeartbeats 1000000 in
theorem splitI_spec {i D : ℕ} (hiB : i < B) (hDB : D < B) :
    Spec B (fun σ => σ.vars "g_i" = i ∧ σ.vars "g_D" = D) splitI
      (fun σ σ' => σ' = (σ.setVar "g_j" (i / D)).setVar "g_j2" (i % D)) 10 := by
  have h1 : i / D ≤ i := Nat.div_le_self i D
  have h2 : i / D * D ≤ i := Nat.div_mul_le_self i D
  refine Spec.pre (P := fun σ => (σ.vars "g_i" = i ∧ σ.vars "g_D" = D) ∧
      σ.vars "g_i" / σ.vars "g_D" ≤ σ.vars "g_i" ∧
      σ.vars "g_i" / σ.vars "g_D" * σ.vars "g_D" ≤ σ.vars "g_i" ∧ σ.vars "g_D" < B) ?_ ?_
  · unfold splitI
    run_vcg
    have hi := ‹σ.vars "g_i" = i›
    have hD := ‹σ.vars "g_D" = D›
    have e : i - i / D * D = i % D := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits.mod_eq_sub i D
    simp only [Env.setVar, hi, hD, String.reduceEq, if_false, if_true, e]
  · rintro σ ⟨hi, hD⟩
    exact ⟨⟨hi, hD⟩, by rw [hi, hD]; exact h1, by rw [hi, hD]; exact h2, by rw [hD]; exact hDB⟩

/-! ### Flag loops -/

/-- **A loop setting a flag**: iteration `i` sets `f` iff `p i`. -/
theorem flagLoop {x m f : String} {S : List String} (hfS : f ∈ S) (hxS : x ∉ S) {N Kb : ℕ}
    (hNB : N + 1 < B) (Cx : Env → Prop)
    (hCx : ∀ σ σ', Cx σ → Frame (x :: S) [] σ σ' → Cx σ') (hm : ∀ σ, Cx σ → σ.vars m = N)
    (b0 : Bool) (p : ℕ → Bool) {body : Com}
    (hbody : ∀ i < N, Spec B (fun σ => Cx σ ∧ σ.vars x = i) body
      (fun σ σ' => σ'.vars f = (if p i then 1 else σ.vars f) ∧ Frame S [] σ σ' ∧ σ'.out = σ.out) Kb) :
    Spec B (fun σ => Cx σ ∧ σ.vars f = bn b0) (loopC x m body)
      (fun σ σ' => Cx σ' ∧ σ'.vars f = bn (b0 || anyUpTo p N) ∧ Frame (x :: S) [] σ σ' ∧
        σ'.out = σ.out) ((Kb + 8) * N + 6) := by
  intro σ ⟨hc, hf⟩
  have hxf : x ≠ f := fun h => hxS (h ▸ hfS)
  let I : Env → Prop := fun τ => Cx τ ∧ τ.vars x ≤ N ∧ τ.vars f = bn (b0 || anyUpTo p (τ.vars x)) ∧
    Frame (x :: S) [] σ τ ∧ τ.out = σ.out
  have hstep : Spec B (fun τ => I τ ∧ τ.vars x < N) (.seq body (bump x))
      (fun τ τ' => I τ' ∧ τ'.vars x = τ.vars x + 1) (Kb + 4) := by
    intro τ ⟨⟨hc1, hle, hf1, fr1, o1⟩, hlt⟩
    obtain ⟨τ1, hr1, hf2, fr2, o2⟩ := hbody (τ.vars x) hlt τ ⟨hc1, rfl⟩
    have hx1 : τ1.vars x = τ.vars x := fr2.1 x hxS
    obtain ⟨τ2, hr2, rfl⟩ := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop.bump_spec (B := B) x τ1
      (show τ1.vars x + 1 < B by rw [hx1]; omega)
    have fr3 : Frame (x :: S) [] τ (τ1.setVar x (τ1.vars x + 1)) :=
      (fr2.mono (by intro y hy; simp [hy]) (by simp)).trans (Frame.setVar τ1 (by simp) _)
    refine ⟨_, hr1.seq hr2, ⟨hCx _ _ hc1 fr3, by simp [Env.setVar, hx1]; omega, ?_,
      fr1.trans fr3, by rw [← o1, ← o2]; rfl⟩, by simp [Env.setVar, hx1]⟩
    simp only [Env.setVar, if_true, if_neg (Ne.symm hxf), hf2, hx1, hf1, anyUpTo]
    cases p (τ.vars x) <;> simp
  obtain ⟨σ', hr, ⟨hc', -, hf', fr', o'⟩, hx'⟩ := Spec.forRangeZero (B := B) (c := .seq body (bump x))
    x m I N (Kb + 4) (by omega) (fun τ h => h.2.1) (fun τ h => hm τ h.1) hstep σ
    ⟨hCx _ _ hc (Frame.setVar σ (by simp) 0), by simp [Env.setVar],
      by simp [Env.setVar, if_neg (Ne.symm hxf), hf, anyUpTo], Frame.setVar σ (by simp) 0, rfl⟩
  exact ⟨σ', hr.mono (le_of_eq (by ring)), hc', by rw [hf', hx'], fr', o'⟩

/-! ### The decision -/

theorem decT_iff (k D u : ℕ) (bl vl : List ℕ) :
    DecT k D bl vl u ↔ anyUpTo (pT k u bl vl) D = true := by
  rw [anyUpTo_iff]; simp [DecT, pT]

theorem decF_iff (k D u : ℕ) (bl vl : List ℕ) :
    DecF k D bl vl u ↔
      (decide (k = 0) || anyUpTo (pF1 k u bl vl) D || anyUpTo (pF2 k u D bl vl) (D * D)) = true := by
  have hp := exists_pair_iff D fun j j2 => g bl j + 1 = g bl j2 ∧ g bl j2 < k ∧ g vl j < u ∧
    u < g vl j2
  simp only [Bool.or_eq_true, anyUpTo_iff, decide_eq_true_eq, DecF, pF1, pF2, hp]
  constructor
  · rintro (h | ⟨j, hj, h⟩ | ⟨j, hj, h⟩ | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨j, hj, Or.inl h⟩)
    · exact Or.inl (Or.inr ⟨j, hj, Or.inr h⟩)
    · exact Or.inr h
  · rintro ((h | ⟨j, hj, h | h⟩) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨j, hj, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨j, hj, h⟩))
    · exact Or.inr (Or.inr (Or.inr h))

/-- The scalars the decision assigns. -/
def decVars : List String := ["g_fT", "g_j", "g_fF", "g_i", "g_j2", "w_f", "g_und"]

theorem DA.frame {k D u : ℕ} {bl vl : List ℕ} {σ σ' : Env} {S : List String}
    (h : DA k D u bl vl σ) (hf : Frame S [] σ σ') (hS : ∀ y ∈ S, y ∈ decVars) : DA k D u bl vl σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hv : ∀ y, y ∉ decVars → σ'.vars y = σ.vars y := fun y hy => hf.1 y fun hm => hy (hS y hm)
  exact ⟨by rw [hf.2.1 _ (by simp)]; exact h1, by rw [hf.2.1 _ (by simp)]; exact h2,
    by rw [hv _ (by simp [decVars])]; exact h3, by rw [hv _ (by simp [decVars])]; exact h4,
    by rw [hv _ (by simp [decVars])]; exact h5, by rw [hv _ (by simp [decVars])]; exact h6⟩

/-- The cost of the decision. -/
def Kdec (D : ℕ) : ℕ := 100 * (D * D) + 200 * D + 200

set_option maxHeartbeats 4000000 in
/-- **The decision.** -/
theorem decCom_spec {k D u : ℕ} {bl vl : List ℕ} (hb : DB B k D u bl vl) :
    Spec B (DA k D u bl vl) decCom
      (fun σ σ' => σ'.vars "w_f" = (if dec k D bl vl u = some true then 1 else 0) ∧
        σ'.vars "g_und" = (if dec k D bl vl u = none then 1 else σ.vars "g_und") ∧
        Frame decVars [] σ σ' ∧ σ'.out = σ.out) (Kdec D) := by
  intro σ hσ
  have hbB := hb.hb; have hvB := hb.hv; have hkB := hb.hk; have huB := hb.hu; have hDB := hb.hD
  have hDA : ∀ τ τ' (S : List String), (∀ y ∈ S, y ∈ decVars) → DA k D u bl vl τ →
      Frame S [] τ τ' → DA k D u bl vl τ' := fun τ τ' S hS h hf => h.frame hf hS
  -- `g_fT := 0`
  have hr1 := RunStep.assign B σ "g_fT" (.lit 0) 0 (RunStep.eval_lit B 0 σ (by omega))
  set σ1 := σ.setVar "g_fT" 0 with hσ1
  have hσ1D : DA k D u bl vl σ1 := hDA _ _ ["g_fT"] (by simp [decVars]) hσ (Frame.setVar σ (by simp) 0)
  -- the used slots
  have hT := flagLoop (B := B) (x := "g_j") (m := "g_D") (f := "g_fT") (S := ["g_fT"]) (by simp)
    (by simp) (N := D) (Kb := 20) (by omega) (DA k D u bl vl)
    (fun τ τ' h hf => hDA τ τ' _ (by simp [decVars]) h hf) (fun τ h => h.2.2.2.2.1) false
    (pT k u bl vl) (body := tBody) (fun i hi => by
      intro τ ⟨⟨h1, h2, h3, h4, h5, h6⟩, hj⟩
      have := hbB i; have := hvB i
      obtain ⟨τ', hr, e, fr, o⟩ := tBody_spec (B := B) τ ⟨by rw [h1, hj, hb.hbl]; exact hi,
        by rw [h2, hj, hb.hvl]; exact hi, by rw [h1, hj]; omega, by rw [h2, hj]; omega,
        by rw [h3]; omega, by rw [h4]; omega, by omega, by rw [hj]; omega⟩
      refine ⟨τ', hr, ?_, fr, o⟩
      rw [e, h1, h2, h3, h4, hj]
      simp [pT, g])
  obtain ⟨σ2, hr2, hσ2D, hfT2, fr2, o2⟩ := hT σ1 ⟨hσ1D, by simp [hσ1, Env.setVar]⟩
  -- `g_fF := 0`, `k = 0`
  have hr3 := RunStep.assign B σ2 "g_fF" (.lit 0) 0 (RunStep.eval_lit B 0 σ2 (by omega))
  set σ3 := σ2.setVar "g_fF" 0 with hσ3
  have hσ3D : DA k D u bl vl σ3 := hDA _ _ ["g_fF"] (by simp [decVars]) hσ2D (Frame.setVar σ2 (by simp) 0)
  have hk3 : σ3.vars "w_k" = k := hσ3D.2.2.1
  have ev_k : (Expr.var "w_k").evalB B σ3 = some k := by rw [← hk3]; exact evalB_var (by rw [hk3]; omega)
  have ev_0 : (Expr.lit 0).evalB B σ3 = some 0 := evalB_lit (by omega)
  obtain ⟨σ4, hr4, hfF4, fr4, o4⟩ : ∃ σ4, Run B (setIf (.eq (V "w_k") (.lit 0)) "g_fF") σ3 σ4 8 ∧
      σ4.vars "g_fF" = bn (decide (k = 0)) ∧ Frame ["g_fF"] [] σ3 σ4 ∧ σ4.out = σ3.out := by
    by_cases hk0 : k = 0
    · refine ⟨σ3.setVar "g_fF" 1, (RunStep.ite_true B _ _ _ σ3 _ _
        (RunStep.cond_eq_true B σ3 _ _ _ _ ev_k ev_0 hk0)
        (RunStep.assign B σ3 "g_fF" (.lit 1) 1 (RunStep.eval_lit B 1 σ3 (by omega)))).mono
        (by simp [Cond.size, Expr.size]), by simp [Env.setVar, hk0], Frame.setVar σ3 (by simp) _, rfl⟩
    · refine ⟨σ3, (RunStep.ite_false B _ _ _ σ3 _ _
        (RunStep.cond_eq_false B σ3 _ _ _ _ ev_k ev_0 hk0) (RunStep.skip B σ3)).mono
        (by simp [Cond.size, Expr.size]), by simp [hσ3, Env.setVar, hk0], Frame.refl _ _ _, rfl⟩
  have hσ4D : DA k D u bl vl σ4 := hDA _ _ _ (by simp [decVars]) hσ3D fr4
  -- the slots below `0`, above `k-1`
  have hF1 := flagLoop (B := B) (x := "g_j") (m := "g_D") (f := "g_fF") (S := ["g_fF"]) (by simp)
    (by simp) (N := D) (Kb := 40) (by omega) (DA k D u bl vl)
    (fun τ τ' h hf => hDA τ τ' _ (by simp [decVars]) h hf) (fun τ h => h.2.2.2.2.1) (decide (k = 0))
    (pF1 k u bl vl) (body := f1Body) (fun i hi => by
      intro τ ⟨⟨h1, h2, h3, h4, h5, h6⟩, hj⟩
      have := hbB i; have := hvB i
      obtain ⟨τ', hr, e, fr, o⟩ := f1Body_spec (B := B) τ ⟨by rw [h1, hj, hb.hbl]; exact hi,
        by rw [h2, hj, hb.hvl]; exact hi, by rw [h1, hj]; omega, by rw [h2, hj]; omega,
        by rw [h3]; omega, by rw [h4]; omega, by rw [hj]; omega⟩
      refine ⟨τ', hr, ?_, fr, o⟩
      rw [e, h1, h2, h3, h4, hj]
      simp [pF1, g])
  obtain ⟨σ5, hr5, hσ5D, hfF5, fr5, o5⟩ := hF1 σ4 ⟨hσ4D, hfF4⟩
  -- the pairs of slots
  have hF2 := flagLoop (B := B) (x := "g_i") (m := "g_DD") (f := "g_fF")
    (S := ["g_fF", "g_j", "g_j2"]) (by simp) (by simp) (N := D * D) (Kb := 50) (by omega)
    (DA k D u bl vl) (fun τ τ' h hf => hDA τ τ' _ (by simp [decVars]) h hf)
    (fun τ h => h.2.2.2.2.2) (decide (k = 0) || anyUpTo (pF1 k u bl vl) D)
    (pF2 k u D bl vl) (body := .seq splitI f2Test) (fun i hi => by
      intro τ ⟨⟨h1, h2, h3, h4, h5, h6⟩, hj⟩
      obtain ⟨hjD, hj2D⟩ := div_mod_lt hi
      have := hbB (i / D); have := hvB (i / D); have := hbB (i % D); have := hvB (i % D)
      obtain ⟨τ1, hr1, rfl⟩ := splitI_spec (B := B) (i := i) (D := D) (by omega) (by omega) τ ⟨hj, h5⟩
      obtain ⟨τ', hr, e, fr, o⟩ := f2Test_spec (B := B)
        ((τ.setVar "g_j" (i / D)).setVar "g_j2" (i % D)) (by
          simp only [Env.setVar, String.reduceEq, if_false, if_true]
          rw [h1, h2, hb.hbl, hb.hvl, h3, h4]
          exact ⟨hjD, hjD, hj2D, hj2D, by omega, by omega, by omega, by omega, by omega, by omega,
            by omega, by omega⟩)
      refine ⟨τ', hr1.seq hr, ?_, ((Frame.setVar τ (by simp) _).trans (Frame.setVar _ (by simp) _)).trans
        (fr.mono (by simp) (by simp)), o⟩
      rw [e]
      simp only [Env.setVar, String.reduceEq, if_false, if_true]
      rw [h1, h2, h3, h4]
      simp [pF2, g])
  obtain ⟨σ6, hr6, hσ6D, hfF6, fr6, o6⟩ := hF2 σ5 ⟨hσ5D, hfF5⟩
  -- the result
  have hfT6 : σ6.vars "g_fT" = bn (anyUpTo (pT k u bl vl) D) := by
    rw [fr6.1 _ (by simp), fr5.1 _ (by simp), fr4.1 _ (by simp), hσ3, Env.setVar]
    simp only [String.reduceEq, if_false]; rw [hfT2]; simp
  have hdec := decT_iff k D u bl vl
  have hdecF := decF_iff k D u bl vl
  have e1 : (Expr.var "g_fT").evalB B σ6 = some (σ6.vars "g_fT") :=
    evalB_var (by rw [hfT6]; have := bn_le_one (anyUpTo (pT k u bl vl) D); omega)
  have e2 : (Expr.var "g_fF").evalB B σ6 = some (σ6.vars "g_fF") :=
    evalB_var (by rw [hfF6]; have := bn_le_one ((decide (k = 0) || anyUpTo (pF1 k u bl vl) D) ||
      anyUpTo (pF2 k u D bl vl) (D * D)); omega)
  have e1' : (Expr.lit 1).evalB B σ6 = some 1 := evalB_lit (by omega)
  have eL0 : (Expr.lit 0).evalB B σ6 = some 0 := evalB_lit (by omega)
  have eL1 : (Expr.lit 1).evalB B (σ6.setVar "w_f" 0) = some 1 := evalB_lit (by omega)
  have fr16 : Frame ["g_fT", "g_j", "g_fF", "g_i", "g_j2"] [] σ σ6 :=
    ((((((Frame.setVar σ (by simp) 0).trans (fr2.mono (by simp) (by simp))).trans
      (Frame.setVar σ2 (by simp) 0)).trans (fr4.mono (by simp) (by simp))).trans
      (fr5.mono (by simp) (by simp))).trans (fr6.mono (by simp) (by simp)))
  have hund6 : σ6.vars "g_und" = σ.vars "g_und" := fr16.1 _ (by simp)
  have o16 : σ6.out = σ.out := by
    rw [o6, o5, o4, hσ3]; show σ2.out = σ.out; rw [o2, hσ1]; rfl
  -- the final test
  obtain ⟨σ7, hr7, ef7, eu7, fr7, o7⟩ : ∃ σ7, Run B (.ite (.eq (V "g_fT") (.lit 1))
      (.assign "w_f" (.lit 1)) (.ite (.eq (V "g_fF") (.lit 1)) (.assign "w_f" (.lit 0))
        (.seq (.assign "w_f" (.lit 0)) (.assign "g_und" (.lit 1))))) σ6 σ7 20 ∧
      σ7.vars "w_f" = (if dec k D bl vl u = some true then 1 else 0) ∧
      σ7.vars "g_und" = (if dec k D bl vl u = none then 1 else σ.vars "g_und") ∧
      Frame ["w_f", "g_und"] [] σ6 σ7 ∧ σ7.out = σ6.out := by
    by_cases hT : anyUpTo (pT k u bl vl) D = true
    · have hdT : DecT k D bl vl u := hdec.mpr hT
      have hft : σ6.vars "g_fT" = 1 := by rw [hfT6, hT]; rfl
      refine ⟨σ6.setVar "w_f" 1, (RunStep.ite_true B _ _ _ σ6 _ _
        (RunStep.cond_eq_true B σ6 _ _ _ _ e1 e1' hft)
        (RunStep.assign B σ6 "w_f" (.lit 1) 1 (RunStep.eval_lit B 1 σ6 (by omega)))).mono
        (by simp [Cond.size, Expr.size]), ?_, ?_, Frame.setVar σ6 (by simp) _, rfl⟩
      · simp [Env.setVar, dec, hdT]
      · simp [Env.setVar, dec, hdT, hund6]
    · have hdT : ¬ DecT k D bl vl u := fun h => hT (hdec.mp h)
      have hft : σ6.vars "g_fT" ≠ 1 := by rw [hfT6]; simp [hT]
      by_cases hF : (decide (k = 0) || anyUpTo (pF1 k u bl vl) D ||
          anyUpTo (pF2 k u D bl vl) (D * D)) = true
      · have hdF : DecF k D bl vl u := hdecF.mpr hF
        have hff : σ6.vars "g_fF" = 1 := by rw [hfF6, hF]; rfl
        refine ⟨σ6.setVar "w_f" 0, (RunStep.ite_false B _ _ _ σ6 _ _
          (RunStep.cond_eq_false B σ6 _ _ _ _ e1 e1' hft)
          (RunStep.ite_true B _ _ _ σ6 _ _ (RunStep.cond_eq_true B σ6 _ _ _ _ e2 e1' hff)
            (RunStep.assign B σ6 "w_f" (.lit 0) 0 eL0))).mono
          (by simp [Cond.size, Expr.size]), ?_, ?_, Frame.setVar σ6 (by simp) _, rfl⟩
        · simp [Env.setVar, dec, hdT, hdF]
        · simp [Env.setVar, dec, hdT, hdF, hund6]
      · have hdF : ¬ DecF k D bl vl u := fun h => hF (hdecF.mp h)
        have hff : σ6.vars "g_fF" ≠ 1 := by rw [hfF6]; simp [hF]
        have ha := RunStep.assign B σ6 "w_f" (.lit 0) 0 eL0
        have hb2 := RunStep.assign B (σ6.setVar "w_f" 0) "g_und" (.lit 1) 1 eL1
        refine ⟨(σ6.setVar "w_f" 0).setVar "g_und" 1, (RunStep.ite_false B _ _ _ σ6 _ _
          (RunStep.cond_eq_false B σ6 _ _ _ _ e1 e1' hft)
          (RunStep.ite_false B _ _ _ σ6 _ _ (RunStep.cond_eq_false B σ6 _ _ _ _ e2 e1' hff)
            (ha.seq hb2))).mono (by simp [Cond.size, Expr.size]), ?_, ?_,
          (Frame.setVar σ6 (by simp) _).trans (Frame.setVar _ (by simp) _), rfl⟩
        · simp [Env.setVar, dec, hdT, hdF]
        · simp [Env.setVar, dec, hdT, hdF]
  refine ⟨σ7, (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq (hr6.seq (hr7.seq (Run.skip)))))))).mono
    ?_, ef7, eu7, (fr16.mono (by simp [decVars]) (by simp)).trans
      (fr7.mono (by simp [decVars]) (by simp)), by rw [o7, o16]⟩
  simp only [Kdec, Expr.size]
  nlinarith

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDec
