import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.MccNP.Ram.ValidateDefs
import Lax496464Proofs.WHierarchy.MccNP.Ram.ValidateLemmas

/-!
# The run-of-ones loop of the validator
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Validate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

variable {B : ℕ} {y : List ℕ}

/-- Loop invariant of the run of ones from `s`. -/
def RI (i : String) (y : List ℕ) (s : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ s ≤ σ.vars i ∧ σ.vars i ≤ s + tw y s ∧
    (σ.vars "v_go" = 1 ∨ (σ.vars "v_go" = 0 ∧ σ.vars i = s + tw y s))

/-- The variant. -/
def RV (i : String) (y : List ℕ) (σ : Env) : ℕ := (y.length - σ.vars i) + σ.vars "v_go"

theorem getD_lt_B (hy : ∀ v ∈ y, v < B) (hB0 : 0 < B) (k : ℕ) : y.getD k 0 < B := by
  by_cases hk : k < y.length
  · rw [List.getD_eq_getElem _ _ hk]; exact hy _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hB0

theorem step1 {s i : ℕ} (h2 : i ≤ s + tw y s) (hlt : i < y.length)
    (heq : y.getD i 0 = 1) : i < s + tw y s := by
  by_contra hc
  have : i = s + tw y s := by omega
  subst this
  exact tw_stop hlt heq

theorem step2 {s i : ℕ} (h1 : s ≤ i) (h2 : i ≤ s + tw y s)
    (hne : ¬ y.getD i 0 = 1) : i = s + tw y s := by
  by_contra hc
  have hj : i - s < tw y s := by omega
  have := tw_one (y := y) hj
  rw [show s + (i - s) = i by omega] at this
  exact hne this

theorem step3 {s i : ℕ} (hs : s ≤ y.length) (h2 : i ≤ s + tw y s)
    (hge : ¬ i < y.length) : i = s + tw y s := by
  have := tw_le' hs
  omega

theorem runBody_spec (i : String) (hiL : i ≠ "L") (hig : i ≠ "v_go") (hy : ∀ v ∈ y, v < B)
    (hB : y.length + 2 < B) (s : ℕ) (hs : s ≤ y.length) :
    Spec B (fun σ => RI i y s σ ∧ σ.vars "v_go" = 1) (runBody i)
      (fun σ σ' => RI i y s σ' ∧ RV i y σ' < RV i y σ) 20 := by
  have htw := tw_le' hs
  have hB0 : 0 < B := by omega
  have hig' : "v_go" ≠ i := fun h => hig h.symm
  have hiL' : "L" ≠ i := fun h => hiL h.symm
  unfold runBody
  run_vcg
  all_goals (
    have hgo := ‹σ.vars "v_go" = 1›
    obtain ⟨ha, hL, h1, h2, -⟩ := ‹RI i y s σ›
    first
    | omega
    | (rw [ha]; omega)
    | (rw [ha]; exact getD_lt_B hy hB0 _)
    | skip)
  · rename_i hlt heq
    rw [ha] at heq
    have := step1 (s := s) h2 (by omega) heq
    simp [RI, RV, Env.setVar, hig', hiL', ha, hL, hgo]
    omega
  · rename_i hlt hne
    rw [ha] at hne
    have := step2 (s := s) h1 h2 hne
    simp [RI, RV, Env.setVar, hig, ha, hL, hgo]
    omega
  · rename_i hge
    have := step3 hs h2 (by omega)
    simp [RI, RV, Env.setVar, hig, ha, hL, hgo]
    omega

theorem runLoop_spec (i : String) (hiL : i ≠ "L") (hig : i ≠ "v_go") (hy : ∀ v ∈ y, v < B)
    (hB : y.length + 2 < B) (s : ℕ) (hs : s ≤ y.length) :
    Spec B (fun σ => RI i y s σ ∧ σ.vars "v_go" = 1) (runLoop i)
      (fun _ σ' => σ'.vars i = s + tw y s ∧ σ'.vars "v_go" = 0 ∧ σ'.arrs "a" = y ∧
        σ'.vars "L" = y.length) (24 * (y.length + 1) + 4) := by
  have hbody := runBody_spec (B := B) i hiL hig hy hB s hs
  have hgoB : ∀ σ : Env, RI i y s σ → σ.vars "v_go" < B := by
    intro σ h
    obtain ⟨-, -, -, -, h5⟩ := h
    omega
  refine Spec.while_count (P := fun σ => RI i y s σ ∧ σ.vars "v_go" = 1) (RI i y s) (RV i y) 20
    ?_ ?_ (fun σ h => h.1) ?_ |>.post ?_
  · intro σ h
    have := hgoB σ h
    obtain ⟨v, hv1, -⟩ := evalB_condEq_isSome (evalB_var this) (evalB_lit (show 1 < B by omega))
    exact ⟨v, hv1⟩
  · intro σ ⟨h1, h2⟩
    have : σ.vars "v_go" = 1 := by
      simp [evalB_condEq_iff] at h2
      omega
    exact hbody σ ⟨h1, this⟩
  · intro σ ⟨h1, h2⟩
    obtain ⟨-, hL, h3, -, -⟩ := h1
    simp only [RV, h2, Cond.size, Expr.size]
    omega
  · intro σ σ' _ ⟨h1, h2⟩
    have hg : σ'.vars "v_go" ≠ 1 := by
      intro hc
      have : (Cond.eq (V "v_go") (.lit 1)).evalB B σ' = some true := by
        have hgB := hgoB σ' h1
        simp [evalB_condEq_iff, hc, V]
        omega
      rw [this] at h2; simp at h2
    obtain ⟨ha, hL, -, -, h5⟩ := h1
    have h0 : σ'.vars "v_go" = 0 := by omega
    refine ⟨?_, h0, ha, hL⟩
    omega

/-- The frame: arrays, tapes, and every scalar outside `S` are as before. -/
def Frm (S : List String) (σ σ' : Env) : Prop :=
  σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧ ∀ z, z ∉ S → σ'.vars z = σ.vars z

theorem Frm.trans {S : List String} {σ σ' σ'' : Env} (h : Frm S σ σ') (h' : Frm S σ' σ'') :
    Frm S σ σ'' :=
  ⟨h'.1.trans h.1, h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1,
    fun z hz => (h'.2.2.2 z hz).trans (h.2.2.2 z hz)⟩

theorem Frm.mono {S S' : List String} {σ σ' : Env} (h : Frm S σ σ') (hS : ∀ z ∈ S, z ∈ S') :
    Frm S' σ σ' := ⟨h.1, h.2.1, h.2.2.1, fun z hz => h.2.2.2 z fun hm => hz (hS z hm)⟩

theorem Spec.frm {B : ℕ} {P : Env → Prop} {c : Com} {Q : Env → Env → Prop} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ z ∈ c.wvars, z ∈ S) (ha : c.warrs = [])
    (hr : ¬ c.reads) (hn : c.NoWrite) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Frm S σ σ') K := by
  refine h.frame.post ?_
  intro σ σ' _ ⟨hq, fv, fa, fi, fo⟩
  refine ⟨hq, funext fun a => fa a (by simp [ha]), fo hn, fi hr,
    fun z hz => fv z fun hm => hz (hw z hm)⟩

theorem runFrom_spec (i : String) (hiL : i ≠ "L") (hig : i ≠ "v_go") (hy : ∀ v ∈ y, v < B)
    (hB : y.length + 2 < B) (start : Expr) (s : ℕ) (hs : s ≤ y.length) :
    Spec B (fun σ => σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ start.evalB B σ = some s)
      (runFrom i start)
      (fun σ σ' => (σ'.vars i = s + tw y s ∧ σ'.vars "v_go" = 0) ∧ Frm [i, "v_go"] σ σ')
      (1 + start.size + 2 + (24 * (y.length + 1) + 4)) := by
  have h1 : Spec B (fun σ : Env => σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧
      start.evalB B σ = some s) (.assign i start) (fun σ σ' => σ' = σ.setVar i s)
      (1 + start.size) := Spec.assign (fun σ hσ => hσ.2.2)
  have h2 : Spec B (fun σ : Env => σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ σ.vars i = s)
      (.assign "v_go" (.lit 1)) (fun σ σ' => σ' = σ.setVar "v_go" 1) (1 + 1) :=
    Spec.assign (f := fun _ => 1) (fun σ _ => evalB_lit (by omega))
  have h3 := runLoop_spec (B := B) i hiL hig hy hB s hs
  have h23 := Spec.seq (R := fun σ σ'' => σ''.vars i = s + tw y s ∧ σ''.vars "v_go" = 0) h2 h3
    (by
      rintro σ σ' ⟨ha, hL, hi⟩ rfl
      simp only [RI, Env.setVar]
      simp [ha, hL, hi, hig]
)
    (fun σ σ' σ'' _ _ hq => ⟨hq.1, hq.2.1⟩)
  have h123 : Spec B (fun σ => σ.arrs "a" = y ∧ σ.vars "L" = y.length ∧ start.evalB B σ = some s)
      (runFrom i start) (fun σ σ'' => σ''.vars i = s + tw y s ∧ σ''.vars "v_go" = 0)
      (1 + start.size + (1 + 1 + (24 * (y.length + 1) + 4))) :=
    Spec.seq h1 h23
    (by
      rintro σ σ' ⟨ha, hL, -⟩ rfl
      simp [ha, hL]
      intro h
      exact absurd h.symm hiL)
    (fun σ σ' σ'' _ _ hq => hq)
  refine (Spec.frm (h123.mono (by omega)) [i, "v_go"] ?_ ?_ ?_ ?_)
  · intro z hz
    simp [runFrom, runLoop, runBody, Com.wvars] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto
  · simp [runFrom, runLoop, runBody, Com.warrs]
  · simp [runFrom, runLoop, runBody, Com.reads]
  · simp [runFrom, runLoop, runBody, Com.NoWrite]

end Lax496464Proofs.WHierarchy.MccNP.Validate
