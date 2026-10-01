import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMain
import Lax496464Proofs.WHierarchy.Machine.ReadTape

/-! # p-Clique to Multicoloured Clique: the whole program

Read the tape into `a`; read `n = a[0]` and `k = a[|x| - 1]`; if `n < k` write the fixed
no-instance, otherwise run the body. The cost is announced per branch, so that the cheap branch
(`k` possibly huge) costs a constant. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdTop

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax496464Proofs.WHierarchy.Machine.ReadTape
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMath Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdDefs
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdAdj Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdRow
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdPass Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdMain

/-- **The program.** -/
def prog : Com := .seq readTape mainCom

/-- The cost of the branch. -/
def Kmain (x : List ℕ) : ℕ := if nV x < kP x then 20 else Ksum x + 20

theorem noCom_spec {B : ℕ} (hB : 1 < B) :
    Spec B (fun σ => σ.out = []) noCom (fun _ σ' => σ'.out = noWord) 20 := by
  unfold noCom
  run_vcg
  all_goals simp_all [noWord]

/-- The branch, with the cost of the branch taken. -/
theorem ite_spec {x : List ℕ} {B : ℕ} (hgood : Good x) (hent : ∀ w ∈ x, w < B)
    (hxB : x.length + 1 < B) (hBOK : kP x ≤ nV x → BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "b_n" = nV x ∧ σ.vars "b_k" = kP x ∧ σ.out = [])
      (.ite (.lt (ProdDefs.V "b_n") (ProdDefs.V "b_k")) noCom body) (fun _ σ' => σ'.out = reduce x)
      (1 + 3 + Kmain x) := by
  have hn : nV x < B := by have := hgood.1; omega
  have hk : kP x < B := kP_lt hent (by omega)
  have hcond : ∀ σ : Env, σ.vars "b_n" = nV x → σ.vars "b_k" = kP x →
      (Cond.lt (ProdDefs.V "b_n") (ProdDefs.V "b_k")).evalB B σ = some (decide (nV x < kP x)) := by
    intro σ h1 h2
    have := evalB_condLt (B := B) (evalB_var (x := "b_n") (σ := σ) (by omega))
      (evalB_var (x := "b_k") (σ := σ) (by omega))
    rw [h1, h2] at this
    exact this
  refine Spec.ite ?_ ?_ ?_
  · rintro σ ⟨-, h1, h2, -⟩; exact ⟨_, hcond σ h1 h2⟩
  · by_cases hnk : nV x < kP x
    · have hK : Kmain x = 20 := by simp [Kmain, hnk]
      rw [hK]
      refine Spec.post (Spec.pre (noCom_spec (by omega)) fun σ h => h.1.2.2.2) ?_
      intro σ σ' _ h
      rw [h]; unfold reduce; rw [if_pos hnk]
    · intro σ ⟨⟨_, h1, h2, _⟩, hc⟩
      rw [hcond σ h1 h2] at hc
      simp [hnk] at hc
  · by_cases hnk : nV x < kP x
    · intro σ ⟨⟨_, h1, h2, _⟩, hc⟩
      rw [hcond σ h1 h2] at hc
      simp [hnk] at hc
    · have hK : Kmain x = Ksum x + 20 := by simp [Kmain, hnk]
      rw [hK]
      refine Spec.mono (Spec.post (Spec.pre (body_spec (hBOK (by omega)))
        fun σ h => ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩) ?_) (by omega)
      rintro σ σ' ⟨⟨_, _, _, ho⟩, _⟩ ⟨h, -⟩
      rw [h, ho]; unfold reduce; rw [if_neg hnk]; simp

theorem last_eq_getD {x : List ℕ} (h : x ≠ []) : x.getD (x.length - 1) 0 = kP x := by
  unfold kP
  rcases List.eq_nil_or_concat x with rfl | ⟨l, a, rfl⟩
  · exact absurd rfl h
  · simp

set_option maxHeartbeats 1000000 in
theorem mainCom_spec {x : List ℕ} {B : ℕ} (hgood : Good x) (hent : ∀ w ∈ x, w < B)
    (hxB : x.length + 1 < B) (hBOK : kP x ≤ nV x → BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.out = []) mainCom
      (fun _ σ' => σ'.out = reduce x) (20 + (1 + 3 + Kmain x)) := by
  have hne : x ≠ [] := by
    intro h; have := hgood.1; rw [h] at this; simp at this
  have hlast := last_eq_getD hne
  have h0 : x.getD 0 0 = nV x := rfl
  have hn : nV x < B := by have := hgood.1; omega
  have hk : kP x < B := kP_lt hent (by omega)
  have hl : 0 < x.length := List.length_pos_of_ne_nil hne
  refine Spec.pre (P := fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.out = [] ∧
    x.getD 0 0 = nV x ∧ x.getD (x.length - 1) 0 = kP x ∧ nV x < B ∧ kP x < B ∧
    0 < x.length ∧ x.length < B) ?_ fun σ h => ⟨h.1, h.2.1, h.2.2, h0, hlast, hn, hk, hl, by omega⟩
  unfold mainCom
  run_vcg [ite_spec hgood hent hxB hBOK]
  all_goals (simp_all [Env.setVar]; try omega)

/-- **The run.** From the initial state on the tape `|x| :: x`, the program writes `reduce x`. -/
theorem prog_spec (x : List ℕ) (σ0 : Env) {B : ℕ} (hgood : Good x) (hent : ∀ w ∈ x, w < B)
    (hxB : x.length + 1 < B) (hBOK : kP x ≤ nV x → BOK x B)
    (hinp : σ0.inp = x.length :: x) (ha : σ0.arrs "a" = List.replicate x.length 0)
    (hout : σ0.out = []) :
    Spec B (fun σ => σ = σ0) prog (fun _ σ' => σ'.out = reduce x)
      (16 * x.length + 7 + (20 + (1 + 3 + Kmain x))) := by
  refine Spec.seq (readTape_spec x σ0 hent (by omega) hinp ha)
    (mainCom_spec hgood hent hxB hBOK) ?_ (fun _ _ _ _ _ h => h)
  rintro σ σ' rfl ⟨h1, h2, _, h4, _⟩
  exact ⟨h1, h2, by rw [h4, hout]⟩

/-! ### The layout -/

/-- The layout: the reader's scalars, `b_n`, `b_k`, the body's, and the array `a`. -/
def layout : Layout := ⟨["rt_n", "rt_i", "rt_v", "b_n", "b_k"] ++ bodyVars, ["a"], 8⟩

set_option maxHeartbeats 4000000 in
theorem prog_ok : Com.Ok layout prog := by
  simp [layout, prog, readTape, readLoop, readBody, mainCom, noCom, body, header, pass1, pass2,
    pass3, pass4, rowCount, rowEmit, emitIf, adjCom, adjPrep, adjTest, scan, scanLoop, scanBody,
    bump, bodyVars, Lax496464Proofs.WHierarchy.Machine.ReadTape.V, ProdDefs.V, Com.Ok, Expr.Ok, Cond.Ok, condExpr]

end Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.ProdTop
