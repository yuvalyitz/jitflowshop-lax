import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWalk

/-! # Phases 9–11: the formula

`mxPass` finds the first fresh variable `bb = 1 + max x`, `qOut` writes the quantifier block of
`phiOf`, `trPass` sets up and runs the walk. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PForm

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre Lax496464Proofs.WHierarchy.Lemmas.NegElim.PTr
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWalk Lax496464Proofs.WHierarchy.Lemmas.NegElim.PDisp
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Parse Lax496464Proofs.WHierarchy.Lemmas.NegElim.Math
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PStr

variable {x : List ℕ} {φ : Formula}

/-! ### The largest entry -/

theorem maxEntry_snoc (l : List ℕ) (a : ℕ) : maxEntry (l ++ [a]) = max (maxEntry l) a := by
  induction l with
  | nil => simp [maxEntry]
  | cons b l ih =>
    simp only [List.cons_append, maxEntry, List.foldr_cons] at ih ⊢
    rw [ih]; omega

theorem maxEntry_le {l : List ℕ} {m : ℕ} (h : ∀ v ∈ l, v ≤ m) : maxEntry l ≤ m := by
  induction l with
  | nil => simp [maxEntry]
  | cons a l ih =>
    simp only [maxEntry, List.foldr_cons] at ih ⊢
    exact max_le (h a (by simp)) (ih fun v hv => h v (by simp [hv]))

theorem maxEntry_take_le (x : List ℕ) (t : ℕ) : maxEntry (x.take t) ≤ maxEntry x :=
  maxEntry_le fun _ hv => le_maxEntry (List.mem_of_mem_take hv)

theorem maxEntry_take_succ {x : List ℕ} {t : ℕ} (h : t < x.length) :
    maxEntry (x.take (t + 1)) = max (maxEntry (x.take t)) x[t] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  exact maxEntry_snoc _ _

/-- The invariant of `mxPass`'s loop. -/
def MXI (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "t2" ≤ x.length ∧
    σ.vars "mx" = maxEntry (x.take (σ.vars "t2"))

theorem mxPass_spec :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) mxPass
      (fun σ σ' => σ'.vars "bb" = bOf x ∧ Keep ["mx", "t2", "bb"] σ σ' ∧ σ'.out = σ.out)
      ((20 + 4) * x.length + 20) := by
  have hl := len_lt_Bv x
  have hbody : Spec (Bv x) (fun σ => MXI x σ ∧ σ.vars "t2" < x.length) mxBody
      (fun σ σ' => MXI x σ' ∧ σ'.vars "t2" = σ.vars "t2" + 1) 20 := by
    refine Spec.pre (P := fun σ => (MXI x σ ∧ σ.vars "t2" < x.length) ∧
      σ.vars "t2" < (σ.arrs "a").length ∧ (σ.arrs "a").getD (σ.vars "t2") 0 < Bv x ∧
      σ.vars "mx" < Bv x ∧ σ.vars "t2" + 1 < Bv x ∧
      x.take (σ.vars "t2" + 1) = x.take (σ.vars "t2") ++ [x.getD (σ.vars "t2") 0]) ?_ ?_
    · unfold mxBody
      run_vcg
      all_goals
        (try simp only [MXI, Env.setVar] at *)
        simp_all [maxEntry_take_succ]
      all_goals (try omega)
    · rintro σ ⟨⟨ha, hn, ht, hm⟩, hlt⟩
      have hle := maxEntry_take_le x (σ.vars "t2")
      refine ⟨⟨⟨ha, hn, ht, hm⟩, hlt⟩, by rw [ha]; omega, by rw [ha]; exact getD_lt_Bv x _, ?_,
        by omega, take_succ_getD hlt⟩
      rw [hm]; have := Bv_big x; omega
  have h : Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) mxPass
      (fun _ σ' => σ'.vars "bb" = bOf x) ((20 + 4) * x.length + 20) := by
    have hloop := Spec.forRangeZero (B := Bv x) (c := mxBody) "t2" "rt_n" (MXI x) x.length 20
      (by omega) (fun σ h => h.2.2.1) (fun σ h => h.2.1) hbody
    have hbb : maxEntry x + 1 < Bv x := by have := Bv_big x; omega
    unfold mxPass loop
    run_vcg [hloop]
    all_goals
      (try simp only [MXI, Env.setVar] at *)
      simp_all [bOf, maxEntry, List.take_of_length_le]
    all_goals (try omega)
  exact Spec.keepOut h _ (by intro y hy; simp [mxPass, mxBody, loop, bump, Com.wvars] at hy; simp; tauto)
    (by simp [mxPass, mxBody, loop, bump, Com.warrs]) (by simp [mxPass, mxBody, loop, bump, Com.reads])
    (by simp [mxPass, mxBody, loop, bump, Com.NoWrite])

/-! ### The quantifier block -/

/-- The invariant of `qOut`'s loop. -/
def QI (b K : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "bb" = b ∧ σ.vars "KK" = K ∧ σ.vars "v" ≤ K ∧
    σ.out = out0 ++ (List.range' b (σ.vars "v")).flatMap fun v => [6, v]

theorem range'_succ' (b n : ℕ) : List.range' b (n + 1) = List.range' b n ++ [b + n] := by
  rw [← List.range'_append]; simp

theorem qOut_spec {b f0 : ℕ} (hf0 : f0 ≤ x.length) (hb : b + 2 * x.length + 8 < Bv x) :
    Spec (Bv x) (fun σ => σ.vars "rt_n" = x.length ∧ σ.vars "F0" = f0 ∧ σ.vars "bb" = b) qOut
      (fun σ σ' => σ'.out = σ.out ++
        (List.range' b (2 * (x.length - f0))).flatMap (fun v => [6, v]))
      ((20 + 4) * (2 * (x.length - f0)) + 20) := by
  have hl := len_lt_Bv x
  intro σ hσ
  have hbody : Spec (Bv x) (fun τ => QI b (2 * (x.length - f0)) σ.out τ ∧
      τ.vars "v" < 2 * (x.length - f0)) qBody
      (fun τ τ' => QI b (2 * (x.length - f0)) σ.out τ' ∧ τ'.vars "v" = τ.vars "v" + 1) 20 := by
    refine Spec.pre (P := fun τ => (QI b (2 * (x.length - f0)) σ.out τ ∧
      τ.vars "v" < 2 * (x.length - f0)) ∧ b + τ.vars "v" < Bv x ∧ τ.vars "v" + 1 < Bv x) ?_ ?_
    · unfold qBody writes
      run_vcg
      all_goals
        (try simp only [QI, Env.setVar] at *)
        simp_all [range'_succ']
      all_goals (try omega)
    · rintro τ ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by omega, by omega⟩
  have hloop := Spec.forRangeZero (B := Bv x) (c := qBody) "v" "KK" (QI b (2 * (x.length - f0)) σ.out)
    (2 * (x.length - f0)) 20 (by omega) (fun τ h => h.2.2.1) (fun τ h => h.2.1) hbody
  have h : Spec (Bv x) (fun τ => (τ.vars "rt_n" = x.length ∧ τ.vars "F0" = f0 ∧ τ.vars "bb" = b) ∧
      τ.out = σ.out) qOut
      (fun _ σ' => σ'.out = σ.out ++
        (List.range' b (2 * (x.length - f0))).flatMap (fun v => [6, v]))
      ((20 + 4) * (2 * (x.length - f0)) + 20) := by
    unfold qOut loop
    run_vcg [hloop]
    all_goals
      (try simp only [QI, Env.setVar] at *)
      simp_all
    all_goals (try omega)
  exact h σ ⟨hσ, rfl⟩

/-! ### The walk -/

theorem trPass_spec {b f0 : ℕ} (hdrop : x.drop f0 = φ.encode) (hlen : f0 + φ.encode.length = x.length)
    (hct : b + cnt true φ + 2 * x.length + 1 < Bv x) :
    Spec (Bv x) (fun σ => σ.arrs "a" = x ∧ σ.arrs "st" = List.replicate (x.length + 2) 0 ∧
        σ.vars "bb" = b ∧ σ.vars "F0" = f0) trPass
      (fun σ σ' => σ'.out = σ.out ++ (tr true φ b).encode)
      (20 + ((1 + (Cond.lt (L 0) (V "h")).size + (Kd x + 60)) * x.length + 1 +
        (Cond.lt (L 0) (V "h")).size)) := by
  have hl := len_lt_Bv x
  intro σ hσ
  have hloop := trLoop_spec (x := x) (T0 := (tr true φ b).encode) (ctot := b + cnt true φ)
    (out0 := σ.out) (by omega)
  have h : Spec (Bv x) (fun τ => (τ.arrs "a" = x ∧ τ.arrs "st" = List.replicate (x.length + 2) 0 ∧
      τ.vars "bb" = b ∧ τ.vars "F0" = f0) ∧ τ.out = σ.out) trPass
      (fun _ σ' => σ'.out = σ.out ++ (tr true φ b).encode)
      (20 + ((1 + (Cond.lt (L 0) (V "h")).size + (Kd x + 60)) * x.length + 1 +
        (Cond.lt (L 0) (V "h")).size)) := by
    unfold trPass
    run_vcg [hloop]
    all_goals
      (try simp only [Env.setVar, Env.setArr] at *)
    all_goals first
      | (refine ⟨[(true, φ)], [], ?_⟩
         refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [pend, stackOf, pb, trL, cntL]
         all_goals (try omega)
         all_goals (rw [show x.length + 2 = (x.length + 1) + 1 by ring, List.replicate_succ]; simp))
      | (simp_all; try omega)
    all_goals (try omega)
  exact h σ ⟨hσ, rfl⟩

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PForm
