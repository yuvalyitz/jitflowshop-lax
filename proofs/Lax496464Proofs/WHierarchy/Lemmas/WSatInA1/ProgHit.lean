import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgNRows

/-! # Phase 7a: does the chosen set hit a clause?

`hitLoop_spec`: the test whether the elements chosen so far hit a clause, by a scan of the chosen
elements (`chLoop_spec`) for each literal. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgHit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgRows

variable {cl : List (List ℕ)} {d k B : ℕ}

/-- The chosen elements: the first `w_nch` entries of `ch`. -/
def chOf (σ : Env) : List ℕ := (σ.arrs "ch").take (σ.vars "w_nch")

theorem mem_take_succ {A : List ℕ} {q : ℕ} (hq : q < A.length) (f : ℕ) :
    f ∈ A.take (q + 1) ↔ f ∈ A.take q ∨ A.getD q 0 = f := by
  rw [List.take_add_one, List.getElem?_eq_getElem hq, Option.toList_some, List.mem_append,
    List.mem_singleton, List.getD_eq_getElem _ _ hq, eq_comm]

/-! ### Is `w_f` chosen? -/

def CHI (A : List ℕ) (f n : ℕ) (h0 : Prop) (σ : Env) : Prop :=
  σ.arrs "ch" = A ∧ σ.vars "w_f" = f ∧ σ.vars "w_nch" = n ∧ σ.vars "w_q" ≤ n ∧
    (σ.vars "w_hit" = 1 ↔ h0 ∨ f ∈ A.take (σ.vars "w_q")) ∧ σ.vars "w_hit" ≤ 1

set_option maxHeartbeats 1000000 in
theorem chBody_spec {A : List ℕ} {f n : ℕ} {h0 : Prop} (hn : n ≤ A.length)
    (hA : ∀ q < n, A.getD q 0 < B) (hnB : n + 1 < B) (hfB : f < B) :
    Spec B (fun σ => CHI A f n h0 σ ∧ σ.vars "w_q" < n)
      (.seq (.ite (.eq (.get "ch" (V "w_q")) (V "w_f")) (.assign "w_hit" (.lit 1)) .skip)
        (bump "w_q"))
      (fun σ σ' => CHI A f n h0 σ' ∧ σ'.vars "w_q" = σ.vars "w_q" + 1) 20 := by
  refine Spec.pre (P := fun σ => CHI A f n h0 σ ∧ σ.vars "w_q" < n ∧
      σ.vars "w_q" < (σ.arrs "ch").length ∧ (σ.arrs "ch").getD (σ.vars "w_q") 0 < B ∧
      (f ∈ A.take (σ.vars "w_q" + 1) ↔ f ∈ A.take (σ.vars "w_q") ∨ A.getD (σ.vars "w_q") 0 = f) ∧
      σ.vars "w_q" + 1 < B ∧ 1 < B) ?_ ?_
  · run_vcg
    all_goals (try simp only [CHI] at *)
    all_goals (try simp_all [Env.setVar]; try omega)
  · rintro σ ⟨⟨ha, hf, hn', hq, hh, hh1⟩, hlt⟩
    exact ⟨⟨ha, hf, hn', hq, hh, hh1⟩, hlt, by rw [ha]; omega, by rw [ha]; exact hA _ hlt,
      mem_take_succ (by omega) f, by omega, by omega⟩

/-- **The scan of the chosen elements.** -/
theorem chLoop_spec {N : ℕ} (hNB : N + 1 < B) :
    Spec B (fun σ => σ.vars "w_hit" ≤ 1 ∧ σ.vars "w_nch" ≤ N ∧
        σ.vars "w_nch" ≤ (σ.arrs "ch").length ∧
        (∀ q < σ.vars "w_nch", (σ.arrs "ch").getD q 0 < B) ∧ σ.vars "w_f" < B) chLoop
      (fun σ σ' => (σ'.vars "w_hit" = 1 ↔ σ.vars "w_hit" = 1 ∨ σ.vars "w_f" ∈ chOf σ) ∧
        σ'.vars "w_hit" ≤ 1 ∧ (∀ y, y ≠ "w_q" → y ≠ "w_hit" → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) (24 * N + 6) := by
  rintro σ ⟨hh, hnN, hnl, hA, hfB⟩
  set A := σ.arrs "ch"
  set n := σ.vars "w_nch"
  set f := σ.vars "w_f"
  have hloop := Spec.forRangeZero (B := B) "w_q" "w_nch" (CHI A f n (σ.vars "w_hit" = 1)) n 20
    (by omega) (fun σ h => h.2.2.2.1) (fun σ h => h.2.2.1) (chBody_spec hnl hA (by omega) hfB)
  obtain ⟨σ', hr, ⟨⟨ha, -, -, -, hh', hh1⟩, hq⟩, hv, har, hin, hout⟩ :=
    hloop.frame.run (σ := σ) ⟨by simp [Env.setVar, A], by simp [Env.setVar, f],
      by simp [Env.setVar, n], by simp [Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar]; omega⟩
  refine ⟨σ', hr.mono (by nlinarith), by rw [hh', hq]; rfl, hh1, fun y h1 h2 => hv y ?_, ?_,
    hin (by simp [Com.reads]), hout (by simp [Com.NoWrite])⟩
  · simp [Com.wvars, h1, h2]
  · funext a; exact har a (by simp [Com.warrs])

/-! ### Does the chosen set hit the clause at `w_o`? -/

/-- The facts the scan of a clause reads. -/
def HP (cl : List (List ℕ)) (d k c2 : ℕ) (σ : Env) : Prop :=
  σ.arrs "cd" = cl.flatten ∧ σ.arrs "fp_f" = F1 cl d k ∧ c2 < cl.length ∧
    σ.vars "w_o" = off cl c2 ∧ σ.vars "w_ln" = len cl c2 ∧ σ.vars "w_nch" ≤ k ∧
    σ.vars "w_nch" ≤ (σ.arrs "ch").length ∧ (∀ e ∈ chOf σ, e ≤ nL cl)

/-- The scan has seen the literals before `i`. -/
def HitP (cl : List (List ℕ)) (c2 i : ℕ) (ch : List ℕ) : Prop :=
  ∃ i' < i, code cl (off cl c2 + i') % 2 = 0 ∧ fst cl (off cl c2 + i') ∈ ch

def HI (cl : List (List ℕ)) (d k c2 : ℕ) (ch : List ℕ) (σ : Env) : Prop :=
  HP cl d k c2 σ ∧ chOf σ = ch ∧ σ.vars "w_i" ≤ len cl c2 ∧
    (σ.vars "w_hit" = 1 ↔ HitP cl c2 (σ.vars "w_i") ch) ∧ σ.vars "w_hit" ≤ 1

theorem hitP_succ {c2 i : ℕ} {ch : List ℕ} :
    HitP cl c2 (i + 1) ch ↔ HitP cl c2 i ch ∨
      (code cl (off cl c2 + i) % 2 = 0 ∧ fst cl (off cl c2 + i) ∈ ch) := by
  unfold HitP
  constructor
  · rintro ⟨i', hi', h⟩
    rcases Nat.lt_or_ge i' i with h' | h'
    · exact Or.inl ⟨i', h', h⟩
    · have : i' = i := by omega
      subst this; exact Or.inr h
  · rintro (⟨i', hi', h⟩ | h)
    · exact ⟨i', by omega, h⟩
    · exact ⟨i, by omega, h⟩

set_option maxHeartbeats 4000000 in
theorem hitBody_spec (hB : BB cl d k B) {c2 : ℕ} {ch : List ℕ} :
    Spec B (fun σ => HI cl d k c2 ch σ ∧ σ.vars "w_i" < len cl c2) (.seq hitLit (bump "w_i"))
      (fun σ σ' => HI cl d k c2 ch σ' ∧ σ'.vars "w_i" = σ.vars "w_i" + 1) (24 * k + 40) := by
  have hl := hB.hl
  have hMB := hB.cb.small
  have hsz := nL_le_sz cl d k
  have hch := chLoop_spec (B := B) (N := k) (by omega)
  refine Spec.pre (P := fun σ => HI cl d k c2 ch σ ∧ σ.vars "w_i" < len cl c2 ∧
      σ.vars "w_o" + σ.vars "w_i" < (σ.arrs "cd").length ∧
      σ.vars "w_o" + σ.vars "w_i" < (σ.arrs "fp_f").length ∧ σ.vars "w_o" + σ.vars "w_i" < B ∧
      (σ.arrs "cd").getD (σ.vars "w_o" + σ.vars "w_i") 0 < B ∧
      (σ.arrs "fp_f").getD (σ.vars "w_o" + σ.vars "w_i") 0 < B ∧
      (σ.arrs "cd").getD (σ.vars "w_o" + σ.vars "w_i") 0 = code cl (off cl c2 + σ.vars "w_i") ∧
      (σ.arrs "fp_f").getD (σ.vars "w_o" + σ.vars "w_i") 0 = fst cl (off cl c2 + σ.vars "w_i") ∧
      (∀ q < σ.vars "w_nch", (σ.arrs "ch").getD q 0 < B) ∧ σ.vars "w_i" + 1 < B ∧ 1 < B) ?_ ?_
  · unfold hitLit
    run_vcg [hch]
    all_goals (try simp only [HI, HP] at *)
    all_goals (try simp_all [Env.setVar, hitP_succ, chOf]; try omega)
  · rintro σ ⟨⟨⟨hcd, hf, hc2, ho, hln, hnk, hnl, hent⟩, hchv, hi, hh, hh1⟩, hlt⟩
    have hj : off cl c2 + σ.vars "w_i" < nL cl := off_lt cl hc2 hlt
    have hcode : (σ.arrs "cd").getD (σ.vars "w_o" + σ.vars "w_i") 0 =
        code cl (off cl c2 + σ.vars "w_i") := by rw [hcd, ho]; rfl
    have hfst : (σ.arrs "fp_f").getD (σ.vars "w_o" + σ.vars "w_i") 0 =
        fst cl (off cl c2 + σ.vars "w_i") := by rw [hf, ho]; exact WH_F1_getD hj
    refine ⟨⟨⟨hcd, hf, hc2, ho, hln, hnk, hnl, hent⟩, hchv, hi, hh, hh1⟩, hlt, ?_, ?_, ?_, ?_, ?_,
      hcode, hfst, ?_, by omega, by omega⟩
    · rw [hcd, ho]; exact hj
    · rw [hf, length_F1, ho]; omega
    · rw [ho]; omega
    · rw [hcode]; exact code_lt hB.hx hj
    · rw [hfst]; have := fst_lt cl hj; omega
    · intro q hq
      have hm : (σ.arrs "ch").getD q 0 ∈ chOf σ := by
        unfold chOf
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.mem_iff_getElem.mpr ⟨q, by simp; omega, by simp⟩
      have := hent _ hm; omega

/-- The cost of the scan of a clause. -/
def Khit (d k : ℕ) : ℕ := (24 * k + 44) * d + 6

theorem hitLoop_spec (hB : BB cl d k B) (hd : ∀ C ∈ cl, C.length ≤ d) {c2 : ℕ} :
    Spec B (fun σ => HP cl d k c2 σ ∧ σ.vars "w_hit" = 0) hitLoop
      (fun σ σ' => (σ'.vars "w_hit" = 1 ↔ hitB cl (chOf σ) c2 = true) ∧ σ'.vars "w_hit" ≤ 1 ∧
        (∀ y, y ∉ ["w_i", "w_f", "w_q", "w_hit"] → σ'.vars y = σ.vars y) ∧
        σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out) (Khit d k) := by
  rintro σ ⟨hp, hh⟩
  have hl := hB.hl
  have hlen := len_le_of_dcnf cl hd c2
  have hol := off_len_le cl hp.2.2.1
  have hloop := Spec.forRangeZero (B := B) "w_i" "w_ln" (HI cl d k c2 (chOf σ)) (len cl c2)
    (24 * k + 40) (by omega) (fun σ h => h.2.2.1) (fun σ h => h.1.2.2.2.2.1) (hitBody_spec hB)
  obtain ⟨hcd, hf, hc2, ho, hln, hnk, hnl, hent⟩ := hp
  obtain ⟨σ', hr, ⟨⟨-, -, -, hh', hh1⟩, hi'⟩, hv, har, hin, hout⟩ :=
    hloop.frame.run (σ := σ) ⟨⟨by simp [Env.setVar, hcd], by simp [Env.setVar, hf], hc2,
      by simp [Env.setVar, ho], by simp [Env.setVar, hln], by simp [Env.setVar, hnk],
      by simp [Env.setVar, hnl], by simpa [chOf, Env.setVar] using hent⟩,
      by simp [chOf, Env.setVar], by simp [Env.setVar],
      by simp [Env.setVar, hh, HitP], by simp [Env.setVar, hh]⟩
  refine ⟨σ', hr.mono ?_, by rw [hh', hi', hitB_iff]; rfl, hh1, fun y hy => hv y ?_, ?_,
    hin (by simp [hitLit, chLoop, Com.reads]), hout (by simp [hitLit, chLoop, Com.NoWrite])⟩
  · unfold Khit; nlinarith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [hitLit, chLoop, Com.wvars, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2]
  · funext a; exact har a (by simp [hitLit, chLoop, Com.warrs])

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgHit
