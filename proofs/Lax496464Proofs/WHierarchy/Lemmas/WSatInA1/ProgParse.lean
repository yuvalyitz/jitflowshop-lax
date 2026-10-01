import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic

/-! # Phase 1: parsing the clauses

`parse` walks the clauses of the word `x = wordOf' cl k`: it stores the offset of every clause into
`co` and copies the literal codes into `cd`, and ends with `w_m = m`, `w_L = L`, `w_k = k`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs
open Lax496464Proofs.WHierarchy.Machine.ReadTape (take_append_set)

/-! ### The word -/

section Word

variable (cl : List (List ℕ))

/-- The clause part of the word. -/
def clw : List ℕ := cl.flatMap fun c => c.length :: c

theorem length_clw : (clw cl).length = cl.length + nL cl := by
  unfold clw nL
  induction cl with
  | nil => simp
  | cons C cl ih => simp [List.flatten_cons] at ih ⊢; omega

theorem clw_len {c : ℕ} (hc : c < cl.length) : (clw cl).getD (c + off cl c) 0 = len cl c := by
  induction cl generalizing c with
  | nil => simp at hc
  | cons C cl ih =>
    rcases c with _ | c
    · simp [clw, off, len]
    · have e : c + 1 + off (C :: cl) (c + 1) = (C.length + 1) + (c + off cl c) := by
        rw [off_cons_succ]; omega
      rw [e, len_cons_succ]
      unfold clw at ih ⊢
      rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by simp), List.length_cons,
        Nat.add_sub_cancel_left]
      exact ih (by simp at hc; omega)

theorem clw_code {c i : ℕ} (hc : c < cl.length) (hi : i < len cl c) :
    (clw cl).getD (c + off cl c + 1 + i) 0 = code cl (off cl c + i) := by
  induction cl generalizing c with
  | nil => simp at hc
  | cons C cl ih =>
    rcases c with _ | c
    · simp only [off_zero, zero_add, clw, List.flatMap_cons]
      have hi' : i < C.length := by simpa [len] using hi
      rw [code_cons_lt cl C hi', show 0 + 1 + i = (1 + i) by omega, List.cons_append,
        show 1 + i = i + 1 by omega, List.getD_cons_succ, List.getD_append _ _ _ _ hi']
    · have e : c + 1 + off (C :: cl) (c + 1) + 1 + i = (C.length + 1) + (c + off cl c + 1 + i) := by
        rw [off_cons_succ]; omega
      have e2 : off (C :: cl) (c + 1) + i = C.length + (off cl c + i) := by
        rw [off_cons_succ]; omega
      rw [e, e2, code_cons_add]
      rw [len_cons_succ] at hi
      unfold clw at ih ⊢
      rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by simp), List.length_cons,
        Nat.add_sub_cancel_left]
      exact ih (by simp at hc; omega) hi

end Word

variable {cl : List (List ℕ)} {k : ℕ}

theorem wordOf'_eq (cl : List (List ℕ)) (k : ℕ) : wordOf' cl k = cl.length :: (clw cl ++ [k]) := by
  simp [wordOf', clw]

theorem length_wordOf' : (wordOf' cl k).length = cl.length + nL cl + 2 := by
  rw [wordOf'_eq]; simp [length_clw]

theorem word_zero : (wordOf' cl k).getD 0 0 = cl.length := by rw [wordOf'_eq]; rfl

theorem word_len {c : ℕ} (hc : c < cl.length) :
    (wordOf' cl k).getD (1 + c + off cl c) 0 = len cl c := by
  have h1 := off_len_le cl hc
  have h2 := length_clw cl
  rw [wordOf'_eq, show 1 + c + off cl c = (c + off cl c) + 1 by omega, List.getD_cons_succ,
    List.getD_append _ _ _ _ (by omega)]
  exact clw_len cl hc

theorem word_code {c i : ℕ} (hc : c < cl.length) (hi : i < len cl c) :
    (wordOf' cl k).getD (1 + c + off cl c + 1 + i) 0 = code cl (off cl c + i) := by
  have h1 := off_len_le cl hc
  have h2 := length_clw cl
  rw [wordOf'_eq, show 1 + c + off cl c + 1 + i = (c + off cl c + 1 + i) + 1 by omega,
    List.getD_cons_succ, List.getD_append _ _ _ _ (by omega)]
  exact clw_code cl hc hi

theorem off_length (cl : List (List ℕ)) : off cl cl.length = nL cl := by
  simp [off, nL, List.length_flatten]

theorem word_k : (wordOf' cl k).getD (1 + cl.length + off cl cl.length) 0 = k := by
  rw [off_length, wordOf'_eq, show 1 + cl.length + nL cl = (clw cl).length + 1 by
    rw [length_clw]; omega, List.getD_cons_succ, List.getD_append_right _ _ _ _ le_rfl]
  simp

/-! ### The arrays -/

/-- The offsets of the clauses, `m + 1` of them. -/
def coList (cl : List (List ℕ)) : List ℕ := (List.range (cl.length + 1)).map (off cl)

/-- The offsets, filled up to `n`. -/
def coS (cl : List (List ℕ)) (n : ℕ) : List ℕ :=
  (coList cl).take n ++ List.replicate ((coList cl).length - n) 0

/-- The codes, filled up to `n`. -/
def cdS (cl : List (List ℕ)) (n : ℕ) : List ℕ :=
  cl.flatten.take n ++ List.replicate (cl.flatten.length - n) 0

theorem length_coList (cl : List (List ℕ)) : (coList cl).length = cl.length + 1 := by
  simp [coList]

theorem coList_getD {cl : List (List ℕ)} {c : ℕ} (hc : c < cl.length + 1) :
    (coList cl).getD c 0 = off cl c := by
  unfold coList; rw [List.getD_eq_getElem _ _ (by simpa using hc)]; simp

theorem cdS_set {n : ℕ} (hn : n < nL cl) : (cdS cl n).set n (code cl n) = cdS cl (n + 1) :=
  take_append_set cl.flatten n hn

theorem coS_set {n : ℕ} (hn : n < cl.length + 1) : (coS cl n).set n (off cl n) = coS cl (n + 1) := by
  rw [← coList_getD hn]
  exact take_append_set _ n (by rw [length_coList]; exact hn)

theorem length_cdS (n : ℕ) : (cdS cl n).length = nL cl := by
  simp [cdS, nL]; omega

theorem length_coS (n : ℕ) : (coS cl n).length = cl.length + 1 := by
  simp [coS, length_coList]; omega

theorem cdS_full : cdS cl (nL cl) = cl.flatten := by simp [cdS, nL]

theorem coS_full : coS cl (cl.length + 1) = coList cl := by simp [coS, length_coList]

theorem coS_zero : coS cl 0 = List.replicate (cl.length + 1) 0 := by simp [coS, length_coList]

theorem cdS_zero : cdS cl 0 = List.replicate (nL cl) 0 := by simp [cdS, nL]

theorem coS_last : (coS cl cl.length).set cl.length (nL cl) = coList cl := by
  rw [← off_length cl, coS_set (by omega), coS_full]

/-! ### Copying one clause -/

variable {B : ℕ}

/-- The invariant of the copy of clause `c`. -/
def CI (cl : List (List ℕ)) (k c : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = wordOf' cl k ∧ σ.vars "w_L" = off cl c ∧ σ.vars "w_pos" = 1 + c + off cl c ∧
    σ.vars "w_ln" = len cl c ∧ σ.vars "w_i" ≤ len cl c ∧
    σ.arrs "cd" = cdS cl (off cl c + σ.vars "w_i")

set_option maxHeartbeats 1000000 in
theorem copyBody_spec (hxB : ∀ v ∈ wordOf' cl k, v < B) (hlB : cl.length + nL cl + 4 < B)
    {c : ℕ} (hc : c < cl.length) :
    Spec B (fun σ => CI cl k c σ ∧ σ.vars "w_i" < len cl c) copyBody
      (fun σ σ' => CI cl k c σ' ∧ σ'.vars "w_i" = σ.vars "w_i" + 1) 30 := by
  have hol := off_len_le cl hc
  unfold copyBody
  refine Spec.pre (P := fun σ => CI cl k c σ ∧ σ.vars "w_i" < len cl c ∧
      σ.vars "w_L" + σ.vars "w_i" < (σ.arrs "cd").length ∧
      σ.vars "w_pos" + 1 + σ.vars "w_i" < (σ.arrs "a").length ∧
      (σ.arrs "cd").set (σ.vars "w_L" + σ.vars "w_i")
        ((σ.arrs "a").getD (σ.vars "w_pos" + 1 + σ.vars "w_i") 0) =
        cdS cl (off cl c + (σ.vars "w_i" + 1)) ∧
      (σ.arrs "a").getD (σ.vars "w_pos" + 1 + σ.vars "w_i") 0 < B ∧
      σ.vars "w_L" + σ.vars "w_i" < B ∧ σ.vars "w_pos" + 1 + σ.vars "w_i" < B ∧
      σ.vars "w_pos" + 1 < B ∧ σ.vars "w_i" + 1 < B) ?_ ?_
  · run_vcg
    all_goals (simp only [CI] at *; simp_all [Env.setVar, Env.setArr]; try omega)
  · rintro σ ⟨⟨ha, hL, hpos, hln, hi, hcd⟩, hlt⟩
    have hx := length_wordOf' (cl := cl) (k := k)
    have hw := word_code (k := k) hc hlt
    refine ⟨⟨ha, hL, hpos, hln, hi, hcd⟩, hlt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcd, length_cdS, hL]; omega
    · rw [ha, hpos]; omega
    · rw [hcd, ha, hL, hpos, hw, ← Nat.add_assoc]
      exact cdS_set (by omega)
    · rw [ha, hpos, hw]
      exact hxB _ (by rw [← hw]; exact Lax496464Proofs.WHierarchy.HittingSet.Compress.getD_mem (by omega))
    · rw [hL]; omega
    · rw [hpos]; omega
    · rw [hpos]; omega
    · omega

/-- The cost of a copy. -/
def Kcopy (cl : List (List ℕ)) : ℕ := 34 * nL cl + 6

theorem copyLoop_spec (hxB : ∀ v ∈ wordOf' cl k, v < B) (hlB : cl.length + nL cl + 4 < B) :
    Spec B (fun σ => σ.arrs "a" = wordOf' cl k ∧ σ.vars "w_c" < cl.length ∧
        σ.vars "w_L" = off cl (σ.vars "w_c") ∧
        σ.vars "w_pos" = 1 + σ.vars "w_c" + off cl (σ.vars "w_c") ∧
        σ.vars "w_ln" = len cl (σ.vars "w_c") ∧ σ.arrs "cd" = cdS cl (off cl (σ.vars "w_c")))
      (loop "w_i" "w_ln" copyBody)
      (fun σ σ' => σ'.arrs "cd" = cdS cl (off cl (σ.vars "w_c") + len cl (σ.vars "w_c")) ∧
        (∀ y, y ≠ "w_i" → σ'.vars y = σ.vars y) ∧ (∀ a, a ≠ "cd" → σ'.arrs a = σ.arrs a) ∧
        σ'.inp = σ.inp ∧ σ'.out = σ.out) (Kcopy cl) := by
  rintro σ ⟨ha, hc, hL, hpos, hln, hcd⟩
  set c := σ.vars "w_c"
  have hol := off_len_le cl hc
  have hloop := Spec.forRangeZero (B := B) "w_i" "w_ln" (CI cl k c) (len cl c) 30 (by omega)
    (fun σ h => h.2.2.2.2.1) (fun σ h => h.2.2.2.1) (copyBody_spec hxB hlB hc)
  obtain ⟨σ', hr, ⟨⟨-, -, -, -, -, hcd'⟩, hi'⟩, hv, har, hin, hout⟩ :=
    hloop.frame.run (σ := σ) ⟨by simp [Env.setVar, ha], by simp [Env.setVar, hL],
      by simp [Env.setVar, hpos], by simp [Env.setVar, hln], by simp [Env.setVar],
      by simp [Env.setVar, hcd]⟩
  refine ⟨σ', hr.mono ?_, by rw [hcd', hi'], fun y hy => hv y ?_, fun a hne => har a ?_,
    hin (by simp [copyBody, Com.reads]), hout (by simp [copyBody, Com.NoWrite])⟩
  · unfold Kcopy; nlinarith
  · simp [copyBody, Com.wvars, hy]
  · simp [copyBody, Com.warrs, hne]

/-! ### The loop over the clauses -/

/-- The invariant of the walk over the clauses. -/
def PI (cl : List (List ℕ)) (k : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = wordOf' cl k ∧ σ.vars "w_m" = cl.length ∧ σ.vars "w_c" ≤ cl.length ∧
    σ.vars "w_L" = off cl (σ.vars "w_c") ∧ σ.vars "w_pos" = 1 + σ.vars "w_c" + off cl (σ.vars "w_c") ∧
    σ.arrs "co" = coS cl (σ.vars "w_c") ∧ σ.arrs "cd" = cdS cl (off cl (σ.vars "w_c"))

set_option maxHeartbeats 2000000 in
theorem parseBody_spec (hxB : ∀ v ∈ wordOf' cl k, v < B) (hlB : cl.length + nL cl + 4 < B) :
    Spec B (fun σ => PI cl k σ ∧ σ.vars "w_c" < cl.length) parseBody
      (fun σ σ' => PI cl k σ' ∧ σ'.vars "w_c" = σ.vars "w_c" + 1) (Kcopy cl + 40) := by
  unfold parseBody
  refine Spec.pre (P := fun σ => PI cl k σ ∧ σ.vars "w_c" < cl.length ∧
      σ.vars "w_c" < (σ.arrs "co").length ∧ σ.vars "w_pos" < (σ.arrs "a").length ∧
      (σ.arrs "a").getD (σ.vars "w_pos") 0 = len cl (σ.vars "w_c") ∧
      (σ.arrs "co").set (σ.vars "w_c") (σ.vars "w_L") = coS cl (σ.vars "w_c" + 1) ∧
      off cl (σ.vars "w_c") + len cl (σ.vars "w_c") = off cl (σ.vars "w_c" + 1) ∧
      σ.vars "w_L" + len cl (σ.vars "w_c") < B ∧
      σ.vars "w_pos" + len cl (σ.vars "w_c") + 1 < B ∧ len cl (σ.vars "w_c") < B ∧
      σ.vars "w_c" + 1 < B ∧ σ.vars "w_L" < B ∧ σ.vars "w_pos" < B) ?_ ?_
  · run_vcg [copyLoop_spec hxB hlB]
    all_goals (simp only [PI] at *; simp_all [Env.setVar, Env.setArr]; try omega)
  · rintro σ ⟨⟨ha, hm, hcm, hL, hpos, hco, hcd⟩, hlt⟩
    have hol := off_len_le cl hlt
    have hx := length_wordOf' (cl := cl) (k := k)
    have hsucc := off_succ cl hlt
    refine ⟨⟨ha, hm, hcm, hL, hpos, hco, hcd⟩, hlt, ?_, ?_, ?_, ?_, hsucc.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hco, length_coS]; omega
    · rw [ha, hpos]; omega
    · rw [ha, hpos]; exact word_len hlt
    · rw [hco, hL]; exact coS_set (by omega)
    · rw [hL]; omega
    · rw [hpos]; omega
    · omega
    · omega
    · rw [hL]; omega
    · rw [hpos]; omega

/-- What `parse` establishes. -/
def PostParse (cl : List (List ℕ)) (k : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = wordOf' cl k ∧ σ.vars "w_m" = cl.length ∧ σ.vars "w_L" = nL cl ∧
    σ.vars "w_k" = k ∧ σ.arrs "co" = coList cl ∧ σ.arrs "cd" = cl.flatten

/-- The cost of the loop of `parse`. -/
def KpLoop (cl : List (List ℕ)) : ℕ := (Kcopy cl + 40 + 4) * cl.length + 6

/-- The cost of `parse`. -/
def Kparse (cl : List (List ℕ)) : ℕ := KpLoop cl + 40

set_option maxHeartbeats 2000000 in
theorem parse_value (hxB : ∀ v ∈ wordOf' cl k, v < B) (hlB : cl.length + nL cl + 4 < B) :
    Spec B (fun σ => σ.arrs "a" = wordOf' cl k ∧ σ.arrs "co" = List.replicate (cl.length + 1) 0 ∧
        σ.arrs "cd" = List.replicate (nL cl) 0) parse
      (fun _ σ' => PostParse cl k σ') (Kparse cl) := by
  have hx := length_wordOf' (cl := cl) (k := k)
  have hloop : Spec B (fun σ => PI cl k (σ.setVar "w_c" 0)) (loop "w_c" "w_m" parseBody)
      (fun _ σ' => PI cl k σ' ∧ σ'.vars "w_c" = cl.length) (KpLoop cl) :=
    Spec.forRangeZero (B := B) "w_c" "w_m" (PI cl k) cl.length (Kcopy cl + 40)
      (by omega) (fun σ h => h.2.2.1) (fun σ h => h.2.1) (parseBody_spec hxB hlB)
  have hk := word_k (cl := cl) (k := k)
  have hol := off_length cl
  have hkB : k < B := hxB k (by simp [wordOf'])
  unfold parse Kparse
  refine Spec.pre (P := fun σ => σ.arrs "a" = wordOf' cl k ∧
      σ.arrs "co" = List.replicate (cl.length + 1) 0 ∧ σ.arrs "cd" = List.replicate (nL cl) 0 ∧
      0 < (σ.arrs "a").length ∧ (σ.arrs "a").getD 0 0 = cl.length) ?_ ?_
  · run_vcg [hloop]
    all_goals simp only [PI, PostParse] at *
    all_goals (simp_all [Env.setVar, Env.setArr, off_zero, coS_zero, cdS_zero, length_coS, cdS_full, coS_last]; try omega)
  · rintro σ ⟨ha, hco, hcd⟩
    exact ⟨ha, hco, hcd, by rw [ha]; omega, by rw [ha]; exact word_zero⟩

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
