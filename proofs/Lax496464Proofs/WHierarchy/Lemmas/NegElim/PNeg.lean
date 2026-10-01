import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLex

/-! # Writing the positive formula that replaces a negative atom

`negBig` writes the code of `negRel i ȳ c` for the atom `R_i ȳ` at position `p` of the word
(`ȳ = x[p + 3], …`), with `ri = i`, `ln = |ȳ| ≥ 1` and `fc = c`, in eleven phases. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PNeg

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Syntax Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFMath
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PWord
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PPre Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLex

variable {x : List ℕ}

/-- The scalars `negBig` assigns. -/
def negVars : List String := ["wk", "wg", "wn", "wl", "k1", "g1", "k2", "g2", "lm", "ll", "e1", "e2"]

/-- The context of `negBig`. -/
def NC (x : List ℕ) (p i r c : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "p" = p ∧ σ.vars "ri" = i ∧ σ.vars "ln" = r ∧ σ.vars "fc" = c

theorem NC.keep {p i r c : ℕ} {σ σ' : Env} (h : NC x p i r c σ) (hk : Keep negVars σ σ') :
    NC x p i r c σ' := by
  obtain ⟨ha, hp, hi, hr, hc⟩ := h
  exact ⟨by rw [hk.2.1]; exact ha, by rw [hk.1 "p" (by decide)]; exact hp,
    by rw [hk.1 "ri" (by decide)]; exact hi, by rw [hk.1 "ln" (by decide)]; exact hr,
    by rw [hk.1 "fc" (by decide)]; exact hc⟩

/-- The bounds `negBig` needs. -/
structure NOK (x : List ℕ) (p i r c : ℕ) : Prop where
  pos : 1 ≤ r
  code : p + 3 + r ≤ x.length
  bi : 5 * i + 5 < Bv x
  bc : c + 2 * r + 1 < Bv x
  bp : p + 3 + r + 1 < Bv x

theorem keep_neg {c : Com} {P : Env → Prop} {X : Env → List ℕ} {K : ℕ}
    (h : Spec (Bv x) P c (fun σ σ' => σ'.out = σ.out ++ X σ) K)
    (hw : ∀ y, y ∈ c.wvars → y ∈ negVars) (hwa : c.warrs = []) (hr : ¬ c.reads) :
    Spec (Bv x) P c (fun σ σ' => σ'.out = σ.out ++ X σ ∧ Keep negVars σ σ') K :=
  Spec.keep h negVars hw hwa hr

/-- `wseqOf k g n` in the context, as a spec about its values. -/
macro "wseq_phase" : tactic => `(tactic| (
  unfold wseqOf
  run_vcg [wseq_spec (x := x)]
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all [seqL_fresh]
  all_goals (try omega)))

/-- `lexOf` in the context. -/
macro "lex_phase" : tactic => `(tactic| (
  unfold lexOf
  run_vcg [lexCom_spec (x := x)]
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all
  all_goals (try omega)))

variable {p i r c : ℕ}

theorem ph1 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (writes [L 5, L 0, RI 5, L 1, A Y0, L 5, L 4, L 0, RI 2, V "ln"])
      (fun σ σ' => σ'.out = σ.out ++ [5, 0, 5 * i + 5, 1, x.getD (p + 3) 0, 5, 4, 0, 5 * i + 2, r] ∧
        Keep negVars σ σ') 80 := by
  have hl := len_lt_Bv x
  have hx := getD_lt_Bv x (p + 3)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  refine keep_neg ?_ (by intro y hy; simp [writes, Com.wvars] at hy) (by simp [writes, Com.warrs])
    (by simp [writes, Com.reads])
  unfold writes
  run_vcg
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all
  all_goals (try omega)

theorem lexOf_frame (k1 : ℕ) (g1 : Expr) (k2 : ℕ) (g2 : Expr) :
    (∀ y, y ∈ (lexOf k1 g1 k2 g2).wvars → y ∈ negVars) ∧ (lexOf k1 g1 k2 g2).warrs = [] ∧
      ¬ (lexOf k1 g1 k2 g2).reads := by
  refine ⟨fun y hy => ?_, ?_, ?_⟩
  · simp [lexOf, lexCom, lexBody, elems, writes, loop, bump, Com.wvars] at hy
    simp [negVars]; tauto
  · simp [lexOf, lexCom, lexBody, elems, writes, loop, bump, Com.warrs]
  · simp [lexOf, lexCom, lexBody, elems, writes, loop, bump, Com.reads]

theorem wseqOf_frame (k : ℕ) (g n : Expr) :
    (∀ y, y ∈ (wseqOf k g n).wvars → y ∈ negVars) ∧ (wseqOf k g n).warrs = [] ∧
      ¬ (wseqOf k g n).reads := by
  refine ⟨fun y hy => ?_, ?_, ?_⟩
  · simp [wseqOf, wseq, loop, bump, Com.wvars] at hy
    simp [negVars]; tauto
  · simp [wseqOf, wseq, loop, bump, Com.warrs]
  · simp [wseqOf, wseq, loop, bump, Com.reads]

/-- The variables of the atom. -/
abbrev ysOf (x : List ℕ) (p r : ℕ) : List ℕ := seqL x 0 (p + 3) r

theorem ph2 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (wseqOf 1 (V "fc") (V "ln"))
      (fun σ σ' => σ'.out = σ.out ++ List.range' c r ∧ Keep negVars σ σ') (28 * r + 40) := by
  have hl := len_lt_Bv x
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  obtain ⟨f1, f2, f3⟩ := wseqOf_frame 1 (V "fc") (V "ln")
  refine keep_neg ?_ f1 f2 f3
  unfold wseqOf
  run_vcg [wseq_spec (x := x) (n := r)]
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all [seqL_fresh]
  all_goals (try omega)

theorem ph5 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (wseqOf 1 (V "fc") (.mul (L 2) (V "ln")))
      (fun σ σ' => σ'.out = σ.out ++ List.range' c (2 * r) ∧ Keep negVars σ σ') (56 * r + 40) := by
  have hl := len_lt_Bv x
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  obtain ⟨f1, f2, f3⟩ := wseqOf_frame 1 (V "fc") (.mul (L 2) (V "ln"))
  refine keep_neg ?_ f1 f2 f3
  unfold wseqOf
  run_vcg [wseq_spec (x := x) (n := 2 * r)]
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all [seqL_fresh]
  all_goals (try omega)

theorem ph10 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (wseqOf 1 FV (V "ln"))
      (fun σ σ' => σ'.out = σ.out ++ List.range' (c + r) r ∧ Keep negVars σ σ') (28 * r + 40) := by
  have hl := len_lt_Bv x
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  obtain ⟨f1, f2, f3⟩ := wseqOf_frame 1 FV (V "ln")
  refine keep_neg ?_ f1 f2 f3
  unfold wseqOf
  run_vcg [wseq_spec (x := x) (n := r)]
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all [seqL_fresh]
  all_goals (try omega)

theorem ph3 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (lexOf 0 Y0 1 (V "fc"))
      (fun σ σ' => σ'.out = σ.out ++ (lexF (ysOf x p r) (List.range' c r)).encode ∧
        Keep negVars σ σ') (84 * r + 120) := by
  have hl := len_lt_Bv x
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  obtain ⟨f1, f2, f3⟩ := lexOf_frame 0 Y0 1 (V "fc")
  refine keep_neg ?_ f1 f2 f3
  unfold lexOf
  run_vcg [lexCom_spec (x := x) (m := r)]
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all [seqL_fresh]
  all_goals (try omega)
  all_goals (try exact ⟨by omega, by omega, by omega, fun _ => by omega, fun _ => by omega, by omega,
    by omega⟩)

theorem ph7 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (lexOf 1 (V "fc") 0 Y0)
      (fun σ σ' => σ'.out = σ.out ++ (lexF (List.range' c r) (ysOf x p r)).encode ∧
        Keep negVars σ σ') (84 * r + 120) := by
  have hl := len_lt_Bv x
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  obtain ⟨f1, f2, f3⟩ := lexOf_frame 1 (V "fc") 0 Y0
  refine keep_neg ?_ f1 f2 f3
  unfold lexOf
  run_vcg [lexCom_spec (x := x) (m := r)]
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all [seqL_fresh]
  all_goals (try omega)
  all_goals (try exact ⟨by omega, by omega, by omega, fun _ => by omega, fun _ => by omega, by omega,
    by omega⟩)

theorem ph8 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (lexOf 0 Y0 1 FV)
      (fun σ σ' => σ'.out = σ.out ++ (lexF (ysOf x p r) (List.range' (c + r) r)).encode ∧
        Keep negVars σ σ') (84 * r + 120) := by
  have hl := len_lt_Bv x
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  obtain ⟨f1, f2, f3⟩ := lexOf_frame 0 Y0 1 FV
  refine keep_neg ?_ f1 f2 f3
  unfold lexOf
  run_vcg [lexCom_spec (x := x) (m := r)]
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all [seqL_fresh]
  all_goals (try omega)
  all_goals (try exact ⟨by omega, by omega, by omega, fun _ => by omega, fun _ => by omega, by omega,
    by omega⟩)

theorem ph11 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (lexOf 1 FV 0 Y0)
      (fun σ σ' => σ'.out = σ.out ++ (lexF (List.range' (c + r) r) (ysOf x p r)).encode ∧
        Keep negVars σ σ') (84 * r + 120) := by
  have hl := len_lt_Bv x
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  obtain ⟨f1, f2, f3⟩ := lexOf_frame 1 FV 0 Y0
  refine keep_neg ?_ f1 f2 f3
  unfold lexOf
  run_vcg [lexCom_spec (x := x) (m := r)]
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all [seqL_fresh]
  all_goals (try omega)
  all_goals (try exact ⟨by omega, by omega, by omega, fun _ => by omega, fun _ => by omega, by omega,
    by omega⟩)

theorem ph4 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (writes [L 5, L 4, L 0, RI 4, .mul (L 2) (V "ln")])
      (fun σ σ' => σ'.out = σ.out ++ [5, 4, 0, 5 * i + 4, 2 * r] ∧ Keep negVars σ σ') 60 := by
  have hl := len_lt_Bv x
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  refine keep_neg ?_ (by intro y hy; simp [writes, Com.wvars] at hy) (by simp [writes, Com.warrs])
    (by simp [writes, Com.reads])
  unfold writes
  run_vcg
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all
  all_goals (try omega)

theorem ph6 :
    Spec (Bv x) (NC x p i r c) (.write (L 4))
      (fun σ σ' => σ'.out = σ.out ++ [4] ∧ Keep negVars σ σ') 10 := by
  have hl := len_lt_Bv x
  refine keep_neg ?_ (by intro y hy; simp [Com.wvars] at hy) (by simp [Com.warrs])
    (by simp [Com.reads])
  run_vcg
  all_goals simp_all
  all_goals (try omega)

theorem ph9 (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) (writes [L 4, L 0, RI 3, V "ln"])
      (fun σ σ' => σ'.out = σ.out ++ [4, 0, 5 * i + 3, r] ∧ Keep negVars σ σ') 60 := by
  have hl := len_lt_Bv x
  obtain ⟨h1, h2, h3, h4, h5⟩ := hok
  refine keep_neg ?_ (by intro y hy; simp [writes, Com.wvars] at hy) (by simp [writes, Com.warrs])
    (by simp [writes, Com.reads])
  unfold writes
  run_vcg
  all_goals
    (try simp only [NC, Env.setVar] at *)
    simp_all
  all_goals (try omega)

/-- The cost of `negBig`. -/
def Kneg (r : ℕ) : ℕ :=
  80 + ((28 * r + 40) + ((84 * r + 120) + (60 + ((56 * r + 40) + (10 + ((84 * r + 120) +
    ((84 * r + 120) + (60 + ((28 * r + 40) + (84 * r + 120))))))))))

theorem ysOf_head (hr : 1 ≤ r) : (ysOf x p r).headD 0 = x.getD (p + 3) 0 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp [ysOf, seqL, List.range_succ_eq_map, seqE]

/-- **`negBig` writes the code of `negRel`.** -/
theorem negBig_spec (hok : NOK x p i r c) :
    Spec (Bv x) (NC x p i r c) negBig
      (fun σ σ' => σ'.out = σ.out ++ (negRel i (ysOf x p r) c).encode ∧ Keep negVars σ σ')
      (Kneg r) := by
  have hP : ∀ σ σ', NC x p i r c σ → Keep negVars σ σ' → NC x p i r c σ' :=
    fun _ _ h hk => h.keep hk
  have h := Spec.seq_out (ph1 hok) (Spec.seq_out (ph2 hok) (Spec.seq_out (ph3 hok)
    (Spec.seq_out (ph4 hok) (Spec.seq_out (ph5 hok) (Spec.seq_out ph6 (Spec.seq_out (ph7 hok)
    (Spec.seq_out (ph8 hok) (Spec.seq_out (ph9 hok) (Spec.seq_out (ph10 hok) (ph11 hok) hP) hP) hP)
    hP) hP) hP) hP) hP) hP) hP
  refine h.post ?_
  rintro σ σ' - ⟨ho, hk⟩
  refine ⟨?_, hk⟩
  have hpos := hok.pos
  have hne : ysOf x p r ≠ [] := by
    intro h; have := congrArg List.length h; simp only [length_seqL, List.length_nil] at this; omega
  rw [ho, encode_negRel i _ c hne, ysOf_head hok.pos]
  simp only [length_seqL, ysOf, List.append_assoc, List.cons_append, List.nil_append]

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PNeg
