import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PCmp
import Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct

/-! # The scans for the first, the last and the next tuple

The tuples of the current symbol are `LR w o c r`: `c` tuples of length `r` from position `o` of
the array `R`. `minFind` and `maxFind` leave in `bs` the index of the first and of the last tuple;
`succFind` leaves in `fd`, `bs` whether tuple `js` has a successor and its index. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFind

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PCmp
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct

/-- The tuples of the current symbol. -/
def LR (w : List ℕ) (o c r : ℕ) : List (List ℕ) := (List.range c).map fun j => tupR w (o + j * r) r

@[simp] theorem length_LR (w : List ℕ) (o c r : ℕ) : (LR w o c r).length = c := by simp [LR]

theorem LR_get {w : List ℕ} {o c r j : ℕ} (hj : j < c) :
    (LR w o c r)[j]'(by simpa using hj) = tupR w (o + j * r) r := by simp [LR]

theorem LR_take_succ {w : List ℕ} {o c r j : ℕ} (hj : j < c) :
    (LR w o c r).take (j + 1) = (LR w o c r).take j ++ [tupR w (o + j * r) r] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simpa using hj), LR_get hj]; rfl

theorem LR_headD {w : List ℕ} {o c r : ℕ} (hc : 0 < c) : (LR w o c r).headD [] = tupR w o r := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  simp [LR, List.range_succ_eq_map]

theorem LR_head?_getD {w : List ℕ} {o c r : ℕ} (hc : 0 < c) :
    (LR w o c r).head?.getD [] = tupR w o r := by
  rw [← LR_headD hc]; cases LR w o c r <;> rfl

variable {B : ℕ}

/-- The values the scans need below the bound. -/
structure SymOK (B : ℕ) (w : List ℕ) (o c r : ℕ) : Prop where
  len : o + c * r ≤ w.length
  ent : ∀ v ∈ w, v < B
  big : o + c * r + c + r + 8 < B

theorem tup_le {o c r j : ℕ} (hj : j < c) : o + j * r + r ≤ o + c * r := by
  have := Nat.mul_le_mul_right r (show j + 1 ≤ c by omega)
  rw [Nat.succ_mul] at this; omega

theorem jr_le {c r j : ℕ} (hj : j < c) : j * r ≤ c * r := Nat.mul_le_mul_right r hj.le

theorem SymOK.cmp {w : List ℕ} {o c r : ℕ} (h : SymOK B w o c r) {j k : ℕ} (hj : j < c)
    (hk : k < c) : CmpOK B w (o + j * r) (o + k * r) r :=
  ⟨(tup_le hj).trans h.len, (tup_le hk).trans h.len, h.ent,
    by have := tup_le (o := o) (r := r) hj; have := h.big; omega,
    by have := tup_le (o := o) (r := r) hk; have := h.big; omega,
    by have := h.big; omega⟩

/-- The symbol context. -/
def SC (w : List ℕ) (o c r : ℕ) (σ : Env) : Prop :=
  σ.arrs "R" = w ∧ σ.vars "o" = o ∧ σ.vars "c" = c ∧ σ.vars "r" = r

/-! ### The first tuple -/

/-- The invariant of `minFind`. -/
def MinI (w : List ℕ) (o c r : ℕ) (σ : Env) : Prop :=
  SC w o c r σ ∧ σ.vars "j" ≤ c ∧ (σ.vars "bs" = 0 ∨ σ.vars "bs" < σ.vars "j") ∧
    tupR w (o + σ.vars "bs" * r) r =
      ((LR w o c r).take (σ.vars "j")).foldl minStep ((LR w o c r).headD [])

theorem minI_step {w : List ℕ} {o c r j bs : ℕ} (hj : j < c)
    (hm : tupR w (o + bs * r) r = ((LR w o c r).take j).foldl minStep ((LR w o c r).headD [])) :
    tupR w (o + (if tupR w (o + j * r) r < tupR w (o + bs * r) r then j else bs) * r) r =
      ((LR w o c r).take (j + 1)).foldl minStep ((LR w o c r).headD []) := by
  rw [LR_take_succ hj, List.foldl_append, ← hm]
  simp only [List.foldl_cons, List.foldl_nil, minStep]
  split_ifs <;> rfl

set_option maxHeartbeats 4000000 in
theorem minBody_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (fun σ => MinI w o c r σ ∧ σ.vars "j" < c) minBody
      (fun σ σ' => MinI w o c r σ' ∧ σ'.vars "j" = σ.vars "j" + 1) (64 * r + 60) := by
  have hbig := hs.big
  refine Spec.pre (P := fun σ => (MinI w o c r σ ∧ σ.vars "j" < c) ∧
    σ.vars "o" + σ.vars "j" * σ.vars "r" < B ∧ σ.vars "o" + σ.vars "bs" * σ.vars "r" < B ∧
    σ.vars "j" * σ.vars "r" < B ∧ σ.vars "bs" * σ.vars "r" < B ∧ σ.vars "j" + 1 < B ∧
    σ.vars "j" < B ∧ σ.vars "bs" < B ∧ σ.vars "o" < B ∧ σ.vars "r" < B) ?_ ?_
  · unfold minBody
    run_vcg [cmp_spec' (B := B) (w := w) (r := r)]
    all_goals
      obtain ⟨⟨hR, ho, hc, hr⟩, hj, hbs, hm⟩ := ‹MinI w o c r σ›
    all_goals first
      | (refine ⟨by simp [Env.setVar, hR], by simp [Env.setVar, hr], ?_⟩
         simp only [Env.setVar, ite_true, ite_false, String.reduceEq, ho, hr]
         exact hs.cmp ‹_› (by omega))
      | (simp [Env.setVar]; omega)
      | skip
    all_goals
      obtain ⟨hlt, hkv, hka, -⟩ := ‹_ ∧ Keep ["dd", "lt", "l1"] _ _›
      have eo := hkv "o" (by decide)
      have ej := hkv "j" (by decide)
      have ebs := hkv "bs" (by decide)
      have ec := hkv "c" (by decide)
      have er := hkv "r" (by decide)
      have hR' := congrFun hka "R"
      simp only [Env.setVar] at eo ej ebs ec er hlt hR'
      simp only [ite_true, ite_false, String.reduceEq] at eo ej ebs ec er hlt hR'
      rw [ho, hr] at hlt
      have hst := minI_step (w := w) (bs := σ.vars "bs") ‹σ.vars "j" < c› hm
      have hjc : σ.vars "j" < c := ‹_›
      clear hkv hka
      by_cases hC : tupR w (o + σ.vars "j" * r) r < tupR w (o + σ.vars "bs" * r) r
      · rw [if_pos hC] at hlt hst
        simp only [MinI, SC, Env.setVar] at *
        simp_all
        all_goals first | omega | (split_ifs <;> omega)
      · rw [if_neg hC] at hlt hst
        simp only [MinI, SC, Env.setVar] at *
        simp_all
        all_goals first | omega | (split_ifs <;> omega)
    all_goals done
  · rintro σ ⟨⟨⟨hR, ho, hc, hr⟩, hj, hbs, hm⟩, hjc⟩
    have h1 := jr_le (r := r) hjc
    have h2 : σ.vars "bs" * r ≤ c * r := jr_le (by omega)
    refine ⟨⟨⟨⟨hR, ho, hc, hr⟩, hj, hbs, hm⟩, hjc⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [ho, hr]) <;> omega

/-- The invariant of `maxFind`. -/
def MaxI (w : List ℕ) (o c r : ℕ) (σ : Env) : Prop :=
  SC w o c r σ ∧ σ.vars "j" ≤ c ∧ (σ.vars "bs" = 0 ∨ σ.vars "bs" < σ.vars "j") ∧
    tupR w (o + σ.vars "bs" * r) r =
      ((LR w o c r).take (σ.vars "j")).foldl maxStep ((LR w o c r).headD [])

theorem maxI_step {w : List ℕ} {o c r j bs : ℕ} (hj : j < c)
    (hm : tupR w (o + bs * r) r = ((LR w o c r).take j).foldl maxStep ((LR w o c r).headD [])) :
    tupR w (o + (if tupR w (o + bs * r) r < tupR w (o + j * r) r then j else bs) * r) r =
      ((LR w o c r).take (j + 1)).foldl maxStep ((LR w o c r).headD []) := by
  rw [LR_take_succ hj, List.foldl_append, ← hm]
  simp only [List.foldl_cons, List.foldl_nil, maxStep]
  split_ifs <;> rfl

set_option maxHeartbeats 4000000 in
theorem maxBody_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (fun σ => MaxI w o c r σ ∧ σ.vars "j" < c) maxBody
      (fun σ σ' => MaxI w o c r σ' ∧ σ'.vars "j" = σ.vars "j" + 1) (64 * r + 60) := by
  have hbig := hs.big
  refine Spec.pre (P := fun σ => (MaxI w o c r σ ∧ σ.vars "j" < c) ∧
    σ.vars "o" + σ.vars "j" * σ.vars "r" < B ∧ σ.vars "o" + σ.vars "bs" * σ.vars "r" < B ∧
    σ.vars "j" * σ.vars "r" < B ∧ σ.vars "bs" * σ.vars "r" < B ∧ σ.vars "j" + 1 < B ∧
    σ.vars "j" < B ∧ σ.vars "bs" < B ∧ σ.vars "o" < B ∧ σ.vars "r" < B) ?_ ?_
  · unfold maxBody
    run_vcg [cmp_spec' (B := B) (w := w) (r := r)]
    all_goals
      obtain ⟨⟨hR, ho, hc, hr⟩, hj, hbs, hm⟩ := ‹MaxI w o c r σ›
    all_goals first
      | (refine ⟨by simp [Env.setVar, hR], by simp [Env.setVar, hr], ?_⟩
         simp only [Env.setVar, ite_true, ite_false, String.reduceEq, ho, hr]
         exact hs.cmp (by omega) ‹_›)
      | (simp [Env.setVar]; omega)
      | skip
    all_goals
      obtain ⟨hlt, hkv, hka, -⟩ := ‹_ ∧ Keep ["dd", "lt", "l1"] _ _›
      have eo := hkv "o" (by decide)
      have ej := hkv "j" (by decide)
      have ebs := hkv "bs" (by decide)
      have ec := hkv "c" (by decide)
      have er := hkv "r" (by decide)
      have hR' := congrFun hka "R"
      simp only [Env.setVar] at eo ej ebs ec er hlt hR'
      simp only [ite_true, ite_false, String.reduceEq] at eo ej ebs ec er hlt hR'
      rw [ho, hr] at hlt
      have hst := maxI_step (w := w) (bs := σ.vars "bs") ‹σ.vars "j" < c› hm
      have hjc : σ.vars "j" < c := ‹_›
      clear hkv hka
      by_cases hC : tupR w (o + σ.vars "bs" * r) r < tupR w (o + σ.vars "j" * r) r
      · rw [if_pos hC] at hlt hst
        simp only [MaxI, SC, Env.setVar] at *
        simp_all
        all_goals first | omega | (split_ifs <;> omega)
      · rw [if_neg hC] at hlt hst
        simp only [MaxI, SC, Env.setVar] at *
        simp_all
        all_goals first | omega | (split_ifs <;> omega)
    all_goals done
  · rintro σ ⟨⟨⟨hR, ho, hc, hr⟩, hj, hbs, hm⟩, hjc⟩
    have h1 := jr_le (r := r) hjc
    have h2 : σ.vars "bs" * r ≤ c * r := jr_le (by omega)
    refine ⟨⟨⟨⟨hR, ho, hc, hr⟩, hj, hbs, hm⟩, hjc⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (try simp only [ho, hr]) <;> omega


theorem take_LR (w : List ℕ) (o c r : ℕ) : (LR w o c r).take c = LR w o c r :=
  List.take_of_length_le (by simp)

/-- The scalars `minFind` and `maxFind` assign. -/
def findVars : List String := ["bs", "j", "x1", "x2", "dd", "lt", "l1"]

theorem minFind_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) (hc : 0 < c) :
    Spec B (SC w o c r) minFind
      (fun σ σ' => (SC w o c r σ' ∧ σ'.vars "bs" < c ∧
        tupR w (o + σ'.vars "bs" * r) r = minL (LR w o c r)) ∧ Keep findVars σ σ' ∧
        σ'.out = σ.out)
      ((64 * r + 60 + 4) * c + 8) := by
  have hbig := hs.big
  have hloop := Spec.forRangeZero (B := B) (c := minBody) "j" "c" (MinI w o c r) c (64 * r + 60)
    (by omega) (fun σ h => h.2.1) (fun σ h => h.1.2.2.1) (minBody_spec hs)
  have h : Spec B (SC w o c r) minFind
      (fun _ σ' => SC w o c r σ' ∧ σ'.vars "bs" < c ∧
        tupR w (o + σ'.vars "bs" * r) r = minL (LR w o c r)) ((64 * r + 60 + 4) * c + 8) := by
    unfold minFind loop
    run_vcg [hloop]
    all_goals first
      | (obtain ⟨⟨hsc, -, hbs, hm⟩, hj⟩ := ‹MinI w o c r _ ∧ _›
         rw [hj, take_LR] at hm
         exact ⟨hsc, by omega, hm⟩)
      | (obtain ⟨hR, ho, hc', hr⟩ := ‹SC w o c r σ›
         refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hR, ho, hc', hr, LR_headD hc, LR_head?_getD hc])
      | omega
  intro σ hσ
  have h' := Spec.keepOut h findVars
    (by intro y hy; simp [minFind, minBody, loop, cmpC, cmpStep, bump, Com.wvars] at hy
        simp [findVars]; tauto)
    (by simp [minFind, minBody, loop, cmpC, cmpStep, bump, Com.warrs])
    (by simp [minFind, minBody, loop, cmpC, cmpStep, bump, Com.reads])
    (by simp [minFind, minBody, loop, cmpC, cmpStep, bump, Com.NoWrite])
  exact h' σ hσ

theorem maxFind_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) (hc : 0 < c) :
    Spec B (SC w o c r) maxFind
      (fun σ σ' => (SC w o c r σ' ∧ σ'.vars "bs" < c ∧
        tupR w (o + σ'.vars "bs" * r) r = maxL (LR w o c r)) ∧ Keep findVars σ σ' ∧
        σ'.out = σ.out)
      ((64 * r + 60 + 4) * c + 8) := by
  have hbig := hs.big
  have hloop := Spec.forRangeZero (B := B) (c := maxBody) "j" "c" (MaxI w o c r) c (64 * r + 60)
    (by omega) (fun σ h => h.2.1) (fun σ h => h.1.2.2.1) (maxBody_spec hs)
  have h : Spec B (SC w o c r) maxFind
      (fun _ σ' => SC w o c r σ' ∧ σ'.vars "bs" < c ∧
        tupR w (o + σ'.vars "bs" * r) r = maxL (LR w o c r)) ((64 * r + 60 + 4) * c + 8) := by
    unfold maxFind loop
    run_vcg [hloop]
    all_goals first
      | (obtain ⟨⟨hsc, -, hbs, hm⟩, hj⟩ := ‹MaxI w o c r _ ∧ _›
         rw [hj, take_LR] at hm
         exact ⟨hsc, by omega, hm⟩)
      | (obtain ⟨hR, ho, hc', hr⟩ := ‹SC w o c r σ›
         refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hR, ho, hc', hr, LR_headD hc, LR_head?_getD hc])
      | omega
  intro σ hσ
  have h' := Spec.keepOut h findVars
    (by intro y hy; simp [maxFind, maxBody, loop, cmpC, cmpStep, bump, Com.wvars] at hy
        simp [findVars]; tauto)
    (by simp [maxFind, maxBody, loop, cmpC, cmpStep, bump, Com.warrs])
    (by simp [maxFind, maxBody, loop, cmpC, cmpStep, bump, Com.reads])
    (by simp [maxFind, maxBody, loop, cmpC, cmpStep, bump, Com.NoWrite])
  exact h' σ hσ


/-! ### The next tuple -/

/-- The scan's result so far, as the state holds it. -/
def accOf (w : List ℕ) (o r fd bs : ℕ) : Option (List ℕ) :=
  if fd = 0 then none else some (tupR w (o + bs * r) r)

/-- The invariant of `succFind`, for tuple `js`. -/
def SuI (w : List ℕ) (o c r js : ℕ) (σ : Env) : Prop :=
  SC w o c r σ ∧ σ.vars "js" = js ∧ σ.vars "w" ≤ c ∧ σ.vars "fd" ≤ 1 ∧
    (σ.vars "bs" = 0 ∨ σ.vars "bs" < σ.vars "w") ∧
    accOf w o r (σ.vars "fd") (σ.vars "bs") =
      ((LR w o c r).take (σ.vars "w")).foldl (succStep (tupR w (o + js * r) r)) none

theorem suI_step {w : List ℕ} {o c r js wi : ℕ} (hj : wi < c) (acc : Option (List ℕ))
    (hacc : acc = ((LR w o c r).take wi).foldl (succStep (tupR w (o + js * r) r)) none) :
    ((LR w o c r).take (wi + 1)).foldl (succStep (tupR w (o + js * r) r)) none =
      succStep (tupR w (o + js * r) r) acc (tupR w (o + wi * r) r) := by
  rw [LR_take_succ hj, List.foldl_append, ← hacc]; rfl

/-- The scalars `sfInner` assigns. -/
def innerVars : List String := ["fd", "bs", "x1", "x2", "dd", "lt", "l1"]

set_option maxHeartbeats 4000000 in
theorem sfInner_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (fun σ => SC w o c r σ ∧ σ.vars "fd" ≤ 1 ∧ σ.vars "w" < c ∧ σ.vars "bs" < c)
      sfInner
      (fun σ σ' => (σ'.vars "fd" = 1 ∧ σ'.vars "bs" = (if σ.vars "fd" = 0 then σ.vars "w" else
        if tupR w (o + σ.vars "w" * r) r < tupR w (o + σ.vars "bs" * r) r then σ.vars "w"
          else σ.vars "bs")) ∧ Keep innerVars σ σ') (64 * r + 60) := by
  have hbig := hs.big
  have h : Spec B (fun σ => (SC w o c r σ ∧ σ.vars "fd" ≤ 1 ∧ σ.vars "w" < c ∧ σ.vars "bs" < c) ∧
      σ.vars "o" + σ.vars "w" * σ.vars "r" < B ∧ σ.vars "o" + σ.vars "bs" * σ.vars "r" < B ∧
      σ.vars "w" * σ.vars "r" < B ∧ σ.vars "bs" * σ.vars "r" < B ∧ σ.vars "w" < B ∧
      σ.vars "bs" < B ∧ σ.vars "o" < B ∧ σ.vars "r" < B ∧ σ.vars "fd" < B)
      sfInner
      (fun σ σ' => σ'.vars "fd" = 1 ∧ σ'.vars "bs" = (if σ.vars "fd" = 0 then σ.vars "w" else
        if tupR w (o + σ.vars "w" * r) r < tupR w (o + σ.vars "bs" * r) r then σ.vars "w"
          else σ.vars "bs")) (64 * r + 60) := by
    unfold sfInner
    run_vcg [cmp_spec' (B := B) (w := w) (r := r)]
    all_goals
      obtain ⟨hR, ho, hc, hr⟩ := ‹SC w o c r σ›
    all_goals first
      | (refine ⟨by simp [Env.setVar, hR], by simp [Env.setVar, hr], ?_⟩
         simp only [Env.setVar, ite_true, ite_false, String.reduceEq, ho, hr]
         exact hs.cmp ‹_› ‹_›)
      | (simp [Env.setVar]; omega)
      | (simp_all [Env.setVar]; done)
      | skip
    all_goals
      obtain ⟨hlt, hkv, hka, -⟩ := ‹_ ∧ Keep ["dd", "lt", "l1"] _ _›
      have ew := hkv "w" (by decide)
      have ebs := hkv "bs" (by decide)
      have efd := hkv "fd" (by decide)
      simp only [Env.setVar] at ew ebs efd hlt
      simp only [ite_true, ite_false, String.reduceEq] at ew ebs efd hlt
      rw [ho, hr] at hlt
      clear hkv hka
      by_cases hC : tupR w (o + σ.vars "w" * r) r < tupR w (o + σ.vars "bs" * r) r
      · rw [if_pos hC] at hlt
        simp only [Env.setVar] at *
        simp_all
        all_goals first | omega | (split_ifs <;> omega)
      · rw [if_neg hC] at hlt
        simp only [Env.setVar] at *
        simp_all
        all_goals first | omega | (split_ifs <;> omega)
  intro σ hσ
  have h' := Spec.keep h innerVars
    (by intro y hy; simp [sfInner, loop, cmpC, cmpStep, bump, Com.wvars] at hy
        simp [innerVars]; tauto)
    (by simp [sfInner, loop, cmpC, cmpStep, bump, Com.warrs])
    (by simp [sfInner, loop, cmpC, cmpStep, bump, Com.reads])
  obtain ⟨hR, ho, hc, hr⟩ := hσ.1
  have h1 := jr_le (r := r) hσ.2.2.1
  have h2 := jr_le (r := r) hσ.2.2.2
  refine h' σ ⟨hσ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [ho, hr]) <;> omega

theorem sf_pos {w : List ℕ} {o r fd bs wi : ℕ} {u : List ℕ} (hfd : fd ≤ 1)
    (hu : u < tupR w (o + wi * r) r) :
    accOf w o r 1 (if fd = 0 then wi else
      if tupR w (o + wi * r) r < tupR w (o + bs * r) r then wi else bs) =
      succStep u (accOf w o r fd bs) (tupR w (o + wi * r) r) := by
  unfold accOf succStep
  rw [if_pos hu]
  by_cases h0 : fd = 0
  · simp [h0]
  · have h1 : fd = 1 := by omega
    subst h1
    simp only [one_ne_zero, if_false]
    split_ifs <;> rfl

theorem sf_neg {w : List ℕ} {o r fd bs wi : ℕ} {u : List ℕ} (hu : ¬ u < tupR w (o + wi * r) r) :
    accOf w o r fd bs = succStep u (accOf w o r fd bs) (tupR w (o + wi * r) r) := by
  unfold succStep; rw [if_neg hu]

theorem suI_next {w : List ℕ} {o c r js : ℕ} {σ τ : Env} (h : SuI w o c r js σ)
    (hwc : σ.vars "w" < c) (hR : τ.arrs "R" = w) (ho : τ.vars "o" = o) (hc : τ.vars "c" = c)
    (hr : τ.vars "r" = r) (hjs : τ.vars "js" = js) (hw : τ.vars "w" = σ.vars "w" + 1)
    (hfd : τ.vars "fd" ≤ 1) (hbs : τ.vars "bs" = 0 ∨ τ.vars "bs" < τ.vars "w")
    (hacc : accOf w o r (τ.vars "fd") (τ.vars "bs") = succStep (tupR w (o + js * r) r)
      (accOf w o r (σ.vars "fd") (σ.vars "bs")) (tupR w (o + σ.vars "w" * r) r)) :
    SuI w o c r js τ := by
  refine ⟨⟨hR, ho, hc, hr⟩, hjs, by omega, hfd, hbs, ?_⟩
  rw [hacc, hw, suI_step hwc _ h.2.2.2.2.2]

set_option maxHeartbeats 8000000 in
theorem sfBody_spec {w : List ℕ} {o c r js : ℕ} (hs : SymOK B w o c r) (hjs : js < c) :
    Spec B (fun σ => SuI w o c r js σ ∧ σ.vars "w" < c) sfBody
      (fun σ σ' => SuI w o c r js σ' ∧ σ'.vars "w" = σ.vars "w" + 1) (128 * r + 120) := by
  have hbig := hs.big
  refine Spec.pre (P := fun σ => (SuI w o c r js σ ∧ σ.vars "w" < c) ∧
    σ.vars "o" + σ.vars "w" * σ.vars "r" < B ∧ σ.vars "o" + σ.vars "bs" * σ.vars "r" < B ∧
    σ.vars "o" + σ.vars "js" * σ.vars "r" < B ∧
    σ.vars "w" * σ.vars "r" < B ∧ σ.vars "bs" * σ.vars "r" < B ∧ σ.vars "js" * σ.vars "r" < B ∧
    σ.vars "w" + 1 < B ∧ σ.vars "w" < B ∧ σ.vars "bs" < B ∧ σ.vars "js" < B ∧ σ.vars "o" < B ∧
    σ.vars "r" < B ∧ σ.vars "fd" < B) ?_ ?_
  · unfold sfBody
    run_vcg [cmp_spec' (B := B) (w := w) (r := r), sfInner_spec hs]
    all_goals
      obtain ⟨⟨hR, ho, hc, hr⟩, hj, hw, hfd, hbs, hm⟩ := ‹SuI w o c r js σ›
    all_goals first
      | (refine ⟨by simp [Env.setVar, hR], by simp [Env.setVar, hr], ?_⟩
         simp only [Env.setVar, ite_true, ite_false, String.reduceEq, ho, hr, hj]
         exact hs.cmp hjs ‹_›)
      | (simp [Env.setVar]; omega)
      | skip
    all_goals
      obtain ⟨hlt, hkv, hka, -⟩ := ‹_ ∧ Keep ["dd", "lt", "l1"] _ _›
      have eo := hkv "o" (by decide)
      have ec := hkv "c" (by decide)
      have er := hkv "r" (by decide)
      have ejs := hkv "js" (by decide)
      have ew := hkv "w" (by decide)
      have efd := hkv "fd" (by decide)
      have ebs := hkv "bs" (by decide)
      have hR' := congrFun hka "R"
      simp only [Env.setVar] at eo ec er ejs ew efd ebs hlt hR'
      simp only [ite_true, ite_false, String.reduceEq] at eo ec er ejs ew efd ebs hlt hR'
      rw [ho, hr, hj] at hlt
      clear hkv hka
    all_goals first
      | (show SC w o c r _ ∧ _ ∧ _ ∧ _
         refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
           (first
             | (rw [hR', hR]; done)
             | (rw [eo, ho]; done)
             | (rw [ec, hc]; done)
             | (rw [er, hr]; done)
             | (rw [efd]; omega)
             | (rw [ew]; omega)
             | (rw [ebs]; omega)))
      | (rw [ew]; omega)
      | skip
    all_goals first
      | (rw [hlt]; split_ifs <;> omega)
      | (obtain ⟨-, hkv2, -, -⟩ := ‹(_ ∧ _) ∧ Keep innerVars _ _›
         have e := hkv2 "w" (by decide); rw [e, ew]; omega)
      | skip
    all_goals first
      | (obtain ⟨⟨hfd2, hbs2⟩, hkv2, hka2, -⟩ := ‹(_ ∧ _) ∧ Keep innerVars _ _›
         have eo2 := hkv2 "o" (by decide)
         have ec2 := hkv2 "c" (by decide)
         have er2 := hkv2 "r" (by decide)
         have ejs2 := hkv2 "js" (by decide)
         have ew2 := hkv2 "w" (by decide)
         have hR2 := congrFun hka2 "R"
         rw [ew, efd, ebs] at hbs2
         clear hkv2 hka2
         have hu : tupR w (o + js * r) r < tupR w (o + σ.vars "w" * r) r := by
           by_contra hn; rw [if_neg hn] at hlt; simp_all
         refine ⟨suI_next ‹_› ‹_› ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩ <;> (try simp only [Env.setVar]) <;>
           (try simp only [ite_true, ite_false, String.reduceEq])
         all_goals first
           | (rw [hR2, hR', hR]; done)
           | (rw [eo2, eo, ho]; done)
           | (rw [ec2, ec, hc]; done)
           | (rw [er2, er, hr]; done)
           | (rw [ejs2, ejs, hj]; done)
           | (rw [ew2, ew]; done)
           | (rw [hfd2]; (try omega); done)
           | (rw [ew2, ew, hbs2]; split_ifs <;> omega)
           | (rw [hbs2]; split_ifs <;> omega)
           | (rw [hfd2, hbs2, ew]; exact sf_pos hfd hu)
           | (rw [hbs2]; exact sf_pos hfd hu)
           | (rw [hfd2, hbs2]; exact sf_pos hfd hu))
      | skip
    all_goals first
      | (have hu : ¬ tupR w (o + js * r) r < tupR w (o + σ.vars "w" * r) r := by
           intro hp; rw [if_pos hp] at hlt; simp_all
         refine ⟨suI_next ‹_› ‹_› ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩ <;> (try simp only [Env.setVar]) <;>
           (try simp only [ite_true, ite_false, String.reduceEq])
         all_goals first
           | (rw [hR', hR]; done)
           | (rw [eo, ho]; done)
           | (rw [ec, hc]; done)
           | (rw [er, hr]; done)
           | (rw [ejs, hj]; done)
           | (rw [ew]; done)
           | (rw [efd]; omega)
           | (rw [ebs, ew]; omega)
           | (rw [ebs, ew, ew]; omega)
           | (rw [ebs]; omega)
           | (rw [efd, ebs]; exact sf_neg hu))
      | skip
    all_goals done
  · rintro σ ⟨⟨⟨hR, ho, hc, hr⟩, hj, hw, hfd, hbs, hm⟩, hwc⟩
    have h1 := jr_le (r := r) hwc
    have h2 : σ.vars "bs" * r ≤ c * r := jr_le (by omega)
    have h3 : js * r ≤ c * r := jr_le hjs
    refine ⟨⟨⟨⟨hR, ho, hc, hr⟩, hj, hw, hfd, hbs, hm⟩, hwc⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;> (try simp only [ho, hr, hj]) <;> omega


/-- The scalars `succFind` assigns. -/
def succVars : List String := ["fd", "bs", "w", "x1", "x2", "dd", "lt", "l1"]

/-- **The successor scan.** -/
theorem succFind_spec {w : List ℕ} {o c r js : ℕ} (hs : SymOK B w o c r) (hjs : js < c) :
    Spec B (fun σ => SC w o c r σ ∧ σ.vars "js" = js) succFind
      (fun σ σ' => (SC w o c r σ' ∧ σ'.vars "js" = js ∧ σ'.vars "fd" ≤ 1 ∧ σ'.vars "bs" < c ∧
        accOf w o r (σ'.vars "fd") (σ'.vars "bs") = succOf (LR w o c r) (tupR w (o + js * r) r)) ∧
        Keep succVars σ σ' ∧ σ'.out = σ.out) (4 + ((128 * r + 120 + 4) * c + 6)) := by
  have hbig := hs.big
  have hloop := Spec.forRangeZero (B := B) (c := sfBody) "w" "c" (SuI w o c r js) c (128 * r + 120)
    (by omega) (fun σ h => h.2.2.1) (fun σ h => h.1.2.2.1) (sfBody_spec hs hjs)
  have h : Spec B (fun σ => SC w o c r σ ∧ σ.vars "js" = js) succFind
      (fun _ σ' => SC w o c r σ' ∧ σ'.vars "js" = js ∧ σ'.vars "fd" ≤ 1 ∧ σ'.vars "bs" < c ∧
        accOf w o r (σ'.vars "fd") (σ'.vars "bs") = succOf (LR w o c r) (tupR w (o + js * r) r))
      (4 + ((128 * r + 120 + 4) * c + 6)) := by
    unfold succFind loop
    run_vcg [hloop]
    all_goals first
      | (obtain ⟨⟨hsc, hj, -, hfd, hbs, hm⟩, hw⟩ := ‹SuI w o c r js _ ∧ _›
         rw [hw, take_LR] at hm
         exact ⟨hsc, hj, hfd, by omega, hm⟩)
      | (obtain ⟨hR, ho, hc', hr⟩ := ‹SC w o c r σ›
         have hj : σ.vars "js" = js := ‹_›
         refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
           simp [Env.setVar, hR, ho, hc', hr, hj, accOf])
      | omega
  intro σ hσ
  have h' := Spec.keepOut h succVars
    (by intro y hy; simp [succFind, sfBody, sfInner, loop, cmpC, cmpStep, bump, Com.wvars] at hy
        simp [succVars]; tauto)
    (by simp [succFind, sfBody, sfInner, loop, cmpC, cmpStep, bump, Com.warrs])
    (by simp [succFind, sfBody, sfInner, loop, cmpC, cmpStep, bump, Com.reads])
    (by simp [succFind, sfBody, sfInner, loop, cmpC, cmpStep, bump, Com.NoWrite])
  exact h' σ hσ

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFind
