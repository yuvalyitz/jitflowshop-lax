import Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFind

/-! # The five blocks of one symbol

`symW` writes, for the tuples `L = LR w o c r` of the current symbol, the relation itself, the first
tuple, the last tuple, the pairs of consecutive tuples and `Z` (`symOut`). -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PSym

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.NegElim.PCmp
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.PFind Lax496464Proofs.WHierarchy.Lemmas.NegElim.Struct

variable {B : ℕ}

/-! ### Mathematics -/

theorem tupR_add (w : List ℕ) (g a : ℕ) : ∀ b, tupR w g (a + b) = tupR w g a ++ tupR w (g + a) b
  | 0 => by simp [tupR]
  | b + 1 => by
    rw [← Nat.add_assoc, tupR_succ, tupR_add w g a b, tupR_succ, List.append_assoc, Nat.add_assoc]

/-- The entries of the tuples, in order. -/
theorem flatten_LR (w : List ℕ) (o r : ℕ) : ∀ c, (LR w o c r).flatten = tupR w o (c * r)
  | 0 => by simp [LR, tupR]
  | c + 1 => by
    have ih := flatten_LR w o r c
    rw [show LR w o (c + 1) r = LR w o c r ++ [tupR w (o + c * r) r] by
      simp [LR, List.range_succ], List.flatten_append, ih, Nat.succ_mul, tupR_add]
    simp

/-- What the successor part writes for one tuple. -/
def sItem (L : List (List ℕ)) (u : List ℕ) : List ℕ :=
  match succOf L u with
  | some v => u ++ v
  | none => []

/-- What the successor part has written after `j` tuples. -/
def sAcc (L : List (List ℕ)) (j : ℕ) : List ℕ :=
  ((L.take j).filterMap fun u => (succOf L u).map (u ++ ·)).flatten

theorem sAcc_succ {w : List ℕ} {o c r j : ℕ} (hj : j < c) :
    sAcc (LR w o c r) (j + 1) = sAcc (LR w o c r) j ++ sItem (LR w o c r) (tupR w (o + j * r) r) := by
  unfold sAcc sItem
  rw [LR_take_succ hj, List.filterMap_append, List.flatten_append]
  congr 1
  rcases h : succOf (LR w o c r) (tupR w (o + j * r) r) with _ | v
  · simp [h]
  · simp [h]

theorem sAcc_full (w : List ℕ) (o c r : ℕ) :
    sAcc (LR w o c r) c = (sList (LR w o c r)).flatten := by
  unfold sAcc sList; rw [take_LR]

/-- **What `symW` writes.** -/
def symOut (w : List ℕ) (o c r M : ℕ) : List ℕ :=
  (c :: tupR w o (c * r)) ++
  (if c = 0 then [0] else 1 :: minL (LR w o c r)) ++
  (if c = 0 then [0] else 1 :: maxL (LR w o c r)) ++
  ((c - 1) :: (sList (LR w o c r)).flatten) ++
  (if c = 0 then M :: List.range M else [0])

/-! ### Writing a tuple -/

theorem wTup_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) (x : String) :
    Spec B (fun σ => SC w o c r σ ∧ σ.vars x < c) (wTup (tupAt x))
      (fun σ σ' => σ'.out = σ.out ++ tupR w (o + σ.vars x * r) r ∧ Keep ["g", "nn", "l2"] σ σ')
      (24 * r + 20) := by
  have hbig := hs.big
  have hle := hs.len
  have h : Spec B (fun σ => (SC w o c r σ ∧ σ.vars x < c) ∧ σ.vars "o" + σ.vars x * σ.vars "r" < B ∧
      σ.vars x * σ.vars "r" < B ∧ σ.vars "r" < B ∧ σ.vars "o" < B ∧ σ.vars x < B) (wTup (tupAt x))
      (fun σ σ' => σ'.out = σ.out ++ tupR w (o + σ.vars x * r) r) (24 * r + 20) := by
    unfold wTup
    run_vcg [wR_spec' (B := B) (n := r) hs.ent]
    all_goals
      obtain ⟨hR, ho, hc, hr⟩ := ‹SC w o c r σ›
      have hx : σ.vars x < c := ‹_›
      have h1 := tup_le (o := o) (r := r) hx
    all_goals first
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hR, ho, hr] <;> omega)
      | (obtain ⟨ho', -⟩ := ‹_ ∧ Keep ["l2"] _ _›
         rw [ho']; simp [Env.setVar, ho, hr])
      | omega
  intro σ ⟨hsc, hx⟩
  have h' := Spec.keep h ["g", "nn", "l2"]
    (by intro y hy; simp [wTup, wR, loop, bump, Com.wvars] at hy; simp; tauto)
    (by simp [wTup, wR, loop, bump, Com.warrs]) (by simp [wTup, wR, loop, bump, Com.reads])
  obtain ⟨hR, ho, hc, hr⟩ := hsc
  have hxr := jr_le (r := r) hx
  have h1 := tup_le (o := o) (r := r) hx
  exact h' σ ⟨⟨⟨hR, ho, hc, hr⟩, hx⟩, by rw [ho, hr]; omega, by rw [hr]; omega, by rw [hr]; omega,
    by rw [ho]; omega, by omega⟩

/-! ### The relation itself -/

theorem copyBlock_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (SC w o c r) copyBlock
      (fun σ σ' => σ'.out = σ.out ++ (c :: tupR w o (c * r)) ∧ Keep ["g", "nn", "l2"] σ σ')
      (24 * (c * r) + 30) := by
  have hbig := hs.big
  have hle := hs.len
  have h : Spec B (fun σ => SC w o c r σ ∧ σ.vars "c" < B ∧ σ.vars "o" < B ∧
      σ.vars "c" * σ.vars "r" < B) copyBlock
      (fun σ σ' => σ'.out = σ.out ++ (c :: tupR w o (c * r))) (24 * (c * r) + 30) := by
    unfold copyBlock
    run_vcg [wR_spec' (B := B) (n := c * r) hs.ent]
    all_goals
      obtain ⟨hR, ho, hc, hr⟩ := ‹SC w o c r σ›
    all_goals first
      | (refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hR, ho, hr, hc] <;> omega)
      | (obtain ⟨ho', -⟩ := ‹_ ∧ Keep ["l2"] _ _›
         rw [ho']; simp [Env.setVar, ho, hr, hc])
      | omega
      | (simp [Env.setVar, ho, hr, hc]; omega)
  intro σ hσ
  have h' := Spec.keep h ["g", "nn", "l2"]
    (by intro y hy; simp [copyBlock, wR, loop, bump, Com.wvars] at hy; simp; tauto)
    (by simp [copyBlock, wR, loop, bump, Com.warrs]) (by simp [copyBlock, wR, loop, bump, Com.reads])
  obtain ⟨hR, ho, hc, hr⟩ := hσ
  exact h' σ ⟨⟨hR, ho, hc, hr⟩, by rw [hc]; omega, by rw [ho]; omega, by rw [hc, hr]; omega⟩

/-! ### The first and the last tuple -/

theorem minFind_spec' {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (fun σ => SC w o c r σ ∧ 0 < c) minFind
      (fun σ σ' => (SC w o c r σ' ∧ σ'.vars "bs" < c ∧
        tupR w (o + σ'.vars "bs" * r) r = minL (LR w o c r)) ∧ Keep findVars σ σ' ∧
        σ'.out = σ.out)
      ((64 * r + 60 + 4) * c + 8) := fun σ ⟨h1, h2⟩ => minFind_spec hs h2 σ h1

theorem maxFind_spec' {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (fun σ => SC w o c r σ ∧ 0 < c) maxFind
      (fun σ σ' => (SC w o c r σ' ∧ σ'.vars "bs" < c ∧
        tupR w (o + σ'.vars "bs" * r) r = maxL (LR w o c r)) ∧ Keep findVars σ σ' ∧
        σ'.out = σ.out)
      ((64 * r + 60 + 4) * c + 8) := fun σ ⟨h1, h2⟩ => maxFind_spec hs h2 σ h1

/-- The scalars the blocks of one symbol assign. -/
def blkVars : List String := ["g", "nn", "l2", "bs", "j", "x1", "x2", "dd", "lt", "l1", "fd", "w",
  "js", "u"]

/-- The cost of `fBlock` and `lBlock`. -/
def Kfl (c r : ℕ) : ℕ := (64 * r + 60 + 4) * c + 8 + (24 * r + 20) + 20

set_option maxHeartbeats 4000000 in
theorem fBlock_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (SC w o c r) fBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: minL (LR w o c r)) ∧
        Keep blkVars σ σ') (Kfl c r) := by
  have hbig := hs.big
  have h : Spec B (fun σ => SC w o c r σ ∧ σ.vars "c" < B) fBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: minL (LR w o c r))) (Kfl c r) := by
    unfold fBlock Kfl
    run_vcg [minFind_spec' hs, wTup_spec hs "bs"]
    all_goals
      obtain ⟨hR, ho, hc, hr⟩ := ‹SC w o c r σ›
    all_goals first
      | (simp_all; done)
      | (refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> (try simp [Env.setVar, hR, ho, hr, hc])
         omega)
      | (obtain ⟨⟨hsc, hbs, hm⟩, -, -⟩ := ‹(SC w o c r _ ∧ _) ∧ Keep findVars _ _ ∧ _›
         exact ⟨hsc, hbs⟩)
      | (obtain ⟨⟨hsc, hbs, hm⟩, -, hout⟩ := ‹(SC w o c r _ ∧ _) ∧ Keep findVars _ _ ∧ _›
         obtain ⟨ho', -⟩ := ‹_ ∧ Keep ["g", "nn", "l2"] _ _›
         rw [ho', hout, hm, if_neg (by omega)]
         simp)
      | omega
  intro σ hσ
  have h' := Spec.keep h blkVars
    (by intro y hy; simp [fBlock, minFind, minBody, wTup, wR, loop, cmpC, cmpStep, bump,
          Com.wvars] at hy; simp [blkVars]; tauto)
    (by simp [fBlock, minFind, minBody, wTup, wR, loop, cmpC, cmpStep, bump, Com.warrs])
    (by simp [fBlock, minFind, minBody, wTup, wR, loop, cmpC, cmpStep, bump, Com.reads])
  exact h' σ ⟨hσ, by rw [hσ.2.2.1]; omega⟩

set_option maxHeartbeats 4000000 in
theorem lBlock_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (SC w o c r) lBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: maxL (LR w o c r)) ∧
        Keep blkVars σ σ') (Kfl c r) := by
  have hbig := hs.big
  have h : Spec B (fun σ => SC w o c r σ ∧ σ.vars "c" < B) lBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: maxL (LR w o c r))) (Kfl c r) := by
    unfold lBlock Kfl
    run_vcg [maxFind_spec' hs, wTup_spec hs "bs"]
    all_goals
      obtain ⟨hR, ho, hc, hr⟩ := ‹SC w o c r σ›
    all_goals first
      | (simp_all; done)
      | (refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> (try simp [Env.setVar, hR, ho, hr, hc])
         omega)
      | (obtain ⟨⟨hsc, hbs, hm⟩, -, -⟩ := ‹(SC w o c r _ ∧ _) ∧ Keep findVars _ _ ∧ _›
         exact ⟨hsc, hbs⟩)
      | (obtain ⟨⟨hsc, hbs, hm⟩, -, hout⟩ := ‹(SC w o c r _ ∧ _) ∧ Keep findVars _ _ ∧ _›
         obtain ⟨ho', -⟩ := ‹_ ∧ Keep ["g", "nn", "l2"] _ _›
         rw [ho', hout, hm, if_neg (by omega)]
         simp)
      | omega
  intro σ hσ
  have h' := Spec.keep h blkVars
    (by intro y hy; simp [lBlock, maxFind, maxBody, wTup, wR, loop, cmpC, cmpStep, bump,
          Com.wvars] at hy; simp [blkVars]; tauto)
    (by simp [lBlock, maxFind, maxBody, wTup, wR, loop, cmpC, cmpStep, bump, Com.warrs])
    (by simp [lBlock, maxFind, maxBody, wTup, wR, loop, cmpC, cmpStep, bump, Com.reads])
  exact h' σ ⟨hσ, by rw [hσ.2.2.1]; omega⟩

/-! ### Consecutive tuples -/

theorem SC.of_keep {w : List ℕ} {o c r : ℕ} {S : List String} {σ σ' : Env} (h : SC w o c r σ)
    (hk : Keep S σ σ') (hS : "o" ∉ S ∧ "c" ∉ S ∧ "r" ∉ S) : SC w o c r σ' := by
  obtain ⟨hR, ho, hc, hr⟩ := h
  exact ⟨by rw [hk.2.1]; exact hR, by rw [hk.1 _ hS.1]; exact ho, by rw [hk.1 _ hS.2.1]; exact hc,
    by rw [hk.1 _ hS.2.2]; exact hr⟩

theorem succFind_spec' {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (fun σ => SC w o c r σ ∧ σ.vars "js" < c) succFind
      (fun σ σ' => (SC w o c r σ' ∧ σ'.vars "js" = σ.vars "js" ∧ σ'.vars "fd" ≤ 1 ∧
        σ'.vars "bs" < c ∧ accOf w o r (σ'.vars "fd") (σ'.vars "bs") =
          succOf (LR w o c r) (tupR w (o + σ.vars "js" * r) r)) ∧
        Keep succVars σ σ' ∧ σ'.out = σ.out) (4 + ((128 * r + 120 + 4) * c + 6)) :=
  fun σ ⟨h1, h2⟩ => succFind_spec hs h2 σ ⟨h1, rfl⟩

theorem sItem_of_acc {w : List ℕ} {o c r fd bs : ℕ} {u : List ℕ} (hfd : fd ≤ 1)
    (h : accOf w o r fd bs = succOf (LR w o c r) u) :
    sItem (LR w o c r) u = if fd = 1 then u ++ tupR w (o + bs * r) r else [] := by
  unfold sItem
  rw [← h]
  unfold accOf
  split_ifs with h1 h2 h2 <;> first | rfl | omega

theorem SC.setVar {w : List ℕ} {o c r : ℕ} {σ : Env} (h : SC w o c r σ) {y : String} (v : ℕ)
    (hy : y ≠ "o" ∧ y ≠ "c" ∧ y ≠ "r") : SC w o c r (σ.setVar y v) := by
  obtain ⟨hR, ho, hc, hr⟩ := h
  refine ⟨hR, ?_, ?_, ?_⟩ <;> simp [Env.setVar, hy.1.symm, hy.2.1.symm, hy.2.2.symm, ho, hc, hr]

/-- The invariant of `sBlock`. -/
def SBI (w : List ℕ) (o c r : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  SC w o c r σ ∧ σ.vars "js" ≤ c ∧ σ.out = out0 ++ sAcc (LR w o c r) (σ.vars "js")

/-- The cost of one turn of `sBlock`. -/
def Ks (c r : ℕ) : ℕ := 4 + ((128 * r + 120 + 4) * c + 6) + (24 * r + 20) + (24 * r + 20) + 20

theorem sBody_final {w : List ℕ} {o c r : ℕ} {out0 : List ℕ} {σ σ1 σ2 σ3 : Env}
    (hsc : SC w o c r σ1) (hjs : σ1.vars "js" = σ.vars "js")
    (hout : σ.out = out0 ++ sAcc (LR w o c r) (σ.vars "js")) (hout1 : σ1.out = σ.out)
    (hit : sItem (LR w o c r) (tupR w (o + σ.vars "js" * r) r) =
      if σ1.vars "fd" = 1 then tupR w (o + σ.vars "js" * r) r ++ tupR w (o + σ1.vars "bs" * r) r
      else [])
    (hfd1 : σ1.vars "fd" = 1) (hjc : σ.vars "js" < c)
    (ho2 : σ2.out = σ1.out ++ tupR w (o + σ1.vars "js" * r) r) (hk2 : Keep ["g", "nn", "l2"] σ1 σ2)
    (ho3 : σ3.out = σ2.out ++ tupR w (o + σ2.vars "bs" * r) r) (hk3 : Keep ["g", "nn", "l2"] σ2 σ3) :
    SBI w o c r out0 (σ3.setVar "js" (σ3.vars "js" + 1)) ∧
      (σ3.setVar "js" (σ3.vars "js" + 1)).vars "js" = σ.vars "js" + 1 := by
  have e1 := hk2.1 "js" (by decide)
  have e2 := hk3.1 "js" (by decide)
  have e3 := hk2.1 "bs" (by decide)
  have hj3 : (σ3.setVar "js" (σ3.vars "js" + 1)).vars "js" = σ.vars "js" + 1 := by
    simp only [Env.setVar, ite_true]; rw [e2, e1, hjs]
  refine ⟨⟨SC.setVar (SC.of_keep (SC.of_keep hsc hk2 (by decide)) hk3 (by decide)) _
    (by decide), by rw [hj3]; omega, ?_⟩, hj3⟩
  rw [hj3, sAcc_succ hjc, hit, if_pos hfd1]
  show σ3.out = _
  rw [ho3, ho2, e3, hout1, hout, hjs]
  simp

set_option maxHeartbeats 8000000 in
theorem sBody_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) (out0 : List ℕ) :
    Spec B (fun σ => SBI w o c r out0 σ ∧ σ.vars "js" < c) sBody
      (fun σ σ' => SBI w o c r out0 σ' ∧ σ'.vars "js" = σ.vars "js" + 1) (Ks c r) := by
  have hbig := hs.big
  refine Spec.pre (P := fun σ => (SBI w o c r out0 σ ∧ σ.vars "js" < c) ∧ σ.vars "js" + 1 < B) ?_ ?_
  · unfold sBody Ks
    run_vcg [succFind_spec' hs, wTup_spec hs "js", wTup_spec hs "bs"]
    all_goals
      obtain ⟨⟨hR, ho, hc, hr⟩, hj, hout⟩ := ‹SBI w o c r out0 σ›
    all_goals first
      | (exact ⟨⟨hR, ho, hc, hr⟩, ‹_›⟩)
      | skip
    all_goals
      obtain ⟨⟨hsc, hjs, hfd, hbs, hacc⟩, hk, hout1⟩ := ‹(SC w o c r _ ∧ _) ∧ Keep succVars _ _ ∧ _›
      have hit := sItem_of_acc hfd hacc
    all_goals first
      | (exact ⟨hsc, by rw [hjs]; omega⟩)
      | skip
    all_goals first
      | (find_hyp hK3 : _ ∧ Keep ["g", "nn", "l2"] _ _
         obtain ⟨ho3, hk3⟩ := hK3
         first
          | (find_hyp hK2 : _ ∧ Keep ["g", "nn", "l2"] _ _
             obtain ⟨ho2, hk2⟩ := hK2
             have e1 := hk2.1 "js" (by decide)
             have e2 := hk3.1 "js" (by decide)
             have e3 := hk2.1 "bs" (by decide)
             first
              | (rw [e2, e1, hjs]; omega)
              | (find_hyp hfd1 : Env.vars _ "fd" = 1
                 exact sBody_final hsc hjs hout hout1 hit hfd1 (by omega) ho2 hk2 ho3 hk3))
          | (exact ⟨SC.of_keep hsc hk3 (by decide), by rw [hk3.1 "bs" (by decide)]; exact hbs⟩))
      | skip
    all_goals first
      | (rw [hjs]; omega)
      | (show SBI w o c r out0 _ ∧ _
         find_hyp hfd0 : ¬ _ = 1
         refine ⟨⟨SC.setVar hsc _ (by decide), ?_, ?_⟩, ?_⟩
         · simp only [Env.setVar, ite_true]; rw [hjs]; omega
         · simp only [Env.setVar]
           rw [hout1, hout]
           simp only [ite_true]
           rw [hjs, sAcc_succ (j := σ.vars "js") (by omega), hit, if_neg hfd0, List.append_nil]
         · simp only [Env.setVar, ite_true]; rw [hjs])
      | skip
    all_goals done
  · rintro σ ⟨h1, h2⟩
    exact ⟨⟨h1, h2⟩, by omega⟩

/-- The cost of `sBlock`. -/
def KsB (c r : ℕ) : ℕ := (Ks c r + 4) * c + 6 + 5

theorem sBlock_spec {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (SC w o c r) sBlock
      (fun σ σ' => σ'.out = σ.out ++ ((c - 1) :: (sList (LR w o c r)).flatten) ∧ Keep blkVars σ σ')
      (KsB c r) := by
  have hbig := hs.big
  have h : Spec B (fun σ => SC w o c r σ ∧ σ.vars "c" < B) sBlock
      (fun σ σ' => σ'.out = σ.out ++ ((c - 1) :: (sList (LR w o c r)).flatten)) (KsB c r) := by
    intro σ ⟨hsc, hcB⟩
    have hloop := Spec.forRangeZero (B := B) (c := sBody) "js" "c"
      (SBI w o c r (σ.out ++ [c - 1])) c (Ks c r) (by omega) (fun σ h => h.2.1)
      (fun σ h => h.1.2.2.1) (sBody_spec hs _)
    have h2 : Spec B (fun τ => τ = σ) sBlock
        (fun _ σ' => σ'.out = σ.out ++ ((c - 1) :: (sList (LR w o c r)).flatten)) (KsB c r) := by
      unfold sBlock KsB
      run_vcg [hloop]
      all_goals first
        | (obtain ⟨⟨-, -, hout⟩, hj⟩ := ‹SBI w o c r _ _ ∧ _›
           rw [hout, hj, sAcc_full]; simp)
        | (subst_vars
           obtain ⟨hR, ho, hc, hr⟩ := hsc
           refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> simp [Env.setVar, hR, ho, hc, hr, sAcc])
        | (subst_vars; obtain ⟨hR, ho, hc, hr⟩ := hsc; simp [hc]; omega)
    exact h2 σ rfl
  intro σ hσ
  have h' := Spec.keep h blkVars
    (by intro y hy; simp [sBlock, sBody, succFind, sfBody, sfInner, wTup, wR, loop, cmpC, cmpStep,
          bump, Com.wvars] at hy; simp [blkVars]; tauto)
    (by simp [sBlock, sBody, succFind, sfBody, sfInner, wTup, wR, loop, cmpC, cmpStep, bump,
          Com.warrs])
    (by simp [sBlock, sBody, succFind, sfBody, sfInner, wTup, wR, loop, cmpC, cmpStep, bump,
          Com.reads])
  exact h' σ ⟨hσ, by rw [hσ.2.2.1]; omega⟩

/-! ### `Z` -/

/-- The invariant of the loop of `zBlock`. -/
def ZI (M : ℕ) (out0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "M" = M ∧ σ.vars "u" ≤ M ∧ σ.out = out0 ++ List.range (σ.vars "u")

theorem zLoop_spec {M : ℕ} (hM : M + 1 < B) (out0 : List ℕ) :
    Spec B (fun σ => ZI M out0 (σ.setVar "u" 0)) (loop "u" "M" (.seq (.write (V "u")) (bump "u")))
      (fun _ σ' => ZI M out0 σ' ∧ σ'.vars "u" = M) ((10 + 4) * M + 6) := by
  refine Spec.forRangeZero "u" "M" (ZI M out0) M 10 (by omega) (fun σ h => h.2.1)
    (fun σ h => h.1) ?_
  refine Spec.pre (P := fun σ => (ZI M out0 σ ∧ σ.vars "u" < M) ∧ σ.vars "u" + 1 < B) ?_ ?_
  · run_vcg
    all_goals
      obtain ⟨hM', hu, ho⟩ := ‹ZI M out0 σ›
      simp only [ZI, Env.setVar] at *
      simp_all [List.range_succ]
    all_goals omega
  · rintro σ ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by omega⟩

theorem zBlock_spec {M c : ℕ} (hM : M + c + 1 < B) :
    Spec B (fun σ => σ.vars "M" = M ∧ σ.vars "c" = c) zBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then M :: List.range M else [0]) ∧ Keep blkVars σ σ')
      (14 * M + 20) := by
  have h : Spec B (fun σ => σ.vars "M" = M ∧ σ.vars "c" = c) zBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then M :: List.range M else [0])) (14 * M + 20) := by
    intro σ0 ⟨hM', hc⟩
    have hM1 : M + 1 < B := by omega
    have hl := zLoop_spec hM1 (σ0.out ++ [M])
    have h2 : Spec B (fun τ => τ.vars "M" = M ∧ τ.vars "c" = c ∧ τ.out = σ0.out) zBlock
        (fun _ σ' => σ'.out = σ0.out ++ (if c = 0 then M :: List.range M else [0])) (14 * M + 20) := by
      unfold zBlock
      run_vcg [hl]
      all_goals
        have hM2 : _ = M := ‹_›
        have hc2 : _ = c := ‹_›
        have ho2 : _ = σ0.out := ‹_›
      all_goals first
        | (obtain ⟨⟨-, -, hout⟩, hu⟩ := ‹ZI M _ _ ∧ _›
           rw [hout, hu, if_pos (by omega)]; simp)
        | (simp [ZI, Env.setVar, hM2, ho2]; done)
        | (rw [if_neg (by omega)]; simp [ho2])
        | (simp [hM2, hc2]; omega)
        | omega
    exact h2 σ0 ⟨hM', hc, rfl⟩
  intro σ hσ
  have h' := Spec.keep h blkVars
    (by intro y hy; simp [zBlock, loop, bump, Com.wvars] at hy; simp [blkVars]; tauto)
    (by simp [zBlock, loop, bump, Com.warrs]) (by simp [zBlock, loop, bump, Com.reads])
  exact h' σ hσ

/-! ### No tuples: the first and last blocks are cheap -/

theorem ite_c0 {w : List ℕ} {o c r : ℕ} (hc : c = 0) (hB : 2 < B) {d : Com} {X : List ℕ} :
    Spec B (SC w o c r) (.ite (.eq (V "c") (L 0)) (.write (L 0)) d)
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else X) ∧ Keep blkVars σ σ') 10 := by
  have hev : ∀ σ, SC w o c r σ → (Cond.eq (V "c") (L 0)).evalB B σ = some true := by
    intro σ hσ
    have h1 : (V "c").evalB B σ = some 0 := by
      have := evalB_var (B := B) (x := "c") (σ := σ) (by rw [hσ.2.2.1, hc]; omega)
      rwa [hσ.2.2.1, hc] at this
    rw [evalB_condEq h1 (evalB_lit (by omega))]; rfl
  refine (Spec.ite (K := 2) (fun σ h => ⟨_, hev σ h⟩) ?_ ?_).mono (by simp)
  · intro σ ⟨_, _⟩
    refine ⟨{ σ with out := σ.out ++ [0] }, Run.write (evalB_lit (by omega)), ?_, ?_⟩
    · simp [hc]
    · exact ⟨fun _ _ => rfl, rfl, rfl⟩
  · intro σ ⟨hσ, hf⟩
    rw [hev σ hσ] at hf; cases hf

theorem fBlock_spec0 {w : List ℕ} {o c r : ℕ} (hc : c = 0) (hB : 2 < B) :
    Spec B (SC w o c r) fBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: minL (LR w o c r)) ∧
        Keep blkVars σ σ') 10 := ite_c0 hc hB

theorem lBlock_spec0 {w : List ℕ} {o c r : ℕ} (hc : c = 0) (hB : 2 < B) :
    Spec B (SC w o c r) lBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: maxL (LR w o c r)) ∧
        Keep blkVars σ σ') 10 := ite_c0 hc hB

/-- The cost of `fBlock` and `lBlock`, small without tuples. -/
def Kfl' (c r : ℕ) : ℕ := (64 * r + 60 + 4) * c + (24 * r + 20) * c + 40

theorem Kfl_le {c r : ℕ} (hc : c ≠ 0) : Kfl c r ≤ Kfl' c r := by
  unfold Kfl Kfl'
  have : 24 * r + 20 ≤ (24 * r + 20) * c := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hc)
  omega

theorem fBlock_spec' {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (SC w o c r) fBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: minL (LR w o c r)) ∧
        Keep blkVars σ σ') (Kfl' c r) := by
  by_cases hc : c = 0
  · exact (fBlock_spec0 hc (by have := hs.big; omega)).mono (by unfold Kfl'; omega)
  · exact (fBlock_spec hs).mono (Kfl_le hc)

theorem lBlock_spec' {w : List ℕ} {o c r : ℕ} (hs : SymOK B w o c r) :
    Spec B (SC w o c r) lBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: maxL (LR w o c r)) ∧
        Keep blkVars σ σ') (Kfl' c r) := by
  by_cases hc : c = 0
  · exact (lBlock_spec0 hc (by have := hs.big; omega)).mono (by unfold Kfl'; omega)
  · exact (lBlock_spec hs).mono (Kfl_le hc)

/-! ### All five blocks -/

/-- The context of `symW`. -/
def SCM (w : List ℕ) (o c r M : ℕ) (σ : Env) : Prop := SC w o c r σ ∧ σ.vars "M" = M

theorem SCM.keep {w : List ℕ} {o c r M : ℕ} {σ σ' : Env} (h : SCM w o c r M σ)
    (hk : Keep blkVars σ σ') : SCM w o c r M σ' :=
  ⟨SC.of_keep h.1 hk (by decide), by rw [hk.1 "M" (by decide)]; exact h.2⟩

/-- The cost of `symW`. -/
def Ksym (c r M : ℕ) : ℕ := (24 * (c * r) + 30) + (Kfl' c r + (Kfl' c r + (KsB c r + (14 * M + 20))))

theorem symW_spec {w : List ℕ} {o c r M : ℕ} (hs : SymOK B w o c r) (hM : M + c + 1 < B) :
    Spec B (SCM w o c r M) symW
      (fun σ σ' => σ'.out = σ.out ++ symOut w o c r M ∧ Keep blkVars σ σ') (Ksym c r M) := by
  have h1 : Spec B (SCM w o c r M) copyBlock
      (fun σ σ' => σ'.out = σ.out ++ (c :: tupR w o (c * r)) ∧ Keep blkVars σ σ')
      (24 * (c * r) + 30) := fun σ hσ => by
    obtain ⟨σ', hr, ho, hk⟩ := copyBlock_spec hs σ hσ.1
    exact ⟨σ', hr, ho, hk.mono (by decide)⟩
  have h2 : Spec B (SCM w o c r M) fBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: minL (LR w o c r)) ∧
        Keep blkVars σ σ') (Kfl' c r) := fun σ hσ => fBlock_spec' hs σ hσ.1
  have h3 : Spec B (SCM w o c r M) lBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then [0] else 1 :: maxL (LR w o c r)) ∧
        Keep blkVars σ σ') (Kfl' c r) := fun σ hσ => lBlock_spec' hs σ hσ.1
  have h4 : Spec B (SCM w o c r M) sBlock
      (fun σ σ' => σ'.out = σ.out ++ ((c - 1) :: (sList (LR w o c r)).flatten) ∧ Keep blkVars σ σ')
      (KsB c r) := fun σ hσ => sBlock_spec hs σ hσ.1
  have h5 : Spec B (SCM w o c r M) zBlock
      (fun σ σ' => σ'.out = σ.out ++ (if c = 0 then M :: List.range M else [0]) ∧ Keep blkVars σ σ')
      (14 * M + 20) := fun σ hσ => zBlock_spec hM σ ⟨hσ.2, hσ.1.2.2.1⟩
  have hP : ∀ σ σ', SCM w o c r M σ → Keep blkVars σ σ' → SCM w o c r M σ' :=
    fun _ _ h hk => h.keep hk
  refine (Spec.seq_out h1 (Spec.seq_out h2 (Spec.seq_out h3 (Spec.seq_out h4 h5 hP) hP) hP)
    hP).post ?_
  rintro σ σ' - ⟨ho, hk⟩
  refine ⟨?_, hk⟩
  rw [ho, symOut]
  simp only [List.append_assoc, List.cons_append]

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PSym
