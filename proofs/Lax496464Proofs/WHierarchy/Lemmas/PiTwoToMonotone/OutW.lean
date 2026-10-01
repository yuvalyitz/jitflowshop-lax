import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out

/-! # The output of the program, word by word

`R_eq`: on a word that fits, the reduction is the word the program writes: the number of clauses,
the block clauses (`bWords`), the clauses of the pairs of blocks with values (`xWords`), the clauses
of the universal assignments (`mWords`), and `W`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.OutW

open Lax429075.CNF Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out

variable (Dt : Data) (x : List ℕ)

/-- The words of block clause `b`. -/
def bWords (b : ℕ) : List ℕ :=
  (par Dt x).C :: (List.range (par Dt x).C).map fun e => 2 * (par Dt x).zv b e

/-- The words of the clause of a pair of blocks with values. -/
def xWords (b1 v1 b2 v2 : ℕ) : List ℕ :=
  2 * (par Dt x).C :: ((List.range (par Dt x).C).map (fun e =>
      if (par Dt x).cf b1 v1 b2 v2 = false ∨ e ≠ v1 then 2 * (par Dt x).zv b1 e else 0) ++
    (List.range (par Dt x).C).map (fun e =>
      if (par Dt x).cf b1 v1 b2 v2 = true ∧ e ≠ v2 then 2 * (par Dt x).zv b2 e else 0))

/-- The words of the clause of the universal assignment `za`. -/
def mWords (za : ℕ) : List ℕ :=
  (par Dt x).W * (par Dt x).C * (par Dt x).Q ::
    (List.range (par Dt x).W).flatMap fun b => (List.range (par Dt x).C).flatMap fun v =>
      (List.range (par Dt x).Q).map fun zb =>
        if good Dt x za b v zb = true then 2 * (par Dt x).zv b v else 0

/-- The words of the pair clauses. -/
def xAll : List ℕ :=
  (List.range (par Dt x).W).flatMap fun b1 => (List.range (par Dt x).C).flatMap fun v1 =>
    (List.range (par Dt x).W).flatMap fun b2 => (List.range (par Dt x).C).flatMap fun v2 =>
      xWords Dt x b1 v1 b2 v2

/-- **What the program writes** on a word that fits. -/
def outWords : List ℕ :=
  ((par Dt x).W + (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C + (par Dt x).P) ::
    ((List.range (par Dt x).W).flatMap (bWords Dt x) ++ xAll Dt x ++
      (List.range (par Dt x).P).flatMap (mWords Dt x) ++ [(par Dt x).W])

theorem length_flatMap_range {α : Type} (a m : ℕ) (f : ℕ → List α)
    (h : ∀ i, (f i).length = m) : ((List.range a).flatMap f).length = a * m := by
  induction a with
  | zero => simp
  | succ a ih => rw [List.range_succ, List.flatMap_append]; simp [ih, h]; ring

/-- The word of one clause. -/
def encC (C : Clause) : List ℕ := C.length :: C.map litCode

theorem R_eq (h : fitW Dt x) : R Dt x = outWords Dt x := by
  unfold R outWords
  rw [if_pos h]
  have hlen : (alphaW Dt x).length = (par Dt x).W +
      (par Dt x).W * (par Dt x).C * (par Dt x).W * (par Dt x).C + (par Dt x).P := by
    simp only [alphaW, Par.alpha, Par.xClauses, List.length_append, List.length_map,
      List.length_range]
    rw [length_flatMap_range (par Dt x).W ((par Dt x).C * ((par Dt x).W * (par Dt x).C)) _
      fun b1 => by
        rw [length_flatMap_range (par Dt x).C ((par Dt x).W * (par Dt x).C) _ fun v1 => by
          rw [length_flatMap_range (par Dt x).W (par Dt x).C _ fun b2 => by simp]]]
    ring
  simp only [encode, List.cons_append, hlen, List.cons.injEq, true_and]
  have hb : ∀ b, encC ((par Dt x).blockClause b) = bWords Dt x b := by
    intro b
    simp [Par.blockClause, encC, bWords, Function.comp_def, lp, litCode]
  have hx : ∀ b1 v1 b2 v2, encC ((par Dt x).xClause b1 v1 b2 v2) = xWords Dt x b1 v1 b2 v2 := by
    intro b1 v1 b2 v2
    simp only [Par.xClause, encC, xWords, List.length_append, List.length_map, List.length_range,
      List.map_append, List.map_map, Function.comp_def, lp, litCode]
    refine congrArg₂ _ (by ring) (congrArg₂ _ ?_ ?_)
    · refine List.map_congr_left fun e _ => ?_
      by_cases h1 : (par Dt x).cf b1 v1 b2 v2 = false <;> by_cases h2 : e = v1 <;> simp [h1, h2]
    · refine List.map_congr_left fun e _ => ?_
      by_cases h1 : (par Dt x).cf b1 v1 b2 v2 = true <;> by_cases h2 : e = v2 <;> simp [h1, h2]
  have hm : ∀ za, encC ((par Dt x).mClause (good Dt x) za) = mWords Dt x za := by
    intro za
    simp only [Par.mClause, encC, mWords]
    congr 1
    · rw [length_flatMap_range (par Dt x).W ((par Dt x).C * (par Dt x).Q) _ fun b => by
        rw [length_flatMap_range (par Dt x).C (par Dt x).Q _ fun v => by simp]]
      ring
    · simp only [List.map_flatMap, List.map_map, Function.comp_def, lp, litCode]
      refine List.flatMap_congr fun b _ => List.flatMap_congr fun v _ =>
        List.map_congr_left fun zb _ => ?_
      split_ifs <;> simp
  show (alphaW Dt x).flatMap encC ++ [(par Dt x).W] = _
  simp only [alphaW, Par.alpha, List.flatMap_append, List.flatMap_map, List.append_assoc]
  congr 1
  · exact List.flatMap_congr fun b _ => hb b
  · congr 1
    · simp only [Par.xClauses, xAll, List.flatMap_assoc, List.flatMap_map]
      exact List.flatMap_congr fun b1 _ => List.flatMap_congr fun v1 _ =>
        List.flatMap_congr fun b2 _ => List.flatMap_congr fun v2 _ => hx b1 v1 b2 v2
    · congr 1
      exact List.flatMap_congr fun za _ => hm za

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.OutW
