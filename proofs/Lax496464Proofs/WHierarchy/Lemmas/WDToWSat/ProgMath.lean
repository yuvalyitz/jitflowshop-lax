import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs
import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Reduction

/-!
# The output of the program, word by word

`R_eq`: on a word that fits, the reduction is the word the program writes: the number of clauses,
the clauses of every assignment `z < n^r` (`zWords`), the clauses `Y_c ∨ ¬Y_c` (`tautWords`), and `k`.
Also the facts about the word the program relies on (`Good`): the header is in range, and the blocks
lie within the word.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath

open Lax496464.WH_B1_Structures Lax496464.WH_B3_LogicProblems Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs
open Lax496464Proofs.WHierarchy.Logic.StructureCode

/-! ### The words -/

/-- The words of the clause of `C` under the digits `ds`. -/
def clauseWords (D : Data) (x : List ℕ) (ds : List ℕ) (C : List Lit) : List ℕ :=
  if satNonX D x ds C then [2, 0, 1]
  else (C.filter isXLit).length :: (C.filter isXLit).map fun l => 2 * codeW D x ds l + (1 - bv l.pos)

/-- The words of the clauses of the assignment `z`. -/
def zWords (D : Data) (x : List ℕ) (z : ℕ) : List ℕ :=
  D.cnf.flatMap (clauseWords D x (digits (nW D x) D.r z))

/-- The words of `Y_c ∨ ¬Y_c`. -/
def tautWords (c : ℕ) : List ℕ := [2, 2 * c, 2 * c + 1]

/-- **What the program writes** on a word that fits. -/
def outWords (D : Data) (x : List ℕ) : List ℕ :=
  (nW D x ^ D.r * D.cnf.length + nW D x ^ D.s) ::
    ((List.range (nW D x ^ D.r)).flatMap (zWords D x) ++
      ((List.range (nW D x ^ D.s)).flatMap tautWords ++ [kW x]))

theorem clause_words (D : Data) (x ds : List ℕ) (C : List Lit) :
    (clauseOut D x ds C).length :: (clauseOut D x ds C).map litCode = clauseWords D x ds C := by
  unfold clauseOut clauseWords
  split_ifs
  · simp [litCode]
  · simp only [List.length_map, List.map_map, List.cons.injEq, true_and]
    refine List.map_congr_left fun l _ => ?_
    cases h : l.pos <;> simp [litCode, bv, h]

theorem R_eq {D : Data} {x : List ℕ} (h : fitW D x) : R D x = outWords D x := by
  unfold R outWords
  rw [if_pos h]
  simp only [encode, alphaW, zClauses, List.length_append, List.length_flatMap, List.length_map,
    List.length_range, List.flatMap_append, List.cons_append, List.append_assoc]
  refine congrArg₂ _ ?_ ?_
  · simp [Nat.mul_comm]
  · rw [List.flatMap_assoc]
    congr 1
    · refine List.flatMap_congr fun z _ => ?_
      rw [zWords, zClauses, List.flatMap_map]
      exact List.flatMap_congr fun C _ => clause_words D x _ C
    · rw [List.flatMap_map]
      congr 1

/-! ### The facts about the word -/

/-- The header is in range and the blocks lie within the word. -/
structure Good (x : List ℕ) : Prop where
  head : 1 + spW x < x.length
  blocks : boW x (spW x) < x.length
  cnt : ∀ i < spW x, x.getD (boW x i) 0 < x.length

theorem boW_le_succ (x : List ℕ) (i : ℕ) : boW x i ≤ boW x (i + 1) := by
  simp only [boW]; omega

theorem boW_mono (x : List ℕ) {i j : ℕ} (h : i ≤ j) : boW x i ≤ boW x j := by
  induction j with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · exact (ih (by omega)).trans (boW_le_succ x j)
    · rw [Nat.le_antisymm h h']

theorem good_of_enc {x : List ℕ} {A : Structure} {k : ℕ} {bl : List (List ℕ)} (he : Enc x A k bl) :
    Good x := by
  have hsp := he.spW_eq
  have hb := he.boW_eq (A.arities.length) le_rfl
  have hlen : x.length = 2 + A.arities.length + bl.flatten.length + 1 := by
    rw [he.eq]; simp; omega
  rw [List.take_of_length_le (by rw [he.len])] at hb
  refine ⟨by rw [hsp]; omega, by rw [hsp, hb]; omega, fun i hi => ?_⟩
  rw [hsp] at hi
  obtain ⟨ts, -, -, hbk, htl⟩ := he.block i hi
  have hq := he.getD_boW hi (q := 0) (by rw [hbk]; simp)
  rw [Nat.add_zero, hbk] at hq
  rw [hq]
  have hpos : 1 ≤ A.arities.getD i 0 := A.arity_pos _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi)
  have h1 : ts.length ≤ ts.flatten.length := by
    rw [length_flatten_of_forall htl]; exact Nat.le_mul_of_pos_right _ hpos
  have h2 : (ts.length :: ts.flatten).length ≤ bl.flatten.length := by
    rw [← hbk]
    have hbl : i < bl.length := by rw [he.len]; exact hi
    have := len_flatten_take_succ hbl
    have := len_flatten_take_le bl (i + 1)
    omega
  simp only [List.getD_cons_zero, List.length_cons] at h2 ⊢
  omega

/-- A position of block `i`. -/
theorem pos_lt {x : List ℕ} (hg : Good x) {i t q : ℕ} (hi : i < spW x)
    (ht : t < x.getD (boW x i) 0) (hq : q < x.getD (1 + i) 0) :
    boW x i + 1 + t * x.getD (1 + i) 0 + q < x.length := by
  have h1 := boW_mono x (show i + 1 ≤ spW x by omega)
  have h2 := hg.blocks
  have h3 : t * x.getD (1 + i) 0 + q < x.getD (boW x i) 0 * x.getD (1 + i) 0 := by
    have := Nat.mul_le_mul_right (x.getD (1 + i) 0) (show t + 1 ≤ x.getD (boW x i) 0 by omega)
    rw [Nat.succ_mul] at this; omega
  simp only [boW] at h1
  omega

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath
