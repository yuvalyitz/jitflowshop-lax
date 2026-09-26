import Lax496464Proofs.HittingSet.Correct
import Lax429075.EncodingCorrect
import Lax429075Proofs.DecoderSoundness

/-!
# The reduction on words

Correctness on words, and the three size facts: the required size lies between two and the
size of the universe, the pairs alone cover the universe, and the instance is polynomial in
the length of the word.
-/

namespace Lax496464Proofs.HittingSet.Words

open Lax429075.CNF Lax429075.Encoding Lax429075.Satisfiability Lax434930.PolynomialTime
open Lax496464.HittingSet Lax496464.HittingSetFromSat Lax496464Proofs.HittingSet.Correct

theorem parseF_encodeCNF (F : Formula) : parseF (encodeCNF F) = F := by
  rw [parseF, Lax429075.EncodingCorrect.roundtrip]; rfl

theorem not_sat_empty_clause : ¬ Satisfiable [[]] := by
  rintro ⟨ρ, h⟩; simp [eval] at h

theorem reduce_fst (w : Word) : (reduce w).1 = inst (parseF w) := rfl

theorem reduce_snd (w : Word) : (reduce w).2 = vars (parseF w) := rfl

/-- Correctness on words. A word in SAT is the encoding of a satisfiable formula, which the
reduction decodes back; a word encoding nothing is sent to the instance of the formula with
one empty clause, which has no hitting set. -/
theorem reduce_correct (w : Word) :
    w ∈ SAT ↔ (reduce w).1.HasHittingSet (reduce w).2 := by
  rw [reduce_fst, reduce_snd]
  constructor
  · rintro ⟨F, rfl, hsat⟩
    rw [parseF_encodeCNF]
    exact (Lax496464Proofs.HittingSet.Correct.fromSat_correct F).mp hsat
  · intro h
    rw [← Lax496464Proofs.HittingSet.Correct.fromSat_correct] at h
    cases hd : decodeCNF w with
    | none => rw [parseF, hd] at h; exact absurd h not_sat_empty_clause
    | some F =>
        rw [parseF, hd] at h
        exact ⟨F, Lax429075Proofs.decode_cnf_sound w F hd, h⟩

/-- The required size lies between two and the size of the universe: it is the number of
variables, at least two by construction and half the size of the universe. -/
theorem reduce_bounds (w : Word) : 2 ≤ (reduce w).2 ∧ (reduce w).2 ≤ (reduce w).1.n := by
  rw [reduce_fst, reduce_snd, inst_n]
  exact ⟨two_le_vars _, by omega⟩

/-! ### The pairs cover the universe -/

theorem two_le_card_pair (F : Formula) {j : ℕ} (hj : j < vars F) :
    2 ≤ ((inst F).F ⟨j, by rw [inst_m]; omega⟩).card := by
  have h1 : 2 * j < (inst F).n := by rw [inst_n]; omega
  have h2 : 2 * j + 1 < (inst F).n := by rw [inst_n]; omega
  have hsub : ({⟨2 * j, h1⟩, ⟨2 * j + 1, h2⟩} : Finset (Fin (inst F).n)) ⊆
      (inst F).F ⟨j, by rw [inst_m]; omega⟩ := by
    intro x hx
    rw [mem_F_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [sets_getD_pair F hj]
    rcases hx with rfl | rfl <;> simp
  have hne : (⟨2 * j, h1⟩ : Fin (inst F).n) ≠ ⟨2 * j + 1, h2⟩ := by
    intro h; have := Fin.mk.inj_iff.mp h; omega
  have := Finset.card_le_card hsub
  rwa [Finset.card_pair hne] at this

theorem sum_card_ge (F : Formula) : 2 * vars F ≤ ∑ j : Fin (inst F).m, ((inst F).F j).card := by
  change 2 * vars F ≤ ∑ j : Fin (vars F + F.length), ((inst F).F j).card
  rw [Fin.sum_univ_add]
  have : ∑ i : Fin (vars F), 2 ≤ ∑ i : Fin (vars F), ((inst F).F (Fin.castAdd F.length i)).card :=
    Finset.sum_le_sum fun i _ => two_le_card_pair F i.isLt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- No element lies outside every set: the pair of each variable has two elements, and there
are as many pairs as half the universe. -/
theorem reduce_covered (w : Word) :
    (reduce w).1.n ≤ 4 + (reduce w).1.m + ∑ j : Fin (reduce w).1.m, ((reduce w).1.F j).card := by
  have := sum_card_ge (parseF w)
  show 2 * vars (parseF w) ≤ 4 + (vars (parseF w) + (parseF w).length) +
    ∑ j : Fin (inst (parseF w)).m, ((inst (parseF w)).F j).card
  omega

/-! ### The instance is polynomial in the word -/

theorem length_encodeList_ge {α : Type} (e : α → Word) (l : List α) :
    l.length + 1 ≤ (encodeList e l).length := by
  induction l with
  | nil => simp [encodeList]
  | cons a t ih => simp [encodeList] at ih ⊢; omega

theorem length_mem_encodeList {α : Type} (e : α → Word) {l : List α} {a : α} (ha : a ∈ l) :
    (e a).length + 1 ≤ (encodeList e l).length := by
  induction l with
  | nil => simp at ha
  | cons b t ih =>
      rcases List.mem_cons.mp ha with rfl | ha'
      · simp [encodeList]
      · have := ih ha'; simp [encodeList] at this ⊢; omega

theorem length_encodeLiteral (l : Literal) : (encodeLiteral l).length = l.index + 2 := by
  simp [encodeLiteral, Lax429075.Encoding.encodeNat]

theorem clauses_le_length (F : Formula) : F.length ≤ (encodeCNF F).length := by
  have := length_encodeList_ge encodeClause F; unfold encodeCNF; omega

theorem index_lt_length {F : Formula} {C : Clause} {l : Literal} (hC : C ∈ F) (hl : l ∈ C) :
    l.index + 4 ≤ (encodeCNF F).length := by
  have h1 := length_mem_encodeList encodeLiteral hl
  have h2 := length_mem_encodeList encodeClause hC
  rw [length_encodeLiteral] at h1
  unfold encodeClause at h2; unfold encodeCNF encodeClause
  omega

theorem vars_le (F : Formula) : vars F ≤ (encodeCNF F).length + 2 := by
  have : bound F ≤ (encodeCNF F).length + 1 :=
    bound_le (by omega) fun C hC l hl => by have := index_lt_length hC hl; omega
  unfold vars; omega

theorem four_le_cube (L : ℕ) : 4 * (L + 2) ≤ (L + 2) ^ 3 := by
  have h : 2 ^ 2 ≤ (L + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  norm_num at h
  calc 4 * (L + 2) ≤ (L + 2) ^ 2 * (L + 2) := Nat.mul_le_mul_right _ h
    _ = (L + 2) ^ 3 := by ring

/-- The instance is polynomial in the word: the universe has twice the variables and the
family has one set per variable and per clause; every variable index and every clause costs
at least one bit of the word. -/
theorem reduce_size (w : Word) : (reduce w).1.n + (reduce w).1.m ≤ (w.length + 2) ^ 3 := by
  rw [reduce_fst, inst_n, inst_m]
  have hc := four_le_cube w.length
  cases hd : decodeCNF w with
  | none =>
      rw [parseF, hd]
      have h2 : 2 ^ 3 ≤ (w.length + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      simp only [Option.getD_none, List.length_singleton]
      have : vars [[]] = 2 := by decide
      omega
  | some F =>
      rw [parseF, hd, Option.getD_some]
      have hw := Lax429075Proofs.decode_cnf_sound w F hd
      have h1 := vars_le F
      have h2 := clauses_le_length F
      rw [hw] at h1 h2
      omega

end Lax496464Proofs.HittingSet.Words
