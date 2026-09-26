import Lax496464.HittingSetHardness
import Lax496464Proofs.HittingSet.Final
import Lax496464Proofs.HittingSet.Injective
import Lax429075.SATHard
import Lax434930Proofs.PolynomialComposition
import Lax434930Proofs.TM2Bounds

/-!
# Hitting Set is NP-hard

Cook's theorem in the archive's form, followed by the reduction from satisfiability.
-/

namespace Lax496464Proofs.HittingSet.Hardness

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime Lax429075.Reductions
open Lax496464.HittingSet Lax496464.HittingSetFromSat

/-- A polynomial is bounded by a power of `n + 2`. -/
theorem eval_le_pow (p : Polynomial ℕ) : ∃ c, ∀ n, p.eval n ≤ (n + 2) ^ c := by
  refine ⟨p.natDegree + ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i, fun n => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  have h1 : ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * n ^ i ≤
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (n + 2) ^ p.natDegree :=
    Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _
      (le_trans (Nat.pow_le_pow_left (by omega) i)
        (Nat.pow_le_pow_right (by omega) (by simpa [Nat.lt_succ_iff] using hi)))
  rw [← Finset.sum_mul] at h1
  refine le_trans h1 ?_
  rw [pow_add, Nat.mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  exact le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_left (by omega) _)

/-- The output of a polynomial-time machine is polynomially long. -/
theorem length_le_pow {g : Word → Word} (t : Turing.TM2ComputableInPolyTime id id g) :
    ∃ c, ∀ x, (g x).length ≤ (x.length + 2) ^ c := by
  obtain ⟨c, hc⟩ := eval_le_pow t.time
  obtain ⟨f, hf⟩ : ∃ f, Lax434930Proofs.TM2Bounds.factor t.tm = f := ⟨_, rfl⟩
  refine ⟨c + f + 2, fun x => ?_⟩
  have h := Lax434930Proofs.TM2Bounds.output_length t.tm (t.outputsFun x)
  simp only [List.length_map, id] at h
  rw [hf] at h
  have h2 := hc x.length
  obtain ⟨L, hL⟩ : ∃ L, x.length = L := ⟨_, rfl⟩
  rw [hL] at h h2 ⊢
  obtain ⟨a, ha⟩ : ∃ a, (L + 2) ^ c = a := ⟨_, rfl⟩
  rw [ha] at h2
  have ha1 : L + 2 ≤ (L + 2) * a := by
    rw [← ha]; exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
  have hb : f + 1 ≤ (L + 2) ^ (f + 1) :=
    le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_left (by omega) _)
  have hfa : f * t.time.eval L ≤ f * a := Nat.mul_le_mul_left _ h2
  calc (g x).length ≤ L + f * t.time.eval L := h
    _ ≤ (L + 2) * a + f * ((L + 2) * a) := by
        have : f * a ≤ f * ((L + 2) * a) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
        omega
    _ = (f + 1) * ((L + 2) * a) := by ring
    _ ≤ (L + 2) ^ (f + 1) * ((L + 2) * a) := Nat.mul_le_mul_right _ hb
    _ = (L + 2) ^ (c + f + 2) := by rw [← ha]; ring

/--
---
conclusion: Lax496464.HittingSetHardness.npHard
---
Satisfiability is NP-hard by the Cook–Levin theorem; the reduction is correct and runs in
polynomial time, and polynomial-time reductions compose.
-/
theorem npHard : ∀ A : Language, A ∈ NP → ManyOne A HittingSetLanguage := fun A hA => by
  obtain ⟨g, ⟨tg⟩, hg⟩ := Lax429075.SATHard.hardness A hA
  obtain ⟨tw⟩ := Lax496464Proofs.HittingSet.Final.reduceWord_polyTime
  exact ⟨reduceWord ∘ g, Lax434930Proofs.PolynomialComposition.comp tg tw,
    fun x => (hg x).trans (Lax496464Proofs.HittingSet.Injective.reduceWord_correct (g x))⟩

theorem cube_le {L c : ℕ} {a : ℕ} (ha : (L + 2) ^ c = a) {x : ℕ} (hx : x ≤ a) :
    (x + 2) ^ 3 ≤ (L + 2) ^ (3 * c + 5) := by
  have ha1 : 1 ≤ a := by rw [← ha]; exact Nat.one_le_pow _ _ (by omega)
  have h1 : x + 2 ≤ 3 * a := by omega
  have h2 : (x + 2) ^ 3 ≤ (3 * a) ^ 3 := Nat.pow_le_pow_left h1 3
  have h3 : (3 * a) ^ 3 ≤ 2 ^ 5 * a ^ 3 := by
    rw [mul_pow]; exact Nat.mul_le_mul_right _ (by norm_num)
  have h4 : 2 ^ 5 * a ^ 3 ≤ (L + 2) ^ 5 * a ^ 3 :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 5)
  have h5 : (L + 2) ^ 5 * a ^ 3 = (L + 2) ^ (3 * c + 5) := by
    rw [← ha, ← pow_mul, ← pow_add]; ring_nf
  omega

/--
---
conclusion: Lax496464.HittingSetHardness.hittingSet_npHard
---
The same reduction, writing the instance: the size clauses are those of the construction,
composed with the polynomial length of the output of Cook's reduction.
-/
theorem hittingSet_npHard :
    ∀ A : Language, A ∈ NP →
      ∃ (f : Word → Instance × ℕ) (c : ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime id
          (fun z : Instance × ℕ => encodeInstance z.1 z.2) f) ∧
        (∀ x, 2 ≤ (f x).2 ∧ (f x).2 ≤ (f x).1.n) ∧
        (∀ x, (f x).1.n + (f x).1.m ≤ (x.length + 2) ^ c) ∧
        (∀ x, (f x).1.n ≤ 4 + (f x).1.m + ∑ j : Fin (f x).1.m, ((f x).1.F j).card) ∧
        (∀ x, x ∈ A ↔ Instance.HasHittingSet (f x).1 (f x).2) := fun A hA => by
  obtain ⟨g, ⟨tg⟩, hg⟩ := Lax429075.SATHard.hardness A hA
  obtain ⟨tr⟩ := Lax496464Proofs.HittingSet.Final.fromSat_polyTime
  obtain ⟨c, hc⟩ := length_le_pow tg
  refine ⟨reduce ∘ g, 3 * c + 5, Lax434930Proofs.PolynomialComposition.comp tg tr,
    fun x => Lax496464Proofs.HittingSet.Words.reduce_bounds (g x), fun x => ?_,
    fun x => Lax496464Proofs.HittingSet.Words.reduce_covered (g x),
    fun x => (hg x).trans (Lax496464Proofs.HittingSet.Words.reduce_correct (g x))⟩
  exact le_trans (Lax496464Proofs.HittingSet.Words.reduce_size (g x)) (cube_le rfl (hc x))

end Lax496464Proofs.HittingSet.Hardness
