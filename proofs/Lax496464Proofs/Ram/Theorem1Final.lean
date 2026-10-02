import Lax496464Proofs.Ram.TotalFinal
import Lax496464Proofs.Ram.Reduction
import Lax496464.NPHardness
import Lax496464.Theorem1
import Lax496464.HittingSetHardness
import Lax391470Proofs.RamToTuring
import Lax391470Proofs.TMCompose

/-!
# Theorem 1's Hardness Claim, from the Running-Time and Correctness Results

The word-RAM reduction `TotalReduction.f` is polynomial-time (`TotalFinal.ramPolytime_f`) and
computes, on the bits of a canonical encoding, the bits of the constructed shop. This file
carries that to the Turing-machine statement `StronglyNPHardOn`, composing with the
NP-hardness of Hitting Set.
-/

namespace Lax496464Proofs.Ram.Theorem1Final

open Lax434930.PolynomialTime
open Lax496464Proofs.Ram.BitsNat (natBits bitsNat natBits_encodeNat)
open Lax496464Proofs.Ram.TotalReduction (f)
open Lax496464Proofs.Ram.TotalFinal (f_le_one ramPolytime_f)
open Lax496464Proofs.Ram.InstanceWord (decisionWord blk instanceWord)
open Lax496464Proofs.Ram.TotalReduction (Admissible f_eq)
open Lax496464Proofs.Ram.CsrWord (csrWord membersOf sizes length_membersOf length_csrWord)
open Lax496464.HittingSet Lax496464.Construction
open Lax496464Proofs.Ram.TotalBnd (ExpBd numJobs_lt_two_pow target_lt_two_pow jp_jq_jd_lt_two_pow
  two_le_e)

/-! ## The word-level map -/

/-- A list of zeros and ones, as a binary word. -/
def bitsToWord (l : List ℕ) : Word := l.map fun v => decide (v ≠ 0)

theorem natBits_bitsToWord {l : List ℕ} (h : ∀ v ∈ l, v ≤ 1) : natBits (bitsToWord l) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have ha := h a List.mem_cons_self
    have ht : ∀ v ∈ t, v ≤ 1 := fun v hv => h v (List.mem_cons_of_mem _ hv)
    simp only [bitsToWord, natBits, List.map_cons] at ih ⊢
    rw [ih ht]
    congr 1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;> simp

/-- The reduction on binary words: read the word's bits, apply `f`, read the result back. -/
noncomputable def F (w : Word) : Word := bitsToWord (f (natBits w))

theorem natBits_F (w : Word) : natBits (F w) = f (natBits w) :=
  natBits_bitsToWord fun _ hv => f_le_one hv

theorem natBits_injective : Function.Injective natBits := by
  intro a b h
  induction a generalizing b with
  | nil => cases b <;> simp_all [natBits]
  | cons x t ih =>
    cases b with
    | nil => simp [natBits] at h
    | cons y u =>
      simp only [natBits, List.map_cons, List.cons.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have := ih (b := u) (by simpa [natBits] using h2)
      subst this
      congr 1
      cases x <;> cases y <;> simp_all

/-! ## The bits of a decision instance -/

theorem natBits_encodeDecisionInstance (I : Lax496464.FlowShop.Instance) (W : ℕ) :
    natBits (Lax496464.BinaryEncoding.encodeDecisionInstance I W) =
      (decisionWord I W).flatMap bitsNat := by
  have hn : ∀ n, natBits (Lax496464.BinaryEncoding.encodeNat n) = bitsNat n := fun n =>
    natBits_encodeNat n
  unfold Lax496464.BinaryEncoding.encodeDecisionInstance
    Lax496464.BinaryEncoding.encodeInstance decisionWord instanceWord blk
  simp only [Lax496464Proofs.Ram.ScanModel.natBits_append,
    Lax496464Proofs.Ram.ScanModel.natBits_flatMap, hn, List.flatMap_append, List.flatMap_map,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-! ## Admissibility, and `F` on a canonical encoding -/

/-- The size clause in the form the cited statement carries it: the universe is no larger than
`4 + m` plus the total size of the sets. -/
theorem admissible_of_sum {P : Instance} {k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ P.n)
    (h : P.n ≤ 4 + P.m + ∑ j : Fin P.m, (P.F j).card) : Admissible P k := by
  refine ⟨hk2, hkn, ?_⟩
  rw [length_csrWord, length_membersOf, sizes]
  have hsum : ((List.finRange P.m).map fun j => (P.F j).card).sum =
      ∑ j : Fin P.m, (P.F j).card := (Fin.sum_univ_def _).symm
  rw [hsum]; exact h

/-- **On a canonical, admissible encoding, `F` is the word of the constructed shop.** -/
theorem F_encodeInstance {P : Instance} {k : ℕ} (hAdm : Admissible P k) :
    F (Lax496464.HittingSet.encodeInstance P k) =
      Lax496464.BinaryEncoding.encodeDecisionInstance (construct P k) (target P k) := by
  apply natBits_injective
  rw [natBits_F, f_eq hAdm, natBits_encodeDecisionInstance]

/-! ## The numbers of the constructed shop are polynomially bounded -/

theorem foldr_max_le {α : Type} (l : List α) (g : α → ℕ) (init B : ℕ) (hi : init ≤ B)
    (h : ∀ a ∈ l, g a ≤ B) : (l.map g).foldr max init ≤ B := by
  induction l with
  | nil => simpa using hi
  | cons a t ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h a List.mem_cons_self) (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem numJobs_eq_zero_of_m_zero {P : Instance} {k : ℕ} (hm : P.m = 0) : numJobs P k = 0 := by
  have hdc0 : dumCount P k = 0 := by simp [dumCount, hm]
  have hsc0 : selCount P k = 0 := by
    have hfr : List.finRange P.m = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [List.length_finRange, hm]
    have hml0 : (memberList P).length = 0 := by
      unfold memberList; rw [hfr]; rfl
    simp only [selCount, hml0]; ring
  simp only [numJobs, hsc0, hdc0]

/-- **Every number of the constructed shop is at most `2 ^ (64 e)`.** -/
theorem maxNumber_construct_le {P : Instance} {k e : ℕ} (hAdm : Admissible P k)
    (hb : ExpBd P k e) :
    max (Lax496464.BinaryEncoding.maxNumber (construct P k)) (target P k) ≤ 2 ^ (64 * e) := by
  have hexp2 := two_le_e hAdm hb
  have hnj := numJobs_lt_two_pow hAdm hb
  have htg := target_lt_two_pow hAdm hb
  have hk := hb.k
  have hpad : ∀ c, c ≤ 64 → (2 : ℕ) ^ (c * e) ≤ 2 ^ (64 * e) := fun c hc =>
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right e hc)
  have h1 : (1 : ℕ) < 2 ^ (64 * e) :=
    Nat.one_lt_two_pow (by omega)
  have hkle : k ≤ 2 ^ (64 * e) := by
    have : (2 : ℕ) ^ e ≤ 2 ^ (64 * e) := by
      simpa using hpad 1 (by norm_num)
    omega
  have hnjle : numJobs P k ≤ 2 ^ (64 * e) := (hnj.le).trans (hpad 32 (by norm_num))
  have htgle : target P k < 2 ^ (64 * e) :=
    lt_of_lt_of_le htg (hpad 24 (by norm_num))
  refine max_le ?_ htgle.le
  unfold Lax496464.BinaryEncoding.maxNumber
  have hB : ∀ B, B = 2 ^ (64 * e) → (List.map (fun j => max (max ((construct P k).p j)
      ((construct P k).q j)) (max ((construct P k).d j) ((construct P k).w j)))
      (List.finRange (construct P k).jobs)).foldr max
        (max (construct P k).jobs (construct P k).machines) ≤ B := by
    intro B hB
    subst hB
    refine foldr_max_le _ _ _ _ (max_le hnjle hkle) ?_
    intro j _
    have hjm : 0 < P.m := by
      by_contra h0
      have hm0 : P.m = 0 := by omega
      have := numJobs_eq_zero_of_m_zero (k := k) hm0
      have hj := j.2
      have : (construct P k).jobs = 0 := this
      omega
    obtain ⟨hp, hq, hd⟩ := jp_jq_jd_lt_two_pow hAdm hb hjm (t := j.1) j.2
    exact max_le (max_le hp.le hq.le) (max_le hd.le h1.le)
  exact hB _ rfl

/-- The bit-length exponent: with `e := (n + m).size`, `2 ^ (64 e)` is a polynomial in `n + m`. -/
theorem pow_size_le {N c X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X) (hNX : N ≤ X ^ c) :
    2 ^ (64 * N.size) ≤ X ^ (64 * (c + 1)) := by
  have h1 : 2 ^ (N.size - 1) ≤ N := Nat.lt_size.mp (by have := Nat.size_pos.mpr hN; omega)
  have hsz : 1 ≤ N.size := Nat.size_pos.mpr hN
  have h2 : 2 ^ N.size ≤ 2 * N := by
    have : (2 : ℕ) ^ N.size = 2 * 2 ^ (N.size - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  have h3 : 2 * X ^ c ≤ X ^ (c + 1) := by
    rw [pow_succ]; nlinarith [Nat.zero_le (X ^ c)]
  have h4 : 2 ^ N.size ≤ X ^ (c + 1) := by omega
  calc 2 ^ (64 * N.size) = (2 ^ N.size) ^ 64 := by rw [← pow_mul]; ring_nf
    _ ≤ (X ^ (c + 1)) ^ 64 := Nat.pow_le_pow_left h4 64
    _ = X ^ (64 * (c + 1)) := by rw [← pow_mul]; ring_nf

/-- The shape of Hitting Set's NP-hardness that the composition needs: the cited statement
(`HittingSetHardness.hittingSet_npHard`) together with the size clause that the universe is no
larger than `4 + m` plus the total size of the sets, i.e. no larger than the word that presents
it, which is what a polynomial-time reduction *from that word* can afford. -/
def HSHardNoIsolated : Prop :=
  ∀ A : Language, A ∈ Lax434930.NondeterministicPolynomialTime.NP →
    ∃ (f₀ : Word → Instance × ℕ) (c : ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime id
        (fun z : Instance × ℕ => Lax496464.HittingSet.encodeInstance z.1 z.2) f₀) ∧
      (∀ x, 2 ≤ (f₀ x).2 ∧ (f₀ x).2 ≤ (f₀ x).1.n) ∧
      (∀ x, (f₀ x).1.n + (f₀ x).1.m ≤ (x.length + 2) ^ c) ∧
      (∀ x, (f₀ x).1.n ≤ 4 + (f₀ x).1.m + ∑ j : Fin (f₀ x).1.m, ((f₀ x).1.F j).card) ∧
      (∀ x, x ∈ A ↔ Instance.HasHittingSet (f₀ x).1 (f₀ x).2)

/-- The reduction on binary words is polynomial-time on a Turing machine. -/
theorem polyTime_F : Nonempty (Turing.TM2ComputableInPolyTime id id F) :=
  Lax391470Proofs.RamToTuring.polyTime_of_ram ramPolytime_f (fun w => (natBits_F w).symm)

/-- **Theorem 1's hardness claim**, from the NP-hardness of Hitting Set in the form
`HSHardNoIsolated`. -/
theorem stronglyNPHard_of_noIsolated (h : HSHardNoIsolated) :
    Lax496464.NPHardness.StronglyNPHardOn
      (fun I W => Lax496464.FlowShop.Instance.HasWeight I W)
      fun I => ∀ j : I.Job, I.w j = 1 := by
  intro A hA
  obtain ⟨f₀, c, ⟨t0⟩, hk, hpoly, hnoiso, hiff⟩ := h A hA
  have hAdm : ∀ x, Admissible (f₀ x).1 (f₀ x).2 := fun x =>
    admissible_of_sum (hk x).1 (hk x).2 (hnoiso x)
  refine ⟨fun x => (construct (f₀ x).1 (f₀ x).2, target (f₀ x).1 (f₀ x).2), 64 * (c + 1),
    ?_, ?_, ?_, ?_⟩
  · obtain ⟨tF⟩ := polyTime_F
    let tF' : Turing.TM2ComputableInPolyTime
        (fun z : Instance × ℕ => Lax496464.HittingSet.encodeInstance z.1 z.2) id
        (fun z => F (Lax496464.HittingSet.encodeInstance z.1 z.2)) :=
      { tF with outputsFun := fun z => tF.outputsFun (Lax496464.HittingSet.encodeInstance z.1 z.2) }
    obtain ⟨tc⟩ := Lax391470Proofs.TMCompose.comp t0 tF'
    refine ⟨{ tm := tc.tm, inputAlphabet := tc.inputAlphabet,
              outputAlphabet := tc.outputAlphabet, time := tc.time,
              outputsFun := fun x => ?_ }⟩
    have hc := tc.outputsFun x
    have e : Lax496464.BinaryEncoding.encodeDecisionInstance
        (construct (f₀ x).1 (f₀ x).2) (target (f₀ x).1 (f₀ x).2) =
        F (Lax496464.HittingSet.encodeInstance (f₀ x).1 (f₀ x).2) :=
      (F_encodeInstance (hAdm x)).symm
    simp only [Function.comp_apply, id] at hc ⊢
    rw [e]
    exact hc
  · intro x
    have hb : ExpBd (f₀ x).1 (f₀ x).2 ((f₀ x).1.n + (f₀ x).1.m).size := by
      have hlt := Nat.lt_size_self ((f₀ x).1.n + (f₀ x).1.m)
      have hkn := (hk x).2
      exact ⟨by omega, by omega, by omega⟩
    have h1 := maxNumber_construct_le (hAdm x) hb
    have h2 := pow_size_le (N := (f₀ x).1.n + (f₀ x).1.m) (c := c) (X := x.length + 2)
      (by have := (hk x).1; have := (hk x).2; omega) (by omega) (hpoly x)
    exact h1.trans h2
  · intro x j
    rfl
  · intro x
    exact (hiff x).trans
      (Lax496464Proofs.Section8.construct_correct _ _ (hk x).1 (hk x).2)

/--
---
conclusion: Lax496464.Theorem1.stronglyNPHard_hasWeight
---
Compose the NP-hardness of Hitting Set with the word RAM reduction of Section 8: the reduction
reads the bits of the emitted instance, writes the bits of the constructed shop
(`TotalReduction.f`, polynomial-time on the word RAM by `TotalFinal.ramPolytime_f`, hence on a
Turing machine), and the numbers of the shop are polynomial in the length of the original
input.
-/
theorem stronglyNPHard_hasWeight_proved :
    Lax496464.NPHardness.StronglyNPHardOn
      (fun I W => Lax496464.FlowShop.Instance.HasWeight I W)
      fun I => ∀ j : I.Job, I.w j = 1 :=
  stronglyNPHard_of_noIsolated fun A hA => by
    obtain ⟨f, c, h1, h2, h3, h4, h6⟩ := Lax496464.HittingSetHardness.hittingSet_npHard A hA
    exact ⟨f, c, h1, h2, h3, h4, h6⟩

end Lax496464Proofs.Ram.Theorem1Final
