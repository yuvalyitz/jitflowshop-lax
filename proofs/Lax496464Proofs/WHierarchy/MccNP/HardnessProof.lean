import Lax496464.WH_F4_IndependentSetToMcc
import Lax496464.WH_F5_MccNPHard
import Lax496464.WH_F3_NPHard
import Lax888481.PolynomialReduction
import Lax391470Proofs.TMToNats
import Lax391470Proofs.TMCompose
import Lax391470Proofs.Bits

/-!
# The reductions and NP-hardness from the properties of `reduce`

The strict fpt-reduction, the polynomial-time reduction and NP-hardness of Multicoloured Clique,
each proved from the properties of `reduce` taken as hypotheses. NP-hardness composes the Turing
machine of the archive's NP-hardness of Independent Set with the word RAM reduction.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.HardnessProof

open Lax496464 Lax496464.WH_F1_IndependentSetMatrix
open Lax496464.WH_F2_MccConstruction (reduce)
open Lax888481.ParameterizedComplexity

/-! ## The polynomial reduction -/

/--
The reduction itself is the witness: it is polynomial-time on the word RAM, correct on the words
of instances, and sends the words that present no instance to no-instances of both problems.
-/
theorem polyReduces_of
    (hpoly : Lax759944.RamPolytime.RamPolytime WH_F2_MccConstruction.reduce)
    (hcorr : ∀ x ∈ problem.Domain,
      (problem.Yes x ↔ Lax888481.MulticolouredClique.problem.Yes (reduce x)))
    (hreject : ∀ x, x ∉ problem.Domain →
      ¬ problem.Yes x ∧ ¬ Lax888481.MulticolouredClique.problem.Yes (reduce x)) :
    Lax888481.PolynomialReduction.PolyReduces {x | problem.Yes x}
      {x | Lax888481.MulticolouredClique.problem.Yes x} := by
  refine ⟨reduce, hpoly, fun x => ?_⟩
  by_cases hx : x ∈ problem.Domain
  · exact hcorr x hx
  · obtain ⟨h1, h2⟩ := hreject x hx
    exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

/-! ## The fpt-reduction -/

/--
The reduction with `h = id` and `g k = (k + 1) ^ 2`: the four requirements of a strict fpt-reduction
are the four hypotheses.
-/
theorem isFptReduction_of
    (hdom : ∀ x ∈ problem.Domain, reduce x ∈ Lax888481.MulticolouredClique.problem.Domain)
    (hcorr : ∀ x ∈ problem.Domain,
      (problem.Yes x ↔ Lax888481.MulticolouredClique.problem.Yes (reduce x)))
    (hparam : ∀ x ∈ problem.Domain,
      Lax888481.MulticolouredClique.problem.param (reduce x) = problem.param x)
    (hfpt : ∃ (prog : Lax808846.Ram.Program) (c : ℕ), ∀ w : ℕ,
      Lax808846.RamComputes.ComputesInTime w prog
        {x | x ∈ problem.Domain ∧ Fits c w x ∧ Fits c w (reduce x)}
        reduce (fun x => c * (problem.param x + 1) ^ 2 * (x.length + 1))) :
    ∃ (prog : Lax808846.Ram.Program) (c : ℕ),
      IsFptReduction problem Lax888481.MulticolouredClique.problem reduce prog c
        (fun k => (k + 1) ^ 2) (fun k => k) := by
  obtain ⟨prog, c, hprog⟩ := hfpt
  exact ⟨prog, c,
    { maps_domain := hdom
      correct := hcorr
      param_le := fun x hx => (hparam x hx).le
      time := hprog }⟩

theorem fptReduces_of_isFptReduction
    (h : ∃ (prog : Lax808846.Ram.Program) (c : ℕ),
      IsFptReduction problem Lax888481.MulticolouredClique.problem reduce prog c
        (fun k => (k + 1) ^ 2) (fun k => k)) :
    Lax888481.ParameterizedComplexity.FptReduces problem
      Lax888481.MulticolouredClique.problem := by
  obtain ⟨prog, c, hr⟩ := h
  exact ⟨reduce, prog, c, _, _, hr⟩

/-! ## NP-hardness -/

open Lax434930.PolynomialTime Lax391470Proofs

/-- The bits of the encoding of an instance, as a list of numbers. -/
theorem word_eq_natBits (I : Lax762056.GraphEncoding.Instance) :
    word I = Lax391470Proofs.Bits.natBits (Lax762056.GraphEncoding.encode I) := by
  simp only [word, Lax391470Proofs.Bits.natBits]
  rfl

/--
Every language in NP reduces to Independent Set by a Turing machine (archive); the machine that
converts the bit word of the resulting instance into the encoding of its list of numbers
(`TMToNats`) and the machine of the word RAM reduction (by the Turing/RAM equivalence) are
composed with it.
-/
theorem mcc_npHard_of
    (hpoly : Lax759944.RamPolytime.RamPolytime WH_F2_MccConstruction.reduce)
    (hword : ∀ I, reduce (word I) = WH_F2_MccConstruction.word I)
    (hcorr : ∀ I, Lax762056.GraphProblems.IndependentSet I ↔
      Lax888481.MulticolouredClique.problem.Yes (WH_F2_MccConstruction.word I)) :
    WH_F3_NPHard.NPHard Lax888481.MulticolouredClique.problem := by
  intro A hA
  obtain ⟨f₁, ⟨t0⟩, h1⟩ :=
    Lax762056.IndependentSetHardness.independentSet_inducedGrid_hardness A hA
  obtain ⟨tn⟩ := Lax391470Proofs.TMToNats.toNats
  let t1 : Turing.TM2ComputableInPolyTime Lax762056.GraphEncoding.encode
      Lax759944.BinaryWordEncoding.encode
      (fun I => Lax391470Proofs.Bits.natBits (Lax762056.GraphEncoding.encode I)) :=
    { tn with outputsFun := fun I => tn.outputsFun (Lax762056.GraphEncoding.encode I) }
  obtain ⟨t01⟩ := Lax391470Proofs.TMCompose.comp t0 t1
  obtain ⟨t2⟩ :=
    (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp hpoly
  obtain ⟨t⟩ := Lax391470Proofs.TMCompose.comp t01 t2
  refine ⟨_, ⟨t⟩, fun x => ?_⟩
  simp only [Function.comp_apply, ← word_eq_natBits, hword]
  rw [← hcorr]
  exact (h1 x).2

/--
As `mcc_npHard_of`, and the word produced is always the word of an instance, because every word
of the construction is (`hdom`).
-/
theorem mcc_npHard_in_of
    (hpoly : Lax759944.RamPolytime.RamPolytime WH_F2_MccConstruction.reduce)
    (hword : ∀ I, reduce (word I) = WH_F2_MccConstruction.word I)
    (hcorr : ∀ I, Lax762056.GraphProblems.IndependentSet I ↔
      Lax888481.MulticolouredClique.problem.Yes (WH_F2_MccConstruction.word I))
    (hdom : ∀ I, WH_F2_MccConstruction.word I ∈ Lax888481.MulticolouredClique.problem.Domain) :
    WH_F3_NPHard.NPHardIn Lax888481.MulticolouredClique.problem := by
  intro A hA
  obtain ⟨f₁, ⟨t0⟩, h1⟩ :=
    Lax762056.IndependentSetHardness.independentSet_inducedGrid_hardness A hA
  obtain ⟨tn⟩ := Lax391470Proofs.TMToNats.toNats
  let t1 : Turing.TM2ComputableInPolyTime Lax762056.GraphEncoding.encode
      Lax759944.BinaryWordEncoding.encode
      (fun I => Lax391470Proofs.Bits.natBits (Lax762056.GraphEncoding.encode I)) :=
    { tn with outputsFun := fun I => tn.outputsFun (Lax762056.GraphEncoding.encode I) }
  obtain ⟨t01⟩ := Lax391470Proofs.TMCompose.comp t0 t1
  obtain ⟨t2⟩ :=
    (Lax759944.TuringRamPolytimeEquivalence.ramPolytime_iff_turingPolytime _).mp hpoly
  obtain ⟨t⟩ := Lax391470Proofs.TMCompose.comp t01 t2
  refine ⟨_, ⟨t⟩, fun x => ⟨?_, ?_⟩⟩
  · simp only [Function.comp_apply, ← word_eq_natBits, hword]
    exact hdom _
  · simp only [Function.comp_apply, ← word_eq_natBits, hword]
    rw [← hcorr]
    exact (h1 x).2

/-! ## The hypotheses are the statements of `WH_F4_IndependentSetToMcc` -/

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_polyTime →
    type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_word →
    (∀ I, Lax762056.GraphProblems.IndependentSet I ↔
      Lax888481.MulticolouredClique.problem.Yes (WH_F2_MccConstruction.word I)) →
    type_of% @Lax496464.WH_F5_MccNPHard.mcc_npHard :=
  fun h1 h2 h3 => mcc_npHard_of h1 h2 h3

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_polyTime →
    type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_correct →
    (∀ x, x ∉ problem.Domain →
      ¬ problem.Yes x ∧ ¬ Lax888481.MulticolouredClique.problem.Yes (reduce x)) →
    type_of% @Lax496464.WH_F4_IndependentSetToMcc.independentSet_polyReduces_mcc :=
  fun h1 h2 h3 => polyReduces_of h1 h2 h3

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_maps_domain →
    type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_correct →
    type_of% @Lax496464.WH_F4_IndependentSetToMcc.parameter_preserved →
    type_of% @Lax496464.WH_F4_IndependentSetToMcc.reduce_fptTime →
    type_of% @Lax496464.WH_F4_IndependentSetToMcc.independentSet_isFptReduction :=
  fun h1 h2 h3 h4 => isFptReduction_of h1 h2 h3 h4

example : type_of% @Lax496464.WH_F4_IndependentSetToMcc.independentSet_isFptReduction →
    type_of% @Lax496464.WH_F4_IndependentSetToMcc.independentSet_fptReduces_mcc :=
  fun h => fptReduces_of_isFptReduction h

end Lax496464Proofs.WHierarchy.MccNP.HardnessProof
