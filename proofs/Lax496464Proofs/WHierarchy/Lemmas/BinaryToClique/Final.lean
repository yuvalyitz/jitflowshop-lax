import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Bounds
import Lax496464Proofs.WHierarchy.Machine.ImpBridge
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-!
# Σ₁[2] model checking to Clique (Flum–Grohe, Lemma 6.14)

The map `Defs.reduce` is a reduction (`MathFinal`), its parameter is at most twice the old one,
and the IMP+ program of `ProgTop` computes it in time `10^7 · 32^|φ| · (|x| + 1)^3`: the graph has
at most `2^q · 4|x| · 2q` vertices for the `q ≤ |φ|` atoms of the formula, and every pair of
vertices is tested with at most one scan of a block.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Final

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding
open Lax496464.WH_A1_FptTime Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems
open Lax496464Proofs.WHierarchy.Machine.ImpBridge Lax496464Proofs.WHierarchy.Machine.SizeFacts
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj5 Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgRow
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgPass Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgGph
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgTop Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Bounds
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-! ### The program solves the reduction -/

theorem solves :
    Solves layout prog (Tapes MathFinal.Src.Domain) (fun y => reduce y.tail) Bv Kc := by
  refine ⟨prog_ok, ?_, ?_⟩
  · intro y _ v hv
    have := le_Mmax hv
    unfold Bv; omega
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨ext x, ?_⟩
    obtain ⟨σ', hr, hq⟩ := prog_spec x (bok x (bnd_le_Bv x)) _ rfl
    exact ⟨σ', hr.mono (by simp [Kc]), hq⟩

/-! ### The cost -/

theorem cost_le (x : List ℕ) {U T N : ℕ} (hU : x.length + 1 ≤ U) (hs : sX x ≤ x.length)
    (hT : 1 ≤ T) (hC : CX x ≤ T) (hq : 2 * qX x ≤ 2 * T) (hN : NGX x ≤ N) :
    Kc (x.length :: x) ≤ 3100 * U * T * ((N + 1) * (N + 1)) := by
  have hlim := limX_le' x
  simp only [Kc, List.tail_cons, Kbody, Kg, K1, K3, Krow, Kadj]
  have hU1 : 1 ≤ U := by omega
  have hN1 : 1 ≤ (N + 1) * (N + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hUT : U ≤ U * T := Nat.le_mul_of_pos_right _ (by omega)
  have hUTN : U * T ≤ U * T * ((N + 1) * (N + 1)) := Nat.le_mul_of_pos_right _ (by omega)
  have hA : (100 + ((60 + 4) * x.length + 400) + 100 + 4) ≤ 668 * U := by omega
  have hR : (100 + ((60 + 4) * x.length + 400) + 100 + 4) * NGX x + 8 ≤ 676 * U * (N + 1) := by
    have := Nat.mul_le_mul hA hN
    nlinarith
  have hK1 : ((100 + ((60 + 4) * x.length + 400) + 100 + 4) * NGX x + 8 + 20 + 4) * NGX x + 8 ≤
      700 * U * ((N + 1) * (N + 1)) := by
    have h1 : (100 + ((60 + 4) * x.length + 400) + 100 + 4) * NGX x + 8 + 20 + 4 ≤
        700 * U * (N + 1) := by nlinarith
    have := Nat.mul_le_mul h1 hN
    nlinarith
  have hK3 : ((100 + ((60 + 4) * x.length + 400) + 100 + 4) * NGX x + 8 + 10 + 4) * NGX x + 6 ≤
      700 * U * ((N + 1) * (N + 1)) := by
    have h1 : (100 + ((60 + 4) * x.length + 400) + 100 + 4) * NGX x + 8 + 10 + 4 ≤
        700 * U * (N + 1) := by nlinarith
    have := Nat.mul_le_mul h1 hN
    nlinarith
  have hCT : ((120 + 4) * x.length + 60 + 4) * CX x ≤ 188 * U * T := by
    have := Nat.mul_le_mul (show (120 + 4) * x.length + 60 + 4 ≤ 188 * U by omega) hC
    nlinarith
  have hsU : (60 + 4) * sX x + 40 ≤ 104 * U := by omega
  have hlU : (30 + 4) * limX x ≤ 34 * U + 68 * T := by omega
  nlinarith

/-! ### Powers -/

theorem pow_facts (b q κ : ℕ) (hq : q ≤ κ) :
    1 ≤ 2 ^ q ∧ q ≤ 2 ^ q ∧ 2 ^ q ≤ 2 ^ κ ∧ b + 1 ≤ 2 ^ b := by
  refine ⟨Nat.one_le_two_pow, (Nat.lt_two_pow_self).le, Nat.pow_le_pow_right (by norm_num) hq,
    Nat.lt_two_pow_self⟩

/-- The function of the parameter. -/
def fB (m : ℕ) : ℕ := 10000000 * 32 ^ m

theorem fB_computable : Computable fB :=
  Lax496464Proofs.WHierarchy.ComputableBounds.computable_mul (Computable.const 10000000)
    (Lax496464Proofs.WHierarchy.ComputableBounds.computable_exp 32 Computable.id)

theorem NG_bound (x : List ℕ) {T : ℕ} (hT : 2 ^ qX x ≤ T) (hq : qX x ≤ T) :
    NGX x ≤ 8 * x.length * (T * T) := by
  have h := NGX_le x
  have h1 : 2 ^ qX x * (4 * x.length * (2 * qX x)) ≤ T * (4 * x.length * (2 * T)) :=
    Nat.mul_le_mul hT (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hq))
  have e : T * (4 * x.length * (2 * T)) = 8 * x.length * (T * T) := by ring
  omega

/-- **The cost bound.** -/
theorem hK {x : List ℕ} (hx : x ∈ MathFinal.Src.Domain) :
    layout.const * Kc (x.length :: x) + 1 ≤
      fptBound fB 3 (MathFinal.Src.param x) (bitSize x) := by
  obtain ⟨hqκ, hs⟩ := inst_facts hx
  set κ := MathFinal.Src.param x
  set b := bitSize x
  set q := qX x
  set T := 2 ^ q with hTdef
  have hL : x.length ≤ b := length_le_bitSize x
  obtain ⟨hT1, hqT, hTκ, -⟩ := pow_facts b q κ hqκ
  have hN := NG_bound x (T := T) (le_of_eq hTdef.symm) hqT
  have hc := cost_le x (U := b + 1) (T := T) (N := 8 * x.length * (T * T)) (by omega) hs hT1
    (by simp only [CX]; exact le_of_eq hTdef.symm) (by omega) hN
  have hN1 : 8 * x.length * (T * T) + 1 ≤ 9 * (b + 1) * (T * T) := by
    have : 1 ≤ T * T := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hsq : (8 * x.length * (T * T) + 1) * (8 * x.length * (T * T) + 1) ≤
      81 * ((b + 1) * (b + 1)) * (T * T * (T * T)) := by
    have := Nat.mul_le_mul hN1 hN1
    nlinarith
  have hT5 : T * (T * T * (T * T)) = 32 ^ q := by
    rw [hTdef, show (32 : ℕ) = 2 ^ 5 by norm_num, ← pow_mul]; ring
  have h32 : 32 ^ q ≤ 32 ^ κ := Nat.pow_le_pow_right (by norm_num) hqκ
  have hmain : Kc (x.length :: x) ≤ 251100 * ((b + 1) ^ 3) * 32 ^ κ := by
    have e1 : 3100 * (b + 1) * T * (81 * ((b + 1) * (b + 1)) * (T * T * (T * T))) =
        251100 * ((b + 1) ^ 3) * (T * (T * T * (T * T))) := by ring
    have := Nat.mul_le_mul_left (3100 * (b + 1) * T) hsq
    rw [e1, hT5] at this
    have h2 : 251100 * ((b + 1) ^ 3) * 32 ^ q ≤ 251100 * ((b + 1) ^ 3) * 32 ^ κ :=
      Nat.mul_le_mul_left _ h32
    omega
  have hpos : 1 ≤ (b + 1) ^ 3 * 32 ^ κ :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  simp only [Layout.const, fptBound, fB]
  nlinarith

/-! ### The value bound -/

theorem Bv_le {x : List ℕ} (hx : x ∈ MathFinal.Src.Domain) :
    100 + 10 * Bv (x.length :: x) ≤ 2 ^ (2 * bitSize x + 4 * MathFinal.Src.param x + 11) := by
  obtain ⟨hqκ, -⟩ := inst_facts hx
  set κ := MathFinal.Src.param x
  set b := bitSize x
  set q := qX x
  set T := 2 ^ q with hTdef
  set P := 2 ^ b with hPdef
  have hL : x.length < P := length_lt_two_pow x
  have hMx : Mmax x < P := Mmax_lt_two_pow x
  obtain ⟨hT1, hqT, hTκ, hbP⟩ := pow_facts b q κ hqκ
  have hN := NG_bound x (T := T) (le_of_eq hTdef.symm) hqT
  have hMy : Mmax (x.length :: x) < P := by rw [Mmax_cons]; exact max_lt hL hMx
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hNP : NGX x + 1 ≤ 9 * P * (T * T) := by
    have : 1 ≤ T * T := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hsq1 : (x.length + Mmax x + 4) * (x.length + Mmax x + 4) ≤ 36 * (P * P) := by
    have : x.length + Mmax x + 4 ≤ 6 * P := by omega
    nlinarith
  set W := P * P * (T * T * (T * T)) with hW
  have hsq2 : (NGX x + 1) * (NGX x + 1) ≤ 81 * W := by
    have := Nat.mul_le_mul hNP hNP
    have e : 9 * P * (T * T) * (9 * P * (T * T)) = 81 * W := by rw [hW]; ring
    omega
  have hT4 : 1 ≤ T * T * (T * T) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hT1' : 1 ≤ T := by rw [hTdef]; exact hT1
  have hPP1 : 1 ≤ P * P := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hCT : CX x ≤ W := by
    simp only [CX]
    have h1 : T ≤ T * T * (T * T) := by
      have : T * 1 ≤ T * (T * (T * T)) :=
        Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.2 (by positivity))
      have e : T * (T * (T * T)) = T * T * (T * T) := by ring
      omega
    have h2 : T * T * (T * T) ≤ W := by rw [hW]; exact Nat.le_mul_of_pos_left _ (by omega)
    rw [← hTdef]; omega
  have hPW : P * P ≤ W := by rw [hW]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hPP : P ≤ P * P := Nat.le_mul_of_pos_right _ (by omega)
  have hBv : Bv (x.length :: x) ≤ 150 * W := by
    simp only [Bv, bnd, List.tail_cons]
    omega
  have hpow : 1600 * W ≤ 2 ^ (2 * b + 4 * κ + 11) := by
    have e : 2 ^ (2 * b + 4 * κ + 11) = 2048 * (P * P * (2 ^ κ * 2 ^ κ * (2 ^ κ * 2 ^ κ))) := by
      rw [hPdef]; ring
    have hTT : T * T * (T * T) ≤ 2 ^ κ * 2 ^ κ * (2 ^ κ * 2 ^ κ) := by
      have := Nat.mul_le_mul hTκ hTκ
      exact Nat.mul_le_mul this this
    rw [e]
    have := Nat.mul_le_mul_left (P * P) hTT
    rw [← hW] at this
    omega
  omega

theorem bound_ge (b κ : ℕ) : 2 * b + 4 * κ + 11 ≤ fptBound fB 3 κ b := by
  simp only [fptBound, fB]
  have h1 : κ < 32 ^ κ := Nat.lt_pow_self (by norm_num)
  have h2 : b + 1 ≤ (b + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h3 : 1 ≤ 32 ^ κ := Nat.one_le_pow _ _ (by norm_num)
  nlinarith

theorem hB_fit {x : List ℕ} (hx : x ∈ MathFinal.Src.Domain) :
    1 < Bv (x.length :: x) ∧
      max (Bv (x.length :: x)) (layout.span (Bv (x.length :: x))) ≤
        2 ^ fptBound fB 3 (MathFinal.Src.param x) (bitSize x) := by
  have h := Bv_le hx
  have hg := bound_ge (bitSize x) (MathFinal.Src.param x)
  have hp := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hg
  refine ⟨by simp only [Bv, bnd, List.tail_cons]; omega, max_le (by omega) ?_⟩
  simp only [Layout.span, layout, scalars, adjVars, List.length_cons, List.length_nil,
    List.length_append]
  omega

/-! ### The outputs -/

theorem out_lt {x : List ℕ} (hx : x ∈ MathFinal.Src.Domain) {v : ℕ} (hv : v ∈ reduce x) :
    v < 2 ^ fptBound fB 3 (MathFinal.Src.param x) (bitSize x) := by
  have h := Bv_le hx
  have hg := bound_ge (bitSize x) (MathFinal.Src.param x)
  have hp := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hg
  suffices hvb : v ≤ bnd x by have := bnd_le_Bv x; omega
  have hP := ps_le_sq' x
  have hk : kX x ≤ 2 * x.length := by have := ProgElb.qX_le x; unfold kX; omega
  have hsq : NGX x * NGX x + 2 * NGX x + 1 = (NGX x + 1) * (NGX x + 1) := by ring
  have hbig : NGX x * NGX x + 2 * x.length ≤ bnd x := by unfold bnd; nlinarith
  rw [reduce_eq] at hv
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap, List.nil_append, List.not_mem_nil, or_false] at hv
  have hN2 : NGX x ≤ NGX x * NGX x ∨ NGX x = 0 := by
    rcases Nat.eq_zero_or_pos (NGX x) with h | h
    · exact Or.inr h
    · exact Or.inl (Nat.le_mul_of_pos_left _ h)
  rcases hv with rfl | rfl | rfl | ((⟨s, hs, rfl⟩ | ⟨s, hs, ht⟩) | rfl)
  · rcases hN2 with h | h <;> omega
  · omega
  · omega
  · have := ps_mono x (show s + 1 ≤ NGX x by omega); omega
  · have : v < NGX x := Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.CsrWord.mem_nbW_lt _ _ ht
    rcases hN2 with h | h <;> omega
  · omega

/-- **The reduction runs in fixed-parameter time.** -/
theorem reduce_fptTime : FptTimeOn MathFinal.Src.Domain MathFinal.Src.param reduce :=
  fptTimeOn_of_solves (f := fB) (d := 3) fB_computable solves (fun _ hx => hB_fit hx)
    (fun _ hx => hK hx) (fun _ hx _ hv => out_lt hx hv)

/--
---
conclusion: Lax496464.WH_D05_BinaryToClique.pMC_binary_le_clique
---
**`p-MC(Σ₁[2]) ≤fpt p-Clique`** (Flum–Grohe, Lemma 6.14). For an instance `(A, ∃x̄ ψ)`, list the `q`
atoms of `ψ` and their two variables (`2q` rows); for every truth valuation `c` of the atoms under
which `ψ` holds, the vertices `(c, e, r)` — a candidate value `e` for the variable of row `r` — are
joined when their rows differ, rows of one variable carry one value, and the two rows of an atom
carry values that give the atom the truth value `c` assigns it. A `2q`-clique is exactly a
satisfying assignment. The candidates are the entries of the word inside the universe and the first
`|x| + 2q` elements (isolated elements are interchangeable), so the graph has at most
`2^q · 4|x| · 2q` vertices; the new parameter is `2q ≤ 2|φ|`.
-/
theorem pMC_binary_le_clique :
    Lax496464.WH_B3_LogicProblems.pMC {φ | Lax496464.WH_B2_FirstOrder.IsSigma 1 φ ∧ φ.ArityAtMost 2}
      ≤ᶠᵖᵗ Clique :=
  ⟨reduce, MathFinal.reduce_isReduction, MathFinal.reduce_paramBounded, reduce_fptTime⟩

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Final
