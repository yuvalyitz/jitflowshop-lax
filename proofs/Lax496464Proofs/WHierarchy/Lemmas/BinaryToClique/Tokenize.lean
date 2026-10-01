import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.FormulaData
import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.StructWord
import Lax496464Proofs.WHierarchy.Logic.FormulaCode

/-!
# Σ₁[2] model checking to Clique: the tokenizer on a formula

Started at the code of a quantifier-free formula `ψ` (no relation variable, arity at most two), the
tokenizer takes one step per node of `ψ` and appends exactly the data of `ψ` (`after`): its nodes,
the variables of its atoms, the block starts and arities of their symbols, and it clears the flag
unless every atom fits. A quantifier prefix `∃x₁ … ∃xₖ` is skipped in `k` steps. So on the word of a
model-checking instance the tokenizer ends with the data of the quantifier-free part (`tok_eq`).
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Tokenize

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.FormulaData Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.StructWord

variable (x : List ℕ)

/-- The block start recorded for an atom. -/
def abA : Formula → ℕ
  | .rel i _ => if i < sX x then hp x i else 0
  | _ => 0

/-- The arity recorded for an atom. -/
def arA : Formula → ℕ
  | .rel i _ => if i < sX x then rd x (1 + i) else 0
  | _ => 0

/-- The atom fits the vocabulary of the word. -/
def fitA : Formula → Bool
  | .rel i xs => decide (i < sX x) && (xs.length == rd x (1 + i))
  | _ => true

/-- Every atom fits. -/
def fitsB (ψ : Formula) : Bool := (atoms ψ).all (fitA x)

/-- The state after the tokenizer has read `ψ`. -/
def after (st : TS) (ψ : Formula) : TS where
  p := st.p + ψ.encode.length
  nd := st.nd ++ toks ψ st.ab.length
  vs := st.vs ++ vsOf ψ
  ab := st.ab ++ (atoms ψ).map (abA x)
  ar := st.ar ++ (atoms ψ).map (arA x)
  fl := if fitsB x ψ then st.fl else 0

variable {x}

theorem length_toks : ∀ (ψ : Formula) (off off' : ℕ), (toks ψ off).length = (toks ψ off').length
  | .rel _ _, _, _ => rfl
  | .eq _ _, _, _ => rfl
  | .setVar _, _, _ => rfl
  | .neg φ, off, off' => by simp [toks, length_toks φ off off']
  | .and φ ψ, off, off' => by
    simp [toks, length_toks φ off off', length_toks ψ (off + nA φ) (off' + nA φ)]
  | .or φ ψ, off, off' => by
    simp [toks, length_toks φ off off', length_toks ψ (off + nA φ) (off' + nA φ)]
  | .ex _ _, _, _ => rfl
  | .all _ _, _, _ => rfl

theorem length_toks_le : ∀ (ψ : Formula) (off : ℕ), (toks ψ off).length ≤ ψ.encode.length
  | .rel _ _, _ => by simp [toks, Formula.encode]
  | .eq _ _, _ => by simp [toks, Formula.encode]
  | .setVar _, _ => by simp [toks, Formula.encode]
  | .neg φ, off => by have := length_toks_le φ off; simp [toks, Formula.encode]; omega
  | .and φ ψ, off => by
    have := length_toks_le φ off; have := length_toks_le ψ (off + nA φ)
    simp [toks, Formula.encode]; omega
  | .or φ ψ, off => by
    have := length_toks_le φ off; have := length_toks_le ψ (off + nA φ)
    simp [toks, Formula.encode]; omega
  | .ex _ _, _ => by simp [toks]
  | .all _ _, _ => by simp [toks]

theorem drop_succ_of {p : ℕ} {a : ℕ} {l : List ℕ} (h : x.drop p = a :: l) : x.drop (p + 1) = l := by
  rw [← List.drop_drop, h]; rfl

theorem drop_add_of {p : ℕ} {l l' : List ℕ} (h : x.drop p = l ++ l') :
    x.drop (p + l.length) = l' := by
  rw [← List.drop_drop, h, List.drop_left]

theorem lt_of_drop {p : ℕ} {a : ℕ} {l : List ℕ} (h : x.drop p = a :: l) : p < x.length := by
  by_contra hc
  rw [List.drop_eq_nil_of_le (by omega)] at h
  simp at h

theorem rd_of_drop {p : ℕ} {l : List ℕ} (h : x.drop p = l) (j : ℕ) : rd x (p + j) = l.getD j 0 := by
  rw [rd_add, h]

theorem rd_of_drop0 {p : ℕ} {l : List ℕ} (h : x.drop p = l) : rd x p = l.getD 0 0 := by
  rw [← rd_of_drop h 0]; rfl

/-- **The tokenizer reads a quantifier-free formula.** -/
theorem iterate_toks : ∀ (ψ : Formula), ψ.IsQF → ψ.NoSetVar → ψ.ArityAtMost 2 →
    ∀ (st : TS) (rest : List ℕ), x.drop st.p = ψ.encode ++ rest →
      (tokStep x)^[(toks ψ 0).length] st = after x st ψ
  | .rel i xs, _, _, har, st, rest, hd => by
    have hd' : x.drop st.p = 0 :: i :: xs.length :: (xs ++ rest) := by
      rw [hd]; simp [Formula.encode]
    have hlt := lt_of_drop hd'
    have r0 : rd x st.p = 0 := by rw [rd_of_drop0 hd']; rfl
    have r1 : rd x (st.p + 1) = i := by rw [rd_of_drop hd']; rfl
    have r2 : rd x (st.p + 2) = xs.length := by rw [rd_of_drop hd']; rfl
    have r3 : rd x (st.p + 3) = (xs ++ rest).getD 0 0 := by rw [rd_of_drop hd']; rfl
    have r4 : rd x (st.p + 4) = (xs ++ rest).getD 1 0 := by rw [rd_of_drop hd']; rfl
    have hlen : st.p + 3 + xs.length ≤ x.length := by
      have := congrArg List.length hd'
      simp only [List.length_drop, List.length_cons, List.length_append] at this
      omega
    have har' : xs.length ≤ 2 := har
    simp only [toks, List.length_singleton, Function.iterate_one, tokStep, if_pos hlt, r0,
      if_neg (show (0 : ℕ) ≠ 6 by decide), ↓reduceIte]
    simp only [relStep, after, r1, r2, r3, r4, toks, atoms, List.map_cons, List.map_nil, abA, arA,
      fitsB, List.all_cons, List.all_nil, fitA, Bool.and_true, vsOf, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, apair, Formula.encode, List.length_cons]
    rw [TS.mk.injEq]
    refine ⟨?_, rfl, ?_, rfl, rfl, ?_⟩
    · rw [if_pos (by omega)]; omega
    · congr 1
      match xs, har' with
      | [], _ => simp
      | [a], _ => simp
      | [a, b], _ => simp
    · by_cases hi : i < sX x
      · by_cases hn : xs.length = rd x (1 + i) <;> simp [hi, hn]
      · simp [hi]
  | .eq a b, _, _, _, st, rest, hd => by
    have hd' : x.drop st.p = 2 :: a :: b :: rest := by rw [hd]; simp [Formula.encode]
    have hlt := lt_of_drop hd'
    have r0 : rd x st.p = 2 := by rw [rd_of_drop0 hd']; rfl
    have r1 : rd x (st.p + 1) = a := by rw [rd_of_drop hd']; rfl
    have r2 : rd x (st.p + 2) = b := by rw [rd_of_drop hd']; rfl
    simp only [toks, List.length_singleton, Function.iterate_one, tokStep, if_pos hlt, r0,
      if_neg (show (2 : ℕ) ≠ 6 by decide), if_neg (show (2 : ℕ) ≠ 0 by decide), ↓reduceIte]
    simp only [eqStep, after, r1, r2, toks, atoms, List.map_cons, List.map_nil, abA, arA, fitsB,
      List.all_cons, List.all_nil, fitA, Bool.and_true, vsOf, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, apair, Formula.encode, List.length_cons, List.length_nil, if_true]
  | .setVar _, _, hn, _, _, _, _ => absurd hn id
  | .neg φ, hq, hn, ha, st, rest, hd => by
    have hd' : x.drop st.p = 3 :: (φ.encode ++ rest) := by rw [hd]; simp [Formula.encode]
    have hlt := lt_of_drop hd'
    have r0 : rd x st.p = 3 := by rw [rd_of_drop0 hd']; rfl
    have h1 : tokStep x st = { st with p := st.p + 1, nd := st.nd ++ [(3, 0)] } := by
      simp only [tokStep, if_pos hlt, r0, otherStep]; simp
    have ih := iterate_toks φ hq hn ha { st with p := st.p + 1, nd := st.nd ++ [(3, 0)] } rest
      (drop_succ_of hd')
    simp only [toks, List.length_cons, Function.iterate_succ_apply, h1, ih]
    rw [length_toks φ 0 0] at ih
    simp only [after, toks, atoms, vsOf, fitsB, Formula.encode, List.length_cons, List.append_assoc,
      List.singleton_append]
    rw [TS.mk.injEq]
    refine ⟨by omega, rfl, rfl, rfl, rfl, rfl⟩
  | .and φ ψ, hq, hn, ha, st, rest, hd => by
    have hd' : x.drop st.p = 4 :: (φ.encode ++ (ψ.encode ++ rest)) := by
      rw [hd]; simp [Formula.encode]
    have hlt := lt_of_drop hd'
    have r0 : rd x st.p = 4 := by rw [rd_of_drop0 hd']; rfl
    set st1 : TS := { st with p := st.p + 1, nd := st.nd ++ [(4, 0)] } with hst1
    have h1 : tokStep x st = st1 := by
      simp only [tokStep, if_pos hlt, r0, otherStep, hst1]; simp
    have ih1 := iterate_toks φ hq.1 hn.1 ha.1 st1 (ψ.encode ++ rest) (drop_succ_of hd')
    have hd2 : x.drop (after x st1 φ).p = ψ.encode ++ rest := by
      simp only [after, hst1]; exact drop_add_of (drop_succ_of hd')
    have ih2 := iterate_toks ψ hq.2 hn.2 ha.2 (after x st1 φ) rest hd2
    have hlen : (toks (.and φ ψ) 0).length = (toks ψ 0).length + ((toks φ 0).length + 1) := by
      simp [toks, length_toks ψ (nA φ) 0]; omega
    rw [hlen, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, h1, ih1,
      ih2]
    simp only [after, hst1, toks, atoms, vsOf, fitsB, Formula.encode, List.length_cons,
      List.length_append, List.append_assoc, List.map_append,
      List.flatMap_append, List.all_append, List.cons_append, List.length_map]
    rw [TS.mk.injEq]
    refine ⟨by omega, ?_, rfl, rfl, rfl, ?_⟩
    · rw [length_atoms]; simp
    · cases hφ : (atoms φ).all (fitA x) <;> cases hψ : (atoms ψ).all (fitA x) <;> simp
  | .or φ ψ, hq, hn, ha, st, rest, hd => by
    have hd' : x.drop st.p = 5 :: (φ.encode ++ (ψ.encode ++ rest)) := by
      rw [hd]; simp [Formula.encode]
    have hlt := lt_of_drop hd'
    have r0 : rd x st.p = 5 := by rw [rd_of_drop0 hd']; rfl
    set st1 : TS := { st with p := st.p + 1, nd := st.nd ++ [(5, 0)] } with hst1
    have h1 : tokStep x st = st1 := by
      simp only [tokStep, if_pos hlt, r0, otherStep, hst1]; simp
    have ih1 := iterate_toks φ hq.1 hn.1 ha.1 st1 (ψ.encode ++ rest) (drop_succ_of hd')
    have hd2 : x.drop (after x st1 φ).p = ψ.encode ++ rest := by
      simp only [after, hst1]; exact drop_add_of (drop_succ_of hd')
    have ih2 := iterate_toks ψ hq.2 hn.2 ha.2 (after x st1 φ) rest hd2
    have hlen : (toks (.or φ ψ) 0).length = (toks ψ 0).length + ((toks φ 0).length + 1) := by
      simp [toks, length_toks ψ (nA φ) 0]; omega
    rw [hlen, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, h1, ih1,
      ih2]
    simp only [after, hst1, toks, atoms, vsOf, fitsB, Formula.encode, List.length_cons,
      List.length_append, List.append_assoc, List.map_append,
      List.flatMap_append, List.all_append, List.cons_append, List.length_map]
    rw [TS.mk.injEq]
    refine ⟨by omega, ?_, rfl, rfl, rfl, ?_⟩
    · rw [length_atoms]; simp
    · cases hφ : (atoms φ).all (fitA x) <;> cases hψ : (atoms ψ).all (fitA x) <;> simp
  | .ex _ _, hq, _, _, _, _, _ => absurd hq id
  | .all _ _, hq, _, _, _, _, _ => absurd hq id

/-- **The tokenizer skips a quantifier prefix.** -/
theorem iterate_prefix : ∀ (xs : List ℕ) (st : TS) (rest : List ℕ), rest ≠ [] →
    x.drop st.p = xs.flatMap (fun v => [6, v]) ++ rest →
      (tokStep x)^[xs.length] st = { st with p := st.p + 2 * xs.length }
  | [], st, _, _, _ => by simp
  | v :: xs, st, rest, hr, hd => by
    have hd' : x.drop st.p = 6 :: v :: (xs.flatMap (fun v => [6, v]) ++ rest) := by
      rw [hd]; simp
    have hlt := lt_of_drop hd'
    have r0 : rd x st.p = 6 := by rw [rd_of_drop0 hd']; rfl
    have h1 : tokStep x st = { st with p := st.p + 2 } := by
      simp only [tokStep, if_pos hlt, r0, if_true]
    have hd2 : x.drop (st.p + 2) = xs.flatMap (fun v => [6, v]) ++ rest :=
      drop_succ_of (drop_succ_of hd')
    rw [List.length_cons, Function.iterate_succ_apply, h1,
      iterate_prefix xs { st with p := st.p + 2 } rest hr hd2]
    rw [TS.mk.injEq]
    refine ⟨by dsimp only; omega, rfl, rfl, rfl, rfl, rfl⟩

/-- Past the end of the word the tokenizer stops. -/
theorem iterate_stop (st : TS) (h : x.length ≤ st.p) : ∀ n, (tokStep x)^[n] st = st
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply]
    have : tokStep x st = st := by simp only [tokStep, if_neg (show ¬ st.p < x.length by omega)]
    rw [this, iterate_stop st h n]

/-- **The tokenizer on a model-checking word.** -/
theorem tok_eq {y : List ℕ} {A : Structure} {xs : List ℕ} {ψ : Formula} (hy : Encodes y A)
    (hx : x = y ++ (Formula.exBlock xs ψ).encode) (hq : ψ.IsQF) (hn : ψ.NoSetVar)
    (ha : ψ.ArityAtMost 2) :
    tok x = TS.mk x.length (toks ψ 0) (vsOf ψ) ((atoms ψ).map (abA x)) ((atoms ψ).map (arA x))
      (if fitsB x ψ then 1 else 0) := by
  obtain ⟨blocks, hsw⟩ := SW.of_encodes (rest := (Formula.exBlock xs ψ).encode) hy
  rw [← hx] at hsw
  have hp0 : (tokInit x).p = y.length := by
    simp only [tokInit]; rw [hsw.sX_eq, hsw.hp_last]
  have henc := Lax496464Proofs.WHierarchy.Logic.SatFacts.encode_exBlock ψ xs
  have hne : ψ.encode ≠ [] := Lax496464Proofs.WHierarchy.Logic.FormulaCode.encode_ne_nil ψ
  have hd0 : x.drop (tokInit x).p = xs.flatMap (fun v => [6, v]) ++ ψ.encode := by
    rw [hp0, hx, List.drop_left, henc]
  have h1 := iterate_prefix xs (tokInit x) ψ.encode hne hd0
  set st1 : TS := ({ tokInit x with p := (tokInit x).p + 2 * xs.length } : TS) with hst1
  have hflat : (xs.flatMap (fun v => [6, v])).length = 2 * xs.length := by
    induction xs with
    | nil => simp
    | cons v xs ih => simp [List.flatMap_cons]; ring
  have hd1 : x.drop st1.p = ψ.encode ++ [] := by
    rw [List.append_nil, hst1, ← hflat]
    exact drop_add_of hd0
  have h2 := iterate_toks ψ hq hn ha st1 [] hd1
  have hL : x.length = y.length + 2 * xs.length + ψ.encode.length := by
    rw [hx, List.length_append, henc, List.length_append, hflat]; ring
  have hT := length_toks_le ψ 0
  unfold tok
  have hsplit : x.length = (x.length - (toks ψ 0).length - xs.length) + ((toks ψ 0).length +
      xs.length) := by omega
  rw [hsplit, Function.iterate_add_apply, Function.iterate_add_apply, h1, h2, ← hsplit]
  rw [iterate_stop _ (by simp only [after, hst1, hp0]; omega)]
  simp only [after, hst1, tokInit, List.nil_append, List.length_nil]
  rw [TS.mk.injEq]
  have hp0' : hp x (sX x) = y.length := hp0
  refine ⟨by rw [hp0']; omega, rfl, rfl, rfl, rfl, rfl⟩

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Tokenize
