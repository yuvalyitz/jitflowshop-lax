import Lax496464.WH_B3_LogicProblems
import Lax496464Proofs.WHierarchy.Logic.FormulaCode
import Lax496464Proofs.WHierarchy.Logic.StructureCode

/-! The words of the logic problems determine their instances: a model-checking word determines
its structure and formula, a weighted-definability word its structure and `k`; and the parameters
of the two problems are the size of that formula and that `k`. -/

namespace Lax496464Proofs.WHierarchy.Logic.Words

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.FormulaCode Lax496464Proofs.WHierarchy.Logic.StructureCode

/-- **A model-checking word determines its structure and formula.** -/
theorem encodesMC_unique {x : List ℕ} {A A' : Structure} {φ φ' : Formula}
    (h : EncodesMC x A φ) (h' : EncodesMC x A' φ') : A = A' ∧ φ = φ' := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨y', hy', he⟩ := h'
  obtain ⟨-, rfl, hφ⟩ := encodes_prefix hy hy' he
  exact ⟨rfl, encode_injective hφ⟩

/-- **A weighted-definability word determines its structure and `k`.** -/
theorem encodesWD_unique {x : List ℕ} {A A' : Structure} {k k' : ℕ}
    (h : EncodesWD x A k) (h' : EncodesWD x A' k') : A = A' ∧ k = k' := by
  obtain ⟨y, hy, rfl⟩ := h
  obtain ⟨y', hy', he⟩ := h'
  obtain ⟨-, rfl, hk⟩ := encodes_prefix hy hy' he
  exact ⟨rfl, by simpa using hk⟩

/-- **The parameter of a model-checking word is the size of its formula.** -/
theorem mcParam_eq {x : List ℕ} {A : Structure} {φ : Formula} (h : EncodesMC x A φ) :
    mcParam x = φ.size := by
  have hex : ∃ p : Structure × Formula, EncodesMC x p.1 p.2 := ⟨(A, φ), h⟩
  unfold mcParam
  rw [dif_pos hex]
  rw [(encodesMC_unique (Classical.choose_spec hex) h).2]

/-- The parameter of `p-MC(Φ)` on a word encoding `(A, φ)`. -/
theorem pMC_param_eq (Φ : Set Formula) {x : List ℕ} {A : Structure} {φ : Formula}
    (h : EncodesMC x A φ) : (pMC Φ).param x = φ.size := mcParam_eq h

/-- **The parameter of a weighted-definability word is its `k`.** -/
theorem wdParam_eq {x : List ℕ} {A : Structure} {k : ℕ} (h : EncodesWD x A k) :
    x.getLast?.getD 0 = k := by
  obtain ⟨y, -, rfl⟩ := h
  simp

/-- The parameter of `p-WD_φ` on a word encoding `(A, k)`. -/
theorem pWD_param_eq (φ : Formula) (s : ℕ) {x : List ℕ} {A : Structure} {k : ℕ}
    (h : EncodesWD x A k) : (pWD φ s).param x = k := wdParam_eq h

/-- A yes-instance of `p-MC(Φ)`, read through any encoding of the word. -/
theorem pMC_yes_iff (Φ : Set Formula) {x : List ℕ} {A : Structure} {φ : Formula}
    (h : EncodesMC x A φ) : (pMC Φ).Yes x ↔ Models A φ := by
  constructor
  · rintro ⟨A', φ', h', hm⟩
    obtain ⟨rfl, rfl⟩ := encodesMC_unique h' h
    exact hm
  · exact fun hm => ⟨A, φ, h, hm⟩

/-- A yes-instance of `p-WD_φ`, read through any encoding of the word. -/
theorem pWD_yes_iff (φ : Formula) (s : ℕ) {x : List ℕ} {A : Structure} {k : ℕ}
    (h : EncodesWD x A k) : (pWD φ s).Yes x ↔ Witness A φ s k := by
  constructor
  · rintro ⟨A', k', h', hw⟩
    obtain ⟨rfl, rfl⟩ := encodesWD_unique h' h
    exact hw
  · exact fun hw => ⟨A, k, h, hw⟩

/-- A word of a structure followed by a formula is a model-checking word. -/
theorem encodesMC_append {y : List ℕ} {A : Structure} (hy : Encodes y A) (φ : Formula) :
    EncodesMC (y ++ φ.encode) A φ := ⟨y, hy, rfl⟩

/-- A word of a structure followed by `k` is a weighted-definability word. -/
theorem encodesWD_append {y : List ℕ} {A : Structure} (hy : Encodes y A) (k : ℕ) :
    EncodesWD (y ++ [k]) A k := ⟨y, hy, rfl⟩

/-- The canonical model-checking word of `(A, φ)`. -/
def mcWord (A : Structure) (φ : Formula) : List ℕ := canonicalWord A ++ φ.encode

theorem encodesMC_mcWord (A : Structure) (φ : Formula) : EncodesMC (mcWord A φ) A φ :=
  encodesMC_append (encodes_canonicalWord A) φ

/-- The canonical weighted-definability word of `(A, k)`. -/
def wdWord (A : Structure) (k : ℕ) : List ℕ := canonicalWord A ++ [k]

theorem encodesWD_wdWord (A : Structure) (k : ℕ) : EncodesWD (wdWord A k) A k :=
  encodesWD_append (encodes_canonicalWord A) k

end Lax496464Proofs.WHierarchy.Logic.Words
