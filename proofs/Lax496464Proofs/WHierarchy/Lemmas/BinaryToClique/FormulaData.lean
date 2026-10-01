import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
import Lax496464.WH_B3_LogicProblems
import Lax496464Proofs.WHierarchy.Logic.SatFacts

/-!
# Σ₁[2] model checking to Clique: the data of a quantifier-free formula

For a quantifier-free formula `ψ`: its atoms in prefix order (`atoms`, `nA` of them), its nodes in
prefix order (`toks`, the tag and the atom number of each node), the two variables of each atom
(`apair`, listed by `vsOf`), and its value as a Boolean combination of its atoms (`evalPat`).

* `sat_iff_evalPat`: `ψ` holds iff its Boolean combination holds of the truth values of its atoms;
* `foldr_toks`: the right-to-left stack evaluation of the nodes computes that Boolean combination;
* `mem_freeVars_iff`: the variables of `ψ` are the variables listed by `vsOf`, when every atom is an
  equation or a relation atom with one or two arguments (`GoodAtom`).
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.FormulaData

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs

/-- The number of atoms (relation atoms and equations). -/
def nA : Formula → ℕ
  | .rel _ _ => 1
  | .eq _ _ => 1
  | .neg φ => nA φ
  | .and φ ψ => nA φ + nA ψ
  | .or φ ψ => nA φ + nA ψ
  | _ => 0

/-- The atoms, in prefix order. -/
def atoms : Formula → List Formula
  | .rel i xs => [.rel i xs]
  | .eq a b => [.eq a b]
  | .neg φ => atoms φ
  | .and φ ψ => atoms φ ++ atoms ψ
  | .or φ ψ => atoms φ ++ atoms ψ
  | _ => []

theorem length_atoms : ∀ ψ : Formula, (atoms ψ).length = nA ψ
  | .rel _ _ => rfl
  | .eq _ _ => rfl
  | .setVar _ => rfl
  | .neg φ => length_atoms φ
  | .and φ ψ => by simp [atoms, nA, length_atoms φ, length_atoms ψ]
  | .or φ ψ => by simp [atoms, nA, length_atoms φ, length_atoms ψ]
  | .ex _ _ => rfl
  | .all _ _ => rfl

/-- The nodes in prefix order: tag, and atom number (from `off`) for an atom. -/
def toks : Formula → ℕ → List (ℕ × ℕ)
  | .rel _ _, off => [(0, off)]
  | .eq _ _, off => [(2, off)]
  | .setVar _, _ => [(1, 0)]
  | .neg φ, off => (3, 0) :: toks φ off
  | .and φ ψ, off => (4, 0) :: (toks φ off ++ toks ψ (off + nA φ))
  | .or φ ψ, off => (5, 0) :: (toks φ off ++ toks ψ (off + nA φ))
  | _, _ => []

/-- The formula as a Boolean combination of the values `β (off + m)` of its atoms. -/
def evalPat : Formula → (ℕ → Bool) → ℕ → Bool
  | .rel _ _, β, off => β off
  | .eq _ _, β, off => β off
  | .neg φ, β, off => !evalPat φ β off
  | .and φ ψ, β, off => evalPat φ β off && evalPat ψ β (off + nA φ)
  | .or φ ψ, β, off => evalPat φ β off || evalPat ψ β (off + nA φ)
  | _, _, _ => false

/-- The two variables of an atom (the only one twice for a unary atom). -/
def apair : Formula → ℕ × ℕ
  | .rel _ xs => (xs.headD 0, if xs.length = 2 then xs.getD 1 0 else xs.headD 0)
  | .eq a b => (a, b)
  | _ => (0, 0)

/-- The variables of the atoms, two per atom. -/
def vsOf (ψ : Formula) : List ℕ := (atoms ψ).flatMap fun α => [(apair α).1, (apair α).2]

/-- The default atom. -/
def dflt : Formula := .eq 0 0

/-! ### Satisfaction as a Boolean combination -/

theorem getD_append_left {α : Type} {l l' : List α} {m : ℕ} {d : α} (h : m < l.length) :
    (l ++ l').getD m d = l.getD m d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type} {l l' : List α} {m : ℕ} {d : α} :
    (l ++ l').getD (l.length + m) d = l'.getD m d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega)]
  congr 2; omega

theorem sat_iff_evalPat (A : Structure) (S : Set (List ℕ)) (ρ : ℕ → ℕ) :
    ∀ (ψ : Formula), ψ.IsQF → ψ.NoSetVar → ∀ (β : ℕ → Bool) (off : ℕ),
      (∀ m < nA ψ, (β (off + m) = true ↔ Sat A S ((atoms ψ).getD m dflt) ρ)) →
      (evalPat ψ β off = true ↔ Sat A S ψ ρ)
  | .rel i xs, _, _, β, off, h => by simpa [evalPat, atoms] using h 0 (by simp [nA])
  | .eq a b, _, _, β, off, h => by simpa [evalPat, atoms] using h 0 (by simp [nA])
  | .setVar _, _, hn, _, _, _ => absurd hn id
  | .neg φ, hq, hn, β, off, h => by
    simp only [evalPat, Sat, Bool.not_eq_true']
    rw [← sat_iff_evalPat A S ρ φ hq hn β off h]
    simp
  | .and φ ψ, hq, hn, β, off, h => by
    simp only [evalPat, Sat, Bool.and_eq_true]
    have hl := length_atoms φ
    rw [sat_iff_evalPat A S ρ φ hq.1 hn.1 β off fun m hm => by
        rw [h m (by simp [nA]; omega)]; simp only [atoms]; rw [getD_append_left (by omega)],
      sat_iff_evalPat A S ρ ψ hq.2 hn.2 β (off + nA φ) fun m hm => by
        rw [Nat.add_assoc, h (nA φ + m) (by simp [nA]; omega)]; simp only [atoms]
        rw [← hl, getD_append_right']]
  | .or φ ψ, hq, hn, β, off, h => by
    simp only [evalPat, Sat, Bool.or_eq_true]
    have hl := length_atoms φ
    rw [sat_iff_evalPat A S ρ φ hq.1 hn.1 β off fun m hm => by
        rw [h m (by simp [nA]; omega)]; simp only [atoms]; rw [getD_append_left (by omega)],
      sat_iff_evalPat A S ρ ψ hq.2 hn.2 β (off + nA φ) fun m hm => by
        rw [Nat.add_assoc, h (nA φ + m) (by simp [nA]; omega)]; simp only [atoms]
        rw [← hl, getD_append_right']]
  | .ex _ _, hq, _, _, _, _ => absurd hq id
  | .all _ _, hq, _, _, _, _ => absurd hq id

/-! ### The stack evaluation -/

/-- The value of a formula under the valuation `c`, as `0` or `1`. -/
def valN (ψ : Formula) (c off : ℕ) : ℕ := if evalPat ψ (fun m => bitv c m == 1) off then 1 else 0

theorem bitv_eq_valN (c off : ℕ) (i : ℕ) (xs : List ℕ) :
    bitv c off = valN (.rel i xs) c off := by
  unfold valN evalPat
  have := bitv_le_one c off
  by_cases h : bitv c off = 1 <;> simp [h]
  omega

theorem bitv_eq_valN_eq (c off a b : ℕ) : bitv c off = valN (.eq a b) c off := by
  unfold valN evalPat
  have := bitv_le_one c off
  by_cases h : bitv c off = 1 <;> simp [h]
  omega

/-- **The stack evaluation of the nodes of a formula pushes its value.** -/
theorem foldr_toks (c : ℕ) :
    ∀ (ψ : Formula), ψ.IsQF → ψ.NoSetVar → ∀ (off : ℕ) (l : List ℕ),
      (toks ψ off).foldr (evStep c) l = valN ψ c off :: l
  | .rel i xs, _, _, off, l => by
    have e : evStep c (0, off) l = bitv c off :: l := by simp [evStep]
    simp only [toks, List.foldr_cons, List.foldr_nil, e, bitv_eq_valN c off i xs]
  | .eq a b, _, _, off, l => by
    have e : evStep c (2, off) l = bitv c off :: l := by simp [evStep]
    simp only [toks, List.foldr_cons, List.foldr_nil, e, bitv_eq_valN_eq c off a b]
  | .setVar _, _, hn, _, _ => absurd hn id
  | .neg φ, hq, hn, off, l => by
    simp only [toks, List.foldr_cons, foldr_toks c φ hq hn off l]
    simp only [evStep]
    cases h : evalPat φ (fun m => bitv c m == 1) off <;> simp [valN, evalPat, h]
  | .and φ ψ, hq, hn, off, l => by
    simp only [toks, List.foldr_cons, List.foldr_append, foldr_toks c ψ hq.2 hn.2,
      foldr_toks c φ hq.1 hn.1]
    simp only [evStep]
    simp [valN, evalPat]
    split_ifs <;> simp_all
  | .or φ ψ, hq, hn, off, l => by
    simp only [toks, List.foldr_cons, List.foldr_append, foldr_toks c ψ hq.2 hn.2,
      foldr_toks c φ hq.1 hn.1]
    simp only [evStep]
    simp [valN, evalPat]
    split_ifs <;> simp_all
  | .ex _ _, hq, _, _, _ => absurd hq id
  | .all _ _, hq, _, _, _ => absurd hq id

/-! ### Atoms and variables -/

/-- An equation, or a relation atom with one or two arguments. -/
def GoodAtom : Formula → Prop
  | .rel _ xs => 1 ≤ xs.length ∧ xs.length ≤ 2
  | .eq _ _ => True
  | _ => False

/-- The variables of a good atom are its two variables. -/
theorem freeVars_goodAtom : ∀ α : Formula, GoodAtom α →
    ∀ v, v ∈ α.freeVars ↔ v = (apair α).1 ∨ v = (apair α).2
  | .rel i xs, h, v => by
    obtain ⟨h1, h2⟩ := h
    simp only [Formula.freeVars, List.mem_toFinset, apair]
    match xs, h1, h2 with
    | [a], _, _ => simp
    | [a, b], _, _ => simp
    | a :: b :: c :: t, _, h2 => simp at h2
  | .eq a b, _, v => by simp [Formula.freeVars, apair]
  | .setVar _, h, _ => absurd h id
  | .neg _, h, _ => absurd h id
  | .and _ _, h, _ => absurd h id
  | .or _ _, h, _ => absurd h id
  | .ex _ _, h, _ => absurd h id
  | .all _ _, h, _ => absurd h id

/-- The variables of a quantifier-free formula without the relation variable are those of its
atoms. -/
theorem mem_freeVars_atoms : ∀ (ψ : Formula), ψ.IsQF → ψ.NoSetVar →
    ∀ v, v ∈ ψ.freeVars ↔ ∃ α ∈ atoms ψ, v ∈ α.freeVars
  | .rel i xs, _, _, v => by simp [atoms]
  | .eq a b, _, _, v => by simp [atoms]
  | .setVar _, _, hn, _ => absurd hn id
  | .neg φ, hq, hn, v => mem_freeVars_atoms φ hq hn v
  | .and φ ψ, hq, hn, v => by
    simp only [Formula.freeVars, Finset.mem_union, atoms, List.mem_append,
      mem_freeVars_atoms φ hq.1 hn.1 v, mem_freeVars_atoms ψ hq.2 hn.2 v]
    constructor
    · rintro (⟨α, h1, h2⟩ | ⟨α, h1, h2⟩)
      · exact ⟨α, Or.inl h1, h2⟩
      · exact ⟨α, Or.inr h1, h2⟩
    · rintro ⟨α, h1 | h1, h2⟩
      · exact Or.inl ⟨α, h1, h2⟩
      · exact Or.inr ⟨α, h1, h2⟩
  | .or φ ψ, hq, hn, v => by
    simp only [Formula.freeVars, Finset.mem_union, atoms, List.mem_append,
      mem_freeVars_atoms φ hq.1 hn.1 v, mem_freeVars_atoms ψ hq.2 hn.2 v]
    constructor
    · rintro (⟨α, h1, h2⟩ | ⟨α, h1, h2⟩)
      · exact ⟨α, Or.inl h1, h2⟩
      · exact ⟨α, Or.inr h1, h2⟩
    · rintro ⟨α, h1 | h1, h2⟩
      · exact Or.inl ⟨α, h1, h2⟩
      · exact Or.inr ⟨α, h1, h2⟩
  | .ex _ _, hq, _, _ => absurd hq id
  | .all _ _, hq, _, _ => absurd hq id

theorem getD_flatMap_pair {α : Type} (f g : α → ℕ) :
    ∀ (l : List α) (m : ℕ) (d : α), m < l.length →
      (l.flatMap fun a => [f a, g a]).getD (2 * m) 0 = f (l.getD m d) ∧
      (l.flatMap fun a => [f a, g a]).getD (2 * m + 1) 0 = g (l.getD m d)
  | [], m, _, h => absurd h (Nat.not_lt_zero _)
  | a :: l, 0, _, _ => by simp
  | a :: l, m + 1, d, h => by
    have ih := getD_flatMap_pair f g l m d (by simp at h; omega)
    simp only [List.flatMap_cons, List.getD_cons_succ]
    rw [show 2 * (m + 1) = 2 + 2 * m by ring, show 2 + 2 * m + 1 = 2 + (2 * m + 1) by ring]
    have e : ([f a, g a] : List ℕ).length = 2 := rfl
    rw [← e, getD_append_right', getD_append_right']
    exact ih

theorem length_vsOf (ψ : Formula) : (vsOf ψ).length = 2 * nA ψ := by
  unfold vsOf
  rw [← length_atoms ψ]
  induction atoms ψ with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]; ring

/-- The row variables of atom `m`. -/
theorem vsOf_getD (ψ : Formula) {m : ℕ} (hm : m < nA ψ) :
    (vsOf ψ).getD (2 * m) 0 = (apair ((atoms ψ).getD m dflt)).1 ∧
    (vsOf ψ).getD (2 * m + 1) 0 = (apair ((atoms ψ).getD m dflt)).2 :=
  getD_flatMap_pair _ _ (atoms ψ) m dflt (by rw [length_atoms]; exact hm)

theorem getD_mem {α : Type} {l : List α} {m : ℕ} {d : α} (h : m < l.length) : l.getD m d ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

/-- **The rows list exactly the variables.** -/
theorem vsOf_mem_freeVars (ψ : Formula) (hq : ψ.IsQF) (hn : ψ.NoSetVar)
    (hg : ∀ α ∈ atoms ψ, GoodAtom α) {r : ℕ} (hr : r < 2 * nA ψ) :
    (vsOf ψ).getD r 0 ∈ ψ.freeVars := by
  have hm : r / 2 < nA ψ := by omega
  have hα := getD_mem (d := dflt) (show r / 2 < (atoms ψ).length by rw [length_atoms]; exact hm)
  rw [mem_freeVars_atoms ψ hq hn]
  refine ⟨_, hα, (freeVars_goodAtom _ (hg _ hα) _).2 ?_⟩
  obtain ⟨h1, h2⟩ := vsOf_getD ψ hm
  rcases Nat.even_or_odd r with ⟨j, hj⟩ | ⟨j, hj⟩
  · left
    have e : (vsOf ψ).getD r 0 = (vsOf ψ).getD (2 * (r / 2)) 0 := by congr 1; omega
    rw [e, h1]
  · right
    have e : (vsOf ψ).getD r 0 = (vsOf ψ).getD (2 * (r / 2) + 1) 0 := by congr 1; omega
    rw [e, h2]

theorem freeVars_mem_vsOf (ψ : Formula) (hq : ψ.IsQF) (hn : ψ.NoSetVar)
    (hg : ∀ α ∈ atoms ψ, GoodAtom α) {v : ℕ} (hv : v ∈ ψ.freeVars) :
    ∃ r < 2 * nA ψ, (vsOf ψ).getD r 0 = v := by
  rw [mem_freeVars_atoms ψ hq hn] at hv
  obtain ⟨α, hα, hvα⟩ := hv
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hα
  have hm' : m < nA ψ := by rw [← length_atoms]; exact hm
  have hg' := (freeVars_goodAtom _ (hg _ hα) v).1 hvα
  obtain ⟨h1, h2⟩ := vsOf_getD ψ hm'
  rw [List.getD_eq_getElem _ _ hm] at h1 h2
  rcases hg' with h | h
  · exact ⟨2 * m, by omega, by rw [h1, h]⟩
  · exact ⟨2 * m + 1, by omega, by rw [h2, h]⟩

/-- A quantifier-free formula without the relation variable has an atom. -/
theorem nA_pos : ∀ (ψ : Formula), ψ.IsQF → ψ.NoSetVar → 1 ≤ nA ψ
  | .rel _ _, _, _ => le_rfl
  | .eq _ _, _, _ => le_rfl
  | .setVar _, _, hn => absurd hn id
  | .neg φ, hq, hn => nA_pos φ hq hn
  | .and φ _, hq, hn => by have := nA_pos φ hq.1 hn.1; simp [nA]; omega
  | .or φ _, hq, hn => by have := nA_pos φ hq.1 hn.1; simp [nA]; omega
  | .ex _ _, hq, _ => absurd hq id
  | .all _ _, hq, _ => absurd hq id

/-- Fitting atoms of arity at most two are good. -/
theorem goodAtom_of_fits (arities : List ℕ) (hpos : ∀ a ∈ arities, 1 ≤ a) :
    ∀ (ψ : Formula), ψ.IsQF → ψ.NoSetVar → ψ.Fits arities 0 → ψ.ArityAtMost 2 →
      ∀ α ∈ atoms ψ, GoodAtom α
  | .rel i xs, _, _, hf, ha, α, hα => by
    simp only [atoms, List.mem_singleton] at hα
    subst hα
    refine ⟨?_, ha⟩
    obtain ⟨hi, hl⟩ := hf
    rw [hl, List.getD_eq_getElem _ _ hi]
    exact hpos _ (List.getElem_mem hi)
  | .eq a b, _, _, _, _, α, hα => by
    simp only [atoms, List.mem_singleton] at hα
    subst hα; trivial
  | .setVar _, _, hn, _, _, _, _ => absurd hn id
  | .neg φ, hq, hn, hf, ha, α, hα => goodAtom_of_fits arities hpos φ hq hn hf ha α hα
  | .and φ ψ, hq, hn, hf, ha, α, hα => by
    simp only [atoms, List.mem_append] at hα
    rcases hα with h | h
    · exact goodAtom_of_fits arities hpos φ hq.1 hn.1 hf.1 ha.1 α h
    · exact goodAtom_of_fits arities hpos ψ hq.2 hn.2 hf.2 ha.2 α h
  | .or φ ψ, hq, hn, hf, ha, α, hα => by
    simp only [atoms, List.mem_append] at hα
    rcases hα with h | h
    · exact goodAtom_of_fits arities hpos φ hq.1 hn.1 hf.1 ha.1 α h
    · exact goodAtom_of_fits arities hpos ψ hq.2 hn.2 hf.2 ha.2 α h
  | .ex _ _, hq, _, _, _, _, _ => absurd hq id
  | .all _ _, hq, _, _, _, _, _ => absurd hq id

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.FormulaData
