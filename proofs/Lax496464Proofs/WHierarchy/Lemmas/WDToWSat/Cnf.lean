import Lax496464.WH_B3_LogicProblems
import Lax496464Proofs.WHierarchy.Logic.SatFacts

/-! # A conjunctive normal form of a quantifier-free formula

The atoms of a quantifier-free formula `ψ` whose variables lie in a list `vs` are renamed to the
positions of their variables in `vs`, and `ψ` is put into conjunctive normal form over these atoms
(`cnf vs ψ true`; `cnf vs ψ false` is a CNF of `¬ψ`). Under the assignment `ρ`, the CNF holds for the
positions' values `j ↦ ρ (vs[j])` exactly when `ψ` holds (`cnfHolds_iff`).

Also: the relation atoms and relation-variable arities of a formula (whether it fits a vocabulary is
decided by them, `fits_iff`), what the CNF's literals say about them, and the degenerate fact that a
formula without variables cannot fit a vocabulary of positive arities and a positive arity `s`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder

/-- An atom whose variables are positions `j` in the list of bound variables. -/
inductive Atom
  /-- `R_i` applied to the positions `js`. -/
  | rel (i : ℕ) (js : List ℕ)
  /-- The equation of two positions. -/
  | eq (a b : ℕ)
  /-- The relation variable applied to the positions `js`. -/
  | setVar (js : List ℕ)
  deriving DecidableEq

/-- A literal: an atom with a sign. -/
structure Lit where
  /-- `true` for the atom, `false` for its negation. -/
  pos : Bool
  /-- The atom. -/
  atom : Atom
  deriving DecidableEq

/-- The atom holds in `A` with `X := S`, the positions taking the values `ε`. -/
def Atom.holds (A : Structure) (S : Set (List ℕ)) (ε : ℕ → ℕ) : Atom → Prop
  | .rel i js => js.map ε ∈ A.rel i
  | .eq a b => ε a = ε b
  | .setVar js => js.map ε ∈ S

/-- The literal holds. -/
def Lit.holds (A : Structure) (S : Set (List ℕ)) (ε : ℕ → ℕ) (l : Lit) : Prop :=
  if l.pos then l.atom.holds A S ε else ¬ l.atom.holds A S ε

/-- A list of clauses holds: every clause has a literal that holds. -/
def CnfHolds (A : Structure) (S : Set (List ℕ)) (ε : ℕ → ℕ) (F : List (List Lit)) : Prop :=
  ∀ C ∈ F, ∃ l ∈ C, l.holds A S ε

/-- The clauses `C ++ D`, `C ∈ F`, `D ∈ G`: a CNF of the disjunction. -/
def prod (F G : List (List Lit)) : List (List Lit) := F.flatMap fun C => G.map fun D => C ++ D

/-- **The CNF** of `ψ` (polarity `true`) or of `¬ψ` (polarity `false`), variables renamed to their
positions in `vs`. Quantifiers do not occur in the formulas this is used on. -/
def cnf (vs : List ℕ) : Formula → Bool → List (List Lit)
  | .rel i xs, b => [[⟨b, .rel i (xs.map vs.idxOf)⟩]]
  | .setVar xs, b => [[⟨b, .setVar (xs.map vs.idxOf)⟩]]
  | .eq x y, b => [[⟨b, .eq (vs.idxOf x) (vs.idxOf y)⟩]]
  | .neg φ, b => cnf vs φ (!b)
  | .and φ ψ, true => cnf vs φ true ++ cnf vs ψ true
  | .and φ ψ, false => prod (cnf vs φ false) (cnf vs ψ false)
  | .or φ ψ, true => prod (cnf vs φ true) (cnf vs ψ true)
  | .or φ ψ, false => cnf vs φ false ++ cnf vs ψ false
  | .ex _ _, _ => [[]]
  | .all _ _, _ => [[]]

theorem cnfHolds_append {A : Structure} {S : Set (List ℕ)} {ε : ℕ → ℕ}
    (F G : List (List Lit)) : CnfHolds A S ε (F ++ G) ↔ CnfHolds A S ε F ∧ CnfHolds A S ε G := by
  unfold CnfHolds
  simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun C hC => h C (Or.inl hC), fun C hC => h C (Or.inr hC)⟩
  · rintro ⟨h1, h2⟩ C (hC | hC)
    · exact h1 C hC
    · exact h2 C hC

theorem cnfHolds_prod {A : Structure} {S : Set (List ℕ)} {ε : ℕ → ℕ}
    (F G : List (List Lit)) : CnfHolds A S ε (prod F G) ↔ CnfHolds A S ε F ∨ CnfHolds A S ε G := by
  unfold CnfHolds prod
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · intro h
    by_contra hn
    simp only [not_or, not_forall, not_exists, not_and] at hn
    obtain ⟨⟨C, hC, hC'⟩, ⟨D, hD, hD'⟩⟩ := hn
    obtain ⟨l, hl, hl'⟩ := h (C ++ D) ⟨C, hC, D, hD, rfl⟩
    rcases List.mem_append.mp hl with hl | hl
    · exact hC' l hl hl'
    · exact hD' l hl hl'
  · rintro (h | h) E ⟨C, hC, D, hD, rfl⟩
    · obtain ⟨l, hl, hl'⟩ := h C hC
      exact ⟨l, List.mem_append_left _ hl, hl'⟩
    · obtain ⟨l, hl, hl'⟩ := h D hD
      exact ⟨l, List.mem_append_right _ hl, hl'⟩

/-- A variable of `vs` is at its position. -/
theorem getD_idxOf {vs : List ℕ} {v : ℕ} (h : v ∈ vs) : vs.getD (vs.idxOf v) 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr h)]
  simp

/-- The values of the positions of an assignment. -/
def posVal (vs : List ℕ) (ρ : Assignment) : ℕ → ℕ := fun j => ρ (vs.getD j 0)

theorem map_idxOf {vs xs : List ℕ} (ρ : Assignment) (h : ∀ v ∈ xs, v ∈ vs) :
    (xs.map vs.idxOf).map (posVal vs ρ) = xs.map ρ := by
  rw [List.map_map]
  exact List.map_congr_left fun v hv => by simp only [Function.comp, posVal, getD_idxOf (h v hv)]

/-- **The CNF is correct**: for a quantifier-free `ψ` with variables in `vs`, the CNF of polarity `b`
holds for the positions' values exactly when `ψ` has truth value `b`. -/
theorem cnfHolds_iff (A : Structure) (S : Set (List ℕ)) (vs : List ℕ) (ρ : Assignment) :
    ∀ (ψ : Formula) (b : Bool), ψ.IsQF → (∀ v ∈ ψ.freeVars, v ∈ vs) →
      (CnfHolds A S (posVal vs ρ) (cnf vs ψ b) ↔ (Sat A S ψ ρ ↔ b = true))
  | .rel i xs, b, _, hv => by
    have hm := map_idxOf ρ (vs := vs) (xs := xs) fun v h => hv v (by simp [Formula.freeVars, h])
    cases b <;> simp [cnf, CnfHolds, Lit.holds, Atom.holds, Sat, hm]
  | .setVar xs, b, _, hv => by
    have hm := map_idxOf ρ (vs := vs) (xs := xs) fun v h => hv v (by simp [Formula.freeVars, h])
    cases b <;> simp [cnf, CnfHolds, Lit.holds, Atom.holds, Sat, hm]
  | .eq x y, b, _, hv => by
    have hx : posVal vs ρ (vs.idxOf x) = ρ x := by
      simp only [posVal, getD_idxOf (hv x (by simp [Formula.freeVars]))]
    have hy : posVal vs ρ (vs.idxOf y) = ρ y := by
      simp only [posVal, getD_idxOf (hv y (by simp [Formula.freeVars]))]
    cases b <;> simp [cnf, CnfHolds, Lit.holds, Atom.holds, Sat, hx, hy]
  | .neg φ, b, hq, hv => by
    rw [cnf, cnfHolds_iff A S vs ρ φ (!b) hq fun v h => hv v (by simpa [Formula.freeVars] using h)]
    cases b <;> simp [Sat]
  | .and φ ψ, b, hq, hv => by
    have h1 := cnfHolds_iff A S vs ρ φ b hq.1 fun v h => hv v (by simp [Formula.freeVars, h])
    have h2 := cnfHolds_iff A S vs ρ ψ b hq.2 fun v h => hv v (by simp [Formula.freeVars, h])
    cases b
    · rw [cnf, cnfHolds_prod, h1, h2]; simp [Sat]; tauto
    · rw [cnf, cnfHolds_append, h1, h2]; simp [Sat]
  | .or φ ψ, b, hq, hv => by
    have h1 := cnfHolds_iff A S vs ρ φ b hq.1 fun v h => hv v (by simp [Formula.freeVars, h])
    have h2 := cnfHolds_iff A S vs ρ ψ b hq.2 fun v h => hv v (by simp [Formula.freeVars, h])
    cases b
    · rw [cnf, cnfHolds_append, h1, h2]; simp [Sat]
    · rw [cnf, cnfHolds_prod, h1, h2]; simp [Sat]
  | .ex _ _, _, hq, _ => absurd hq (by simp [Formula.IsQF])
  | .all _ _, _, hq, _ => absurd hq (by simp [Formula.IsQF])

/-! ### The positions of the atoms -/

/-- The positions an atom mentions. -/
def Atom.idxs : Atom → List ℕ
  | .rel _ js => js
  | .eq a b => [a, b]
  | .setVar js => js

/-- An atom holds or not according to the values of its positions only. -/
theorem Atom.holds_congr {A : Structure} {S : Set (List ℕ)} {ε ε' : ℕ → ℕ} :
    ∀ (a : Atom), (∀ j ∈ a.idxs, ε j = ε' j) → (a.holds A S ε ↔ a.holds A S ε')
  | .rel i js, h => by
    simp only [Atom.holds]; rw [List.map_congr_left (l := js) fun j hj => h j hj]
  | .eq a b, h => by
    simp only [Atom.holds, h a (by simp [Atom.idxs]), h b (by simp [Atom.idxs])]
  | .setVar js, h => by
    simp only [Atom.holds]; rw [List.map_congr_left (l := js) fun j hj => h j hj]

theorem Lit.holds_congr {A : Structure} {S : Set (List ℕ)} {ε ε' : ℕ → ℕ} (l : Lit)
    (h : ∀ j ∈ l.atom.idxs, ε j = ε' j) : l.holds A S ε ↔ l.holds A S ε' := by
  unfold Lit.holds; rw [Atom.holds_congr l.atom h]

theorem cnfHolds_congr {A : Structure} {S : Set (List ℕ)} {ε ε' : ℕ → ℕ} {F : List (List Lit)}
    (h : ∀ C ∈ F, ∀ l ∈ C, ∀ j ∈ l.atom.idxs, ε j = ε' j) :
    CnfHolds A S ε F ↔ CnfHolds A S ε' F := by
  unfold CnfHolds
  exact forall₂_congr fun C hC => exists_congr fun l => and_congr_right fun hl =>
    Lit.holds_congr l (h C hC l hl)

theorem mem_prod {F G : List (List Lit)} {E : List Lit} :
    E ∈ prod F G ↔ ∃ C ∈ F, ∃ D ∈ G, E = C ++ D := by
  unfold prod
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨C, hC, D, hD, rfl⟩; exact ⟨C, hC, D, hD, rfl⟩
  · rintro ⟨C, hC, D, hD, rfl⟩; exact ⟨C, hC, D, hD, rfl⟩

/-- The atomic subformulas. -/
def atoms : Formula → List Formula
  | .rel i xs => [.rel i xs]
  | .setVar xs => [.setVar xs]
  | .eq x y => [.eq x y]
  | .neg φ => atoms φ
  | .and φ ψ => atoms φ ++ atoms ψ
  | .or φ ψ => atoms φ ++ atoms ψ
  | .ex _ φ => atoms φ
  | .all _ φ => atoms φ

/-- The renamed atom of an atomic formula. -/
def renameAtom (vs : List ℕ) : Formula → Atom
  | .rel i xs => .rel i (xs.map vs.idxOf)
  | .setVar xs => .setVar (xs.map vs.idxOf)
  | .eq x y => .eq (vs.idxOf x) (vs.idxOf y)
  | _ => .eq 0 0

/-- **Every literal of the CNF is a renamed atom of the formula.** -/
theorem mem_cnf (vs : List ℕ) : ∀ (ψ : Formula) (b : Bool), ψ.IsQF →
    ∀ C ∈ cnf vs ψ b, ∀ l ∈ C, ∃ a ∈ atoms ψ, l.atom = renameAtom vs a
  | .rel i xs, b, _, C, hC, l, hl => by
    simp only [cnf, List.mem_singleton] at hC; subst hC
    simp only [List.mem_singleton] at hl; subst hl
    exact ⟨.rel i xs, by simp [atoms], rfl⟩
  | .setVar xs, b, _, C, hC, l, hl => by
    simp only [cnf, List.mem_singleton] at hC; subst hC
    simp only [List.mem_singleton] at hl; subst hl
    exact ⟨.setVar xs, by simp [atoms], rfl⟩
  | .eq x y, b, _, C, hC, l, hl => by
    simp only [cnf, List.mem_singleton] at hC; subst hC
    simp only [List.mem_singleton] at hl; subst hl
    exact ⟨.eq x y, by simp [atoms], rfl⟩
  | .neg φ, b, hq, C, hC, l, hl => by
    obtain ⟨a, ha, h⟩ := mem_cnf vs φ (!b) hq C hC l hl
    exact ⟨a, by simpa [atoms] using ha, h⟩
  | .and φ ψ, b, hq, C, hC, l, hl => by
    cases b
    · simp only [cnf] at hC
      obtain ⟨C1, h1, C2, h2, rfl⟩ := mem_prod.mp hC
      rcases List.mem_append.mp hl with hl | hl
      · obtain ⟨a, ha, h⟩ := mem_cnf vs φ false hq.1 C1 h1 l hl
        exact ⟨a, by simp [atoms, ha], h⟩
      · obtain ⟨a, ha, h⟩ := mem_cnf vs ψ false hq.2 C2 h2 l hl
        exact ⟨a, by simp [atoms, ha], h⟩
    · simp only [cnf] at hC
      rcases List.mem_append.mp hC with hC | hC
      · obtain ⟨a, ha, h⟩ := mem_cnf vs φ true hq.1 C hC l hl
        exact ⟨a, by simp [atoms, ha], h⟩
      · obtain ⟨a, ha, h⟩ := mem_cnf vs ψ true hq.2 C hC l hl
        exact ⟨a, by simp [atoms, ha], h⟩
  | .or φ ψ, b, hq, C, hC, l, hl => by
    cases b
    · simp only [cnf] at hC
      rcases List.mem_append.mp hC with hC | hC
      · obtain ⟨a, ha, h⟩ := mem_cnf vs φ false hq.1 C hC l hl
        exact ⟨a, by simp [atoms, ha], h⟩
      · obtain ⟨a, ha, h⟩ := mem_cnf vs ψ false hq.2 C hC l hl
        exact ⟨a, by simp [atoms, ha], h⟩
    · simp only [cnf] at hC
      obtain ⟨C1, h1, C2, h2, rfl⟩ := mem_prod.mp hC
      rcases List.mem_append.mp hl with hl | hl
      · obtain ⟨a, ha, h⟩ := mem_cnf vs φ true hq.1 C1 h1 l hl
        exact ⟨a, by simp [atoms, ha], h⟩
      · obtain ⟨a, ha, h⟩ := mem_cnf vs ψ true hq.2 C2 h2 l hl
        exact ⟨a, by simp [atoms, ha], h⟩
  | .ex _ _, _, hq, _, _, _, _ => absurd hq (by simp [Formula.IsQF])
  | .all _ _, _, hq, _, _, _, _ => absurd hq (by simp [Formula.IsQF])

/-- The free variables of the atoms are free variables of the formula. -/
theorem freeVars_of_mem_atoms : ∀ (ψ : Formula), ψ.IsQF → ∀ a ∈ atoms ψ, ∀ v ∈ a.freeVars,
    v ∈ ψ.freeVars
  | .rel i xs, _, a, ha, v, hv => by simp only [atoms, List.mem_singleton] at ha; subst ha; exact hv
  | .setVar xs, _, a, ha, v, hv => by
    simp only [atoms, List.mem_singleton] at ha; subst ha; exact hv
  | .eq x y, _, a, ha, v, hv => by simp only [atoms, List.mem_singleton] at ha; subst ha; exact hv
  | .neg φ, hq, a, ha, v, hv => by
    simpa [Formula.freeVars] using freeVars_of_mem_atoms φ hq a (by simpa [atoms] using ha) v hv
  | .and φ ψ, hq, a, ha, v, hv => by
    simp only [atoms, List.mem_append] at ha
    rcases ha with ha | ha
    · simp [Formula.freeVars, freeVars_of_mem_atoms φ hq.1 a ha v hv]
    · simp [Formula.freeVars, freeVars_of_mem_atoms ψ hq.2 a ha v hv]
  | .or φ ψ, hq, a, ha, v, hv => by
    simp only [atoms, List.mem_append] at ha
    rcases ha with ha | ha
    · simp [Formula.freeVars, freeVars_of_mem_atoms φ hq.1 a ha v hv]
    · simp [Formula.freeVars, freeVars_of_mem_atoms ψ hq.2 a ha v hv]
  | .ex _ _, hq, _, _, _, _ => absurd hq (by simp [Formula.IsQF])
  | .all _ _, hq, _, _, _, _ => absurd hq (by simp [Formula.IsQF])

/-- The atoms of a quantifier-free formula are atomic. -/
theorem isAtom_of_mem_atoms : ∀ (ψ : Formula), ∀ a ∈ atoms ψ,
    (∃ i xs, a = .rel i xs) ∨ (∃ xs, a = .setVar xs) ∨ (∃ x y, a = .eq x y)
  | .rel i xs, a, ha => by simp only [atoms, List.mem_singleton] at ha; subst ha; simp
  | .setVar xs, a, ha => by simp only [atoms, List.mem_singleton] at ha; subst ha; simp
  | .eq x y, a, ha => by simp only [atoms, List.mem_singleton] at ha; subst ha; simp
  | .neg φ, a, ha => isAtom_of_mem_atoms φ a (by simpa [atoms] using ha)
  | .and φ ψ, a, ha => by
    simp only [atoms, List.mem_append] at ha
    rcases ha with ha | ha
    · exact isAtom_of_mem_atoms φ a ha
    · exact isAtom_of_mem_atoms ψ a ha
  | .or φ ψ, a, ha => by
    simp only [atoms, List.mem_append] at ha
    rcases ha with ha | ha
    · exact isAtom_of_mem_atoms φ a ha
    · exact isAtom_of_mem_atoms ψ a ha
  | .ex _ φ, a, ha => isAtom_of_mem_atoms φ a (by simpa [atoms] using ha)
  | .all _ φ, a, ha => isAtom_of_mem_atoms φ a (by simpa [atoms] using ha)

/-- **A formula fits a vocabulary exactly when its atoms do.** -/
theorem fits_iff_atoms (ar : List ℕ) (s : ℕ) : ∀ ψ : Formula,
    ψ.Fits ar s ↔ ∀ a ∈ atoms ψ, a.Fits ar s
  | .rel i xs => by simp [atoms]
  | .setVar xs => by simp [atoms]
  | .eq x y => by simp [atoms]
  | .neg φ => by simp only [Formula.Fits, atoms]; exact fits_iff_atoms ar s φ
  | .and φ ψ => by
    simp only [Formula.Fits, atoms, List.mem_append, fits_iff_atoms ar s φ,
      fits_iff_atoms ar s ψ]
    constructor
    · rintro ⟨h1, h2⟩ a (ha | ha)
      · exact h1 a ha
      · exact h2 a ha
    · intro h; exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  | .or φ ψ => by
    simp only [Formula.Fits, atoms, List.mem_append, fits_iff_atoms ar s φ,
      fits_iff_atoms ar s ψ]
    constructor
    · rintro ⟨h1, h2⟩ a (ha | ha)
      · exact h1 a ha
      · exact h2 a ha
    · intro h; exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  | .ex _ φ => by simp only [Formula.Fits, atoms]; exact fits_iff_atoms ar s φ
  | .all _ φ => by simp only [Formula.Fits, atoms]; exact fits_iff_atoms ar s φ

/-- **The degenerate case.** A quantifier-free formula without variables does not fit a vocabulary
of positive arities with a positive arity of the relation variable: it has an atom, and every atom
has a variable. -/
theorem not_fits_of_noVars (ar : List ℕ) (har : ∀ a ∈ ar, 1 ≤ a) {s : ℕ} (hs : 1 ≤ s) :
    ∀ ψ : Formula, ψ.IsQF → ψ.freeVars = ∅ → ¬ ψ.Fits ar s
  | .rel i xs, _, hv, hf => by
    simp only [Formula.freeVars, List.toFinset_eq_empty_iff] at hv
    subst hv
    obtain ⟨hi, hl⟩ := hf
    have := har (ar.getD i 0) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi)
    rw [List.length_nil] at hl; omega
  | .setVar xs, _, hv, hf => by
    simp only [Formula.freeVars, List.toFinset_eq_empty_iff] at hv
    subst hv
    simp [Formula.Fits] at hf; omega
  | .eq x y, _, hv, _ => by simp [Formula.freeVars] at hv
  | .neg φ, hq, hv, hf => not_fits_of_noVars ar har hs φ hq hv hf
  | .and φ ψ, hq, hv, hf => by
    simp only [Formula.freeVars, Finset.union_eq_empty] at hv
    exact not_fits_of_noVars ar har hs φ hq.1 hv.1 hf.1
  | .or φ ψ, hq, hv, hf => by
    simp only [Formula.freeVars, Finset.union_eq_empty] at hv
    exact not_fits_of_noVars ar har hs φ hq.1 hv.1 hf.1
  | .ex _ _, hq, _, _ => absurd hq (by simp [Formula.IsQF])
  | .all _ _, hq, _, _ => absurd hq (by simp [Formula.IsQF])

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf
