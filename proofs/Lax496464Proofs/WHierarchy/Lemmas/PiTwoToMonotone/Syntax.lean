import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
import Lax496464Proofs.WHierarchy.Logic.SatFacts

/-! # The syntax of the fixed formula

`φ = ∀ xs ∃ ys ψ` with `ψ` quantifier-free. The bound variables are numbered by *positions*: the
list `vs = ys' ++ xs'` of the distinct variables of `ys`, then those of `xs`; the first
`q = |ys'|` positions are existential, the other `p = |xs'|` universal. `ψ` is renamed to positions
(`rename`), which changes satisfaction only by composing the assignment (`sat_rename`).

The fixed data of the reduction (`Data`), the atoms of a formula, and the fit test on a word
(`fitW`, `fitW_iff`) as in `Lemmas/WDToWSat/Output`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word

/-! ### Renaming the variables -/

/-- Rename every variable by `f`. -/
def rename (f : ℕ → ℕ) : Formula → Formula
  | .rel i xs => .rel i (xs.map f)
  | .setVar xs => .setVar (xs.map f)
  | .eq a b => .eq (f a) (f b)
  | .neg φ => .neg (rename f φ)
  | .and φ ψ => .and (rename f φ) (rename f ψ)
  | .or φ ψ => .or (rename f φ) (rename f ψ)
  | .ex x φ => .ex (f x) (rename f φ)
  | .all x φ => .all (f x) (rename f φ)

theorem isQF_rename (f : ℕ → ℕ) : ∀ ψ : Formula, ψ.IsQF → (rename f ψ).IsQF
  | .rel _ _, _ => trivial
  | .setVar _, _ => trivial
  | .eq _ _, _ => trivial
  | .neg φ, h => isQF_rename f φ h
  | .and φ ψ, h => ⟨isQF_rename f φ h.1, isQF_rename f ψ h.2⟩
  | .or φ ψ, h => ⟨isQF_rename f φ h.1, isQF_rename f ψ h.2⟩
  | .ex _ _, h => absurd h (by simp [Formula.IsQF])
  | .all _ _, h => absurd h (by simp [Formula.IsQF])

/-- **Renaming** a quantifier-free formula composes the assignment. -/
theorem sat_rename (A : Structure) (S : Set (List ℕ)) (f : ℕ → ℕ) (ε : ℕ → ℕ) :
    ∀ ψ : Formula, ψ.IsQF → (Sat A S (rename f ψ) ε ↔ Sat A S ψ (ε ∘ f))
  | .rel i xs, _ => by simp [rename, Sat, List.map_map]
  | .setVar xs, _ => by simp [rename, Sat, List.map_map]
  | .eq a b, _ => by simp [rename, Sat]
  | .neg φ, h => by simp only [rename, Sat]; rw [sat_rename A S f ε φ h]
  | .and φ ψ, h => by
    simp only [rename, Sat]; rw [sat_rename A S f ε φ h.1, sat_rename A S f ε ψ h.2]
  | .or φ ψ, h => by
    simp only [rename, Sat]; rw [sat_rename A S f ε φ h.1, sat_rename A S f ε ψ h.2]
  | .ex _ _, h => absurd h (by simp [Formula.IsQF])
  | .all _ _, h => absurd h (by simp [Formula.IsQF])

/-! ### Atoms -/

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

/-- The argument lists of the `X`-atoms. -/
def xatoms : Formula → List (List ℕ)
  | .setVar xs => [xs]
  | .neg φ => xatoms φ
  | .and φ ψ => xatoms φ ++ xatoms ψ
  | .or φ ψ => xatoms φ ++ xatoms ψ
  | .ex _ φ => xatoms φ
  | .all _ φ => xatoms φ
  | _ => []

theorem mem_atoms_of_xatoms : ∀ (ψ : Formula) (js : List ℕ), js ∈ xatoms ψ → .setVar js ∈ atoms ψ
  | .rel _ _, js, h => by simp [xatoms] at h
  | .eq _ _, js, h => by simp [xatoms] at h
  | .setVar xs, js, h => by simp [xatoms] at h; simp [atoms, h]
  | .neg φ, js, h => mem_atoms_of_xatoms φ js h
  | .and φ ψ, js, h => by
    simp only [xatoms, List.mem_append] at h; simp only [atoms, List.mem_append]
    rcases h with h | h
    · exact Or.inl (mem_atoms_of_xatoms φ js h)
    · exact Or.inr (mem_atoms_of_xatoms ψ js h)
  | .or φ ψ, js, h => by
    simp only [xatoms, List.mem_append] at h; simp only [atoms, List.mem_append]
    rcases h with h | h
    · exact Or.inl (mem_atoms_of_xatoms φ js h)
    · exact Or.inr (mem_atoms_of_xatoms ψ js h)
  | .ex _ φ, js, h => mem_atoms_of_xatoms φ js h
  | .all _ φ, js, h => mem_atoms_of_xatoms φ js h

theorem xatoms_rename (f : ℕ → ℕ) : ∀ ψ : Formula, xatoms (rename f ψ) = (xatoms ψ).map (List.map f)
  | .rel _ _ => rfl
  | .setVar _ => rfl
  | .eq _ _ => rfl
  | .neg φ => xatoms_rename f φ
  | .and φ ψ => by simp [rename, xatoms, xatoms_rename f φ, xatoms_rename f ψ]
  | .or φ ψ => by simp [rename, xatoms, xatoms_rename f φ, xatoms_rename f ψ]
  | .ex _ φ => xatoms_rename f φ
  | .all _ φ => xatoms_rename f φ

theorem atoms_rename (f : ℕ → ℕ) : ∀ ψ : Formula, atoms (rename f ψ) = (atoms ψ).map (rename f)
  | .rel _ _ => rfl
  | .setVar _ => rfl
  | .eq _ _ => rfl
  | .neg φ => atoms_rename f φ
  | .and φ ψ => by simp [rename, atoms, atoms_rename f φ, atoms_rename f ψ]
  | .or φ ψ => by simp [rename, atoms, atoms_rename f φ, atoms_rename f ψ]
  | .ex _ φ => atoms_rename f φ
  | .all _ φ => atoms_rename f φ

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

/-- The atoms are atomic. -/
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

/-! ### Positions -/

/-- The positions: the distinct variables of `ys`, then those of `xs`. A variable of both is found
at its position in `ys` (`List.idxOf` finds the first), the existential binding shadowing the
universal one; its universal position is unused, but kept so that the universal block is
nonempty whenever `xs` is (which matters over the empty universe). -/
def posList (xs ys : List ℕ) : List ℕ := ys.dedup ++ xs.dedup

/-! ### The data of the reduction -/

/-- The fixed data of the reduction. -/
structure Data where
  /-- The arity of `X`. -/
  s : ℕ
  /-- The number of existential positions. -/
  q : ℕ
  /-- The number of universal positions. -/
  p : ℕ
  /-- The quantifier-free part, on positions. -/
  ψ : Formula
  /-- The relation atoms, as symbol and number of arguments. -/
  rels : List (ℕ × ℕ)
  /-- Every `X`-atom has arity `s`. -/
  sfit : Bool
  /-- The number of slots of a block. -/
  D : ℕ

/-- The relation atom of an atomic formula. -/
def relPair : Formula → Option (ℕ × ℕ)
  | .rel i ys => some (i, ys.length)
  | _ => none

/-- An `X`-atom has arity `s`. -/
def setOk (s : ℕ) : Formula → Bool
  | .setVar ys => ys.length == s
  | _ => true

/-- **The data of `∀ xs ∃ ys ψ`** with `X` of arity `s`. -/
def dataOf (xs ys : List ℕ) (ψ : Formula) (s : ℕ) : Data where
  s := s
  q := ys.dedup.length
  p := xs.dedup.length
  ψ := rename (posList xs ys).idxOf ψ
  rels := (atoms ψ).filterMap relPair
  sfit := (atoms ψ).all (setOk s)
  D := 2 * (xatoms ψ).length + 2

/-- The number of positions. -/
abbrev Data.r (D : Data) : ℕ := D.q + D.p

/-- The vocabulary of the word fits the relation atoms, and the `X`-atoms have arity `s`. -/
def fitW (D : Data) (x : List ℕ) : Prop :=
  D.sfit = true ∧ ∀ p ∈ D.rels, p.1 < spW x ∧ x.getD (1 + p.1) 0 = p.2

instance (D : Data) (x : List ℕ) : Decidable (fitW D x) := by unfold fitW; infer_instance

/-- **The fit test of the word is the fit of the formula.** -/
theorem fitW_iff {x : List ℕ} {A : Structure} {k : ℕ} {bl : List (List ℕ)} (he : Enc x A k bl)
    (xs ys : List ℕ) (ψ : Formula) (s : ℕ) :
    fitW (dataOf xs ys ψ s) x ↔ ψ.Fits A.arities s := by
  rw [fits_iff_atoms]
  unfold fitW dataOf
  simp only [List.all_eq_true, List.mem_filterMap, he.spW_eq]
  constructor
  · rintro ⟨hs, hr⟩ a ha
    rcases isAtom_of_mem_atoms ψ a ha with ⟨i, ys, rfl⟩ | ⟨ys, rfl⟩ | ⟨u, v, rfl⟩
    · obtain ⟨h1, h2⟩ := hr (i, ys.length) ⟨_, ha, rfl⟩
      have h2' : x.getD (1 + i) 0 = ys.length := h2
      rw [he.arity h1] at h2'
      exact ⟨h1, h2'.symm⟩
    · have := hs _ ha
      simpa [setOk, Formula.Fits] using this
    · trivial
  · intro h
    refine ⟨fun a ha => ?_, ?_⟩
    · rcases isAtom_of_mem_atoms ψ a ha with ⟨i, ys, rfl⟩ | ⟨ys, rfl⟩ | ⟨u, v, rfl⟩
      · rfl
      · have := h _ ha
        simpa [setOk, Formula.Fits] using this
      · rfl
    · rintro ⟨i, l⟩ ⟨a, ha, hp⟩
      rcases isAtom_of_mem_atoms ψ a ha with ⟨i', ys, rfl⟩ | ⟨ys, rfl⟩ | ⟨u, v, rfl⟩
      · simp only [relPair, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        obtain ⟨h1, h2⟩ := h _ ha
        exact ⟨h1, by rw [he.arity h1, h2]⟩
      · simp [relPair] at hp
      · simp [relPair] at hp

/-- The fit of the renamed formula, atom by atom: relation atoms have the arity of their symbol,
`X`-atoms arity `s`. -/
theorem atom_facts {xs ys : List ℕ} {ψ : Formula} {s : ℕ} {ar : List ℕ} (hf : ψ.Fits ar s) :
    ∀ a ∈ atoms (dataOf xs ys ψ s).ψ, a.Fits ar s := by
  intro a ha
  simp only [dataOf, atoms_rename, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hbf := (fits_iff_atoms ar s ψ).mp hf b hb
  rcases isAtom_of_mem_atoms ψ b hb with ⟨i, zs, rfl⟩ | ⟨zs, rfl⟩ | ⟨u, v, rfl⟩
  · simpa [rename, Formula.Fits] using hbf
  · simpa [rename, Formula.Fits] using hbf
  · trivial

/-- The positions of the renamed formula are below `r`. -/
theorem pos_lt {xs ys : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF)
    (hv : ∀ v ∈ ψ.freeVars, v ∈ xs ∨ v ∈ ys) :
    ∀ a ∈ atoms (dataOf xs ys ψ s).ψ, ∀ j ∈ a.freeVars, j < (dataOf xs ys ψ s).r := by
  intro a ha j hj
  simp only [dataOf, atoms_rename, List.mem_map] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  have hlen : (posList xs ys).length = (dataOf xs ys ψ s).r := by
    simp [posList, dataOf, Data.r]
  have key : ∀ v ∈ b.freeVars, (posList xs ys).idxOf v < (dataOf xs ys ψ s).r := by
    intro v hvb
    rw [← hlen]
    refine List.idxOf_lt_length_iff.mpr ?_
    rcases hv v (freeVars_of_mem_atoms ψ hq b hb v hvb) with h | h
    · exact List.mem_append_right _ (List.mem_dedup.mpr h)
    · exact List.mem_append_left _ (List.mem_dedup.mpr h)
  rcases isAtom_of_mem_atoms ψ b hb with ⟨i, zs, rfl⟩ | ⟨zs, rfl⟩ | ⟨u, v, rfl⟩
  · simp only [rename, Formula.freeVars, List.mem_toFinset, List.mem_map] at hj
    obtain ⟨v, hv', rfl⟩ := hj
    exact key v (by simp [Formula.freeVars, hv'])
  · simp only [rename, Formula.freeVars, List.mem_toFinset, List.mem_map] at hj
    obtain ⟨v, hv', rfl⟩ := hj
    exact key v (by simp [Formula.freeVars, hv'])
  · simp only [rename, Formula.freeVars, Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact key u (by simp [Formula.freeVars])
    · exact key v (by simp [Formula.freeVars])

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax
