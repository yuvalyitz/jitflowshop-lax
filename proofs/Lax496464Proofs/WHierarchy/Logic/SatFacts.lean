import Lax496464.WH_B3_LogicProblems
import Mathlib.Tactic.Ring

/-! Basic facts about satisfaction and the syntax of formulas: satisfaction depends only on the
free variables; quantifier blocks; the code, size, free variables and syntactic classes of a block
of quantifiers; model checking a sentence. -/

namespace Lax496464Proofs.WHierarchy.Logic.SatFacts

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems

@[simp] theorem update_same (ρ : Assignment) (x a : ℕ) : ρ.update x a x = a := by
  simp [Assignment.update]

theorem update_ne (ρ : Assignment) {x y : ℕ} (a : ℕ) (h : y ≠ x) : ρ.update x a y = ρ y := by
  simp [Assignment.update, h]

/-- **Satisfaction depends only on the free variables.** -/
theorem sat_congr (A : Structure) (S : Set (List ℕ)) :
    ∀ (φ : Formula) {ρ ρ' : Assignment}, (∀ v ∈ φ.freeVars, ρ v = ρ' v) →
      (Sat A S φ ρ ↔ Sat A S φ ρ')
  | .rel i xs, ρ, ρ', h => by
    have : xs.map ρ = xs.map ρ' := List.map_congr_left fun v hv =>
      h v (by simp [Formula.freeVars, hv])
    simp [Sat, this]
  | .setVar xs, ρ, ρ', h => by
    have : xs.map ρ = xs.map ρ' := List.map_congr_left fun v hv =>
      h v (by simp [Formula.freeVars, hv])
    simp [Sat, this]
  | .eq x y, ρ, ρ', h => by
    simp only [Sat, h x (by simp [Formula.freeVars]), h y (by simp [Formula.freeVars])]
  | .neg φ, ρ, ρ', h => by
    simp only [Sat, sat_congr A S φ fun v hv => h v (by simpa [Formula.freeVars] using hv)]
  | .and φ ψ, ρ, ρ', h => by
    simp only [Sat, sat_congr A S φ fun v hv => h v (by simp [Formula.freeVars, hv]),
      sat_congr A S ψ fun v hv => h v (by simp [Formula.freeVars, hv])]
  | .or φ ψ, ρ, ρ', h => by
    simp only [Sat, sat_congr A S φ fun v hv => h v (by simp [Formula.freeVars, hv]),
      sat_congr A S ψ fun v hv => h v (by simp [Formula.freeVars, hv])]
  | .ex x φ, ρ, ρ', h => by
    simp only [Sat]
    refine exists_congr fun a => and_congr_right fun _ => sat_congr A S φ fun v hv => ?_
    by_cases hvx : v = x
    · subst hvx; simp
    · rw [update_ne _ _ hvx, update_ne _ _ hvx]
      exact h v (by simp [Formula.freeVars, hv, hvx])
  | .all x φ, ρ, ρ', h => by
    simp only [Sat]
    refine forall_congr' fun a => imp_congr_right fun _ => sat_congr A S φ fun v hv => ?_
    by_cases hvx : v = x
    · subst hvx; simp
    · rw [update_ne _ _ hvx, update_ne _ _ hvx]
      exact h v (by simp [Formula.freeVars, hv, hvx])

/-- A sentence is true under one assignment exactly when it is true under any other. -/
theorem sat_sentence {A : Structure} {S : Set (List ℕ)} {φ : Formula} (h : IsSentence φ)
    (ρ ρ' : Assignment) : Sat A S φ ρ ↔ Sat A S φ ρ' :=
  sat_congr A S φ fun v hv => by rw [IsSentence] at h; simp [h] at hv

/-- The implication. -/
theorem sat_imp {A : Structure} {S : Set (List ℕ)} {φ ψ : Formula} {ρ : Assignment} :
    Sat A S (φ.imp ψ) ρ ↔ (Sat A S φ ρ → Sat A S ψ ρ) := by
  simp only [Formula.imp, Sat]
  tauto

/-! ### Blocks of quantifiers -/

@[simp] theorem exBlock_nil (φ : Formula) : Formula.exBlock [] φ = φ := by unfold Formula.exBlock; try rfl

@[simp] theorem exBlock_cons (x : ℕ) (xs : List ℕ) (φ : Formula) :
    Formula.exBlock (x :: xs) φ = .ex x (Formula.exBlock xs φ) := rfl

@[simp] theorem allBlock_nil (φ : Formula) : Formula.allBlock [] φ = φ := by unfold Formula.allBlock; try rfl

@[simp] theorem allBlock_cons (x : ℕ) (xs : List ℕ) (φ : Formula) :
    Formula.allBlock (x :: xs) φ = .all x (Formula.allBlock xs φ) := rfl

/-- **An existential block**: some values of the block's variables, in the universe, satisfy the
formula; the other variables keep their values. -/
theorem sat_exBlock {A : Structure} {S : Set (List ℕ)} (φ : Formula) :
    ∀ (xs : List ℕ) (ρ : Assignment), Sat A S (Formula.exBlock xs φ) ρ ↔
      ∃ ρ' : Assignment, (∀ v, v ∉ xs → ρ' v = ρ v) ∧ (∀ v ∈ xs, ρ' v < A.size) ∧
        Sat A S φ ρ'
  | [], ρ => by
    simp only [exBlock_nil, List.not_mem_nil, not_false_eq_true, forall_const, false_imp_iff,
      true_and]
    exact ⟨fun h => ⟨ρ, fun _ => rfl, h⟩, fun ⟨ρ', h1, h2⟩ => by
      rwa [show ρ' = ρ from funext h1] at h2⟩
  | x :: xs, ρ => by
    simp only [exBlock_cons, Sat, sat_exBlock φ xs]
    constructor
    · rintro ⟨a, ha, ρ', h1, h2, h3⟩
      refine ⟨ρ', fun v hv => ?_, fun v hv => ?_, h3⟩
      · simp only [List.mem_cons, not_or] at hv
        rw [h1 v hv.2, update_ne _ _ hv.1]
      · by_cases hvx : v ∈ xs
        · exact h2 v hvx
        · have hv' : v = x := by simpa [hvx] using hv
          rw [h1 v hvx, hv', update_same]; exact ha
    · rintro ⟨ρ', h1, h2, h3⟩
      refine ⟨ρ' x, h2 x (by simp), ρ', fun v hv => ?_, fun v hv => h2 v (by simp [hv]), h3⟩
      by_cases hvx : v = x
      · subst hvx; simp
      · rw [update_ne _ _ hvx]; exact h1 v (by simp [hv, hvx])

/-- **A universal block**: all values of the block's variables in the universe satisfy the
formula. -/
theorem sat_allBlock {A : Structure} {S : Set (List ℕ)} (φ : Formula) :
    ∀ (xs : List ℕ) (ρ : Assignment), Sat A S (Formula.allBlock xs φ) ρ ↔
      ∀ ρ' : Assignment, (∀ v, v ∉ xs → ρ' v = ρ v) → (∀ v ∈ xs, ρ' v < A.size) →
        Sat A S φ ρ'
  | [], ρ => by
    simp only [allBlock_nil, List.not_mem_nil, not_false_eq_true, forall_const, false_imp_iff]
    exact ⟨fun h ρ' h1 => by rwa [show ρ' = ρ from funext h1], fun h => h ρ fun _ => rfl⟩
  | x :: xs, ρ => by
    simp only [allBlock_cons, Sat, sat_allBlock φ xs]
    constructor
    · intro h ρ' h1 h2
      refine h (ρ' x) (h2 x (by simp)) ρ' (fun v hv => ?_) (fun v hv => h2 v (by simp [hv]))
      by_cases hvx : v = x
      · subst hvx; simp
      · rw [update_ne _ _ hvx]; exact h1 v (by simp [hv, hvx])
    · intro h a ha ρ' h1 h2
      refine h ρ' (fun v hv => ?_) (fun v hv => ?_)
      · simp only [List.mem_cons, not_or] at hv
        rw [h1 v hv.2, update_ne _ _ hv.1]
      · by_cases hvx : v ∈ xs
        · exact h2 v hvx
        · have hv' : v = x := by simpa [hvx] using hv
          rw [h1 v hvx, hv', update_same]; exact ha

/-- The free variables of an existential block. -/
theorem freeVars_exBlock (φ : Formula) :
    ∀ xs : List ℕ, (Formula.exBlock xs φ).freeVars = φ.freeVars \ xs.toFinset
  | [] => by simp
  | x :: xs => by
    rw [exBlock_cons, Formula.freeVars, freeVars_exBlock φ xs]
    ext v; simp [and_comm, and_assoc]

/-- The free variables of a universal block. -/
theorem freeVars_allBlock (φ : Formula) :
    ∀ xs : List ℕ, (Formula.allBlock xs φ).freeVars = φ.freeVars \ xs.toFinset
  | [] => by simp
  | x :: xs => by
    rw [allBlock_cons, Formula.freeVars, freeVars_allBlock φ xs]
    ext v; simp [and_comm, and_assoc]

/-- A block binding every free variable is a sentence. -/
theorem isSentence_exBlock {φ : Formula} {xs : List ℕ} (h : ∀ v ∈ φ.freeVars, v ∈ xs) :
    IsSentence (Formula.exBlock xs φ) := by
  unfold IsSentence
  rw [freeVars_exBlock]
  ext v; simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.notMem_empty, iff_false, not_and,
    not_not]
  exact h v

/-- The code of an existential block: `6, x` per variable, then the formula. -/
theorem encode_exBlock (φ : Formula) :
    ∀ xs : List ℕ, (Formula.exBlock xs φ).encode = xs.flatMap (fun x => [6, x]) ++ φ.encode
  | [] => by simp
  | x :: xs => by simp [Formula.encode, encode_exBlock φ xs]

theorem size_exBlock (φ : Formula) :
    ∀ xs : List ℕ, (Formula.exBlock xs φ).size = φ.size + 2 * xs.length
  | [] => by simp
  | x :: xs => by simp [Formula.size, size_exBlock φ xs]; ring

theorem fits_exBlock (arities : List ℕ) (s : ℕ) (φ : Formula) :
    ∀ xs : List ℕ, (Formula.exBlock xs φ).Fits arities s ↔ φ.Fits arities s
  | [] => Iff.rfl
  | _ :: xs => fits_exBlock arities s φ xs

theorem fits_allBlock (arities : List ℕ) (s : ℕ) (φ : Formula) :
    ∀ xs : List ℕ, (Formula.allBlock xs φ).Fits arities s ↔ φ.Fits arities s
  | [] => Iff.rfl
  | _ :: xs => fits_allBlock arities s φ xs

theorem noSetVar_exBlock (φ : Formula) :
    ∀ xs : List ℕ, (Formula.exBlock xs φ).NoSetVar ↔ φ.NoSetVar
  | [] => Iff.rfl
  | _ :: xs => noSetVar_exBlock φ xs

/-- An existential block in front of a quantifier-free formula is `Σ_1`. -/
theorem isSigma_one_exBlock {φ : Formula} (h : φ.IsQF) (xs : List ℕ) :
    IsSigma 1 (Formula.exBlock xs φ) := ⟨xs, φ, rfl, h⟩

/-! ### Model checking a sentence -/

/-- **A sentence is modelled** when it fits, does not use the relation variable, and holds under
any one assignment. -/
theorem models_iff_of_sentence {A : Structure} {φ : Formula} (h : IsSentence φ)
    (ρ : Assignment) : Models A φ ↔ φ.Fits A.arities 0 ∧ φ.NoSetVar ∧ Sat A ∅ φ ρ := by
  unfold Models
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun ⟨ρ', _, hs⟩ =>
    (sat_sentence h ρ' ρ).mp hs, fun hs => ⟨ρ, fun v hv => ?_, hs⟩⟩
  rw [IsSentence] at h; simp [h] at hv

end Lax496464Proofs.WHierarchy.Logic.SatFacts
