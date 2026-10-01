import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf
import Mathlib.GroupTheory.Perm.Basic

/-! # Isolated elements are interchangeable

An element of a structure is *active* if it occurs in a tuple of some relation. A permutation of the
numbers that fixes every active element is an automorphism of the structure: the literals of the CNF
hold under `ε` with `X := S` exactly when they hold under `π ∘ ε` with `X := π(S)` (`cnfHolds_perm`).

`exists_perm`: finitely many elements `E` of the universe can be moved into a set `U` of elements by a
permutation of the universe fixing a set `Fix`, as long as the elements of `E` outside `U` are not in
`Fix` and `U` has enough elements outside `Fix ∪ E` to receive them. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Perm

open Lax496464.WH_B1_Structures Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf

/-- The element occurs in a tuple of some relation. -/
def Active (A : Structure) (e : ℕ) : Prop := ∃ i, ∃ t ∈ A.rel i, e ∈ t

/-- The image of a relation under a permutation. -/
def imgS (π : Equiv.Perm ℕ) (S : Set (List ℕ)) : Set (List ℕ) := (fun t => t.map π) '' S

section
variable {A : Structure} {π : Equiv.Perm ℕ}

theorem fix_of_active (hπ : ∀ e, Active A e → π e = e) {e : ℕ} (h : Active A (π e)) :
    π e = e := π.injective (hπ _ h)

theorem map_fix_of_mem (hπ : ∀ e, Active A e → π e = e) {i : ℕ} {t : List ℕ}
    (ht : t ∈ A.rel i) : t.map π = t := by
  conv_rhs => rw [← List.map_id t]
  exact List.map_congr_left fun e he => hπ e ⟨i, t, ht, he⟩

theorem map_injective (π : Equiv.Perm ℕ) : Function.Injective (fun t : List ℕ => t.map π) :=
  List.map_injective_iff.mpr π.injective

theorem mem_imgS {S : Set (List ℕ)} {t : List ℕ} : t.map π ∈ imgS π S ↔ t ∈ S := by
  constructor
  · rintro ⟨u, hu, he⟩; rwa [← map_injective π he]
  · intro h; exact ⟨t, h, rfl⟩

/-- **A permutation fixing the active elements preserves the atoms.** -/
theorem atom_holds_perm (hπ : ∀ e, Active A e → π e = e) (S : Set (List ℕ)) (ε : ℕ → ℕ) :
    ∀ a : Atom, a.holds A S ε ↔ a.holds A (imgS π S) (π ∘ ε)
  | .rel i js => by
    simp only [Atom.holds]
    rw [← List.map_map]
    constructor
    · intro h; rw [map_fix_of_mem hπ h]; exact h
    · intro h
      have : (js.map ε).map π = js.map ε := by
        conv_rhs => rw [← List.map_id (js.map ε)]
        refine List.map_congr_left fun e he => ?_
        exact fix_of_active hπ ⟨i, _, h, List.mem_map_of_mem he⟩
      rwa [this] at h
  | .eq a b => by
    simp only [Atom.holds, Function.comp]
    exact ⟨fun h => by rw [h], fun h => π.injective h⟩
  | .setVar js => by
    simp only [Atom.holds]
    rw [← List.map_map, mem_imgS]

theorem cnfHolds_perm (hπ : ∀ e, Active A e → π e = e) (S : Set (List ℕ)) (ε : ℕ → ℕ)
    (F : List (List Lit)) : CnfHolds A S ε F ↔ CnfHolds A (imgS π S) (π ∘ ε) F := by
  unfold CnfHolds Lit.holds
  simp only [← atom_holds_perm hπ S ε]

/-- A permutation fixing the entries of the tuples of `S` fixes `S`. -/
theorem imgS_eq (S : Set (List ℕ)) (h : ∀ t ∈ S, ∀ e ∈ t, π e = e) : imgS π S = S := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u.map π = u := by
      conv_rhs => rw [← List.map_id u]
      exact List.map_congr_left fun e he => h u hu e he
    show u.map π ∈ S
    rw [this]; exact hu
  · intro ht
    refine ⟨t, ht, ?_⟩
    conv_rhs => rw [← List.map_id t]
    exact List.map_congr_left fun e he => h t ht e he

end

/-! ### Moving elements by swaps -/

/-- **Moving finitely many elements into `U`.** -/
theorem exists_perm (N : ℕ) (U Fix : Finset ℕ) (hU : ∀ u ∈ U, u < N) :
    ∀ (c : ℕ) (E : Finset ℕ), (E \ U).card = c → (∀ e ∈ E, e < N) →
      (∀ e ∈ E, e ∉ U → e ∉ Fix) → c ≤ ((U \ Fix) \ E).card →
      ∃ π : Equiv.Perm ℕ, (∀ e ∈ Fix, π e = e) ∧ (∀ e, π e < N ↔ e < N) ∧ ∀ e ∈ E, π e ∈ U
  | 0, E, hc, _, _, _ => by
    refine ⟨1, fun _ _ => rfl, fun _ => Iff.rfl, fun e he => ?_⟩
    have : E \ U = ∅ := Finset.card_eq_zero.mp hc
    by_contra hn
    have h2 : e ∈ E \ U := Finset.mem_sdiff.mpr ⟨he, hn⟩
    rw [this] at h2; simp at h2
  | c + 1, E, hc, hEN, hEF, hcard => by
    obtain ⟨e, he⟩ : (E \ U).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨f, hf⟩ : ((U \ Fix) \ E).Nonempty := Finset.card_pos.mp (by omega)
    simp only [Finset.mem_sdiff] at he hf
    obtain ⟨heE, heU⟩ := he
    obtain ⟨⟨hfU, hfF⟩, hfE⟩ := hf
    have heF : e ∉ Fix := hEF e heE heU
    have hef : e ≠ f := fun h => heU (h ▸ hfU)
    set σ := Equiv.swap e f with hσ
    set E' := E.image σ with hE'
    have hmemE' : ∀ x, x ∈ E' ↔ x = f ∨ (x ∈ E ∧ x ≠ e) := by
      intro x
      simp only [hE', Finset.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        by_cases hye : y = e
        · subst hye; left; simp [hσ]
        · have hyf : y ≠ f := fun h => hfE (h ▸ hy)
          right; rw [hσ, Equiv.swap_apply_of_ne_of_ne hye hyf]; exact ⟨hy, hye⟩
      · rintro (rfl | ⟨hx, hxe⟩)
        · exact ⟨e, heE, by simp [hσ]⟩
        · have hxf : x ≠ f := fun h => hfE (h ▸ hx)
          exact ⟨x, hx, by rw [hσ, Equiv.swap_apply_of_ne_of_ne hxe hxf]⟩
    have h1 : E' \ U = (E \ U).erase e := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, hmemE']
      constructor
      · rintro ⟨rfl | ⟨hx, hxe⟩, hxU⟩
        · exact absurd hfU hxU
        · exact ⟨hxe, hx, hxU⟩
      · rintro ⟨hxe, hx, hxU⟩; exact ⟨Or.inr ⟨hx, hxe⟩, hxU⟩
    have h2 : ((U \ Fix) \ E).erase f ⊆ (U \ Fix) \ E' := by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_sdiff] at hx ⊢
      obtain ⟨hxf, ⟨hxU, hxF⟩, hxE⟩ := hx
      refine ⟨⟨hxU, hxF⟩, fun h => ?_⟩
      rcases (hmemE' x).mp h with h | ⟨h, -⟩
      · exact hxf h
      · exact hxE h
    have hc' : (E' \ U).card = c := by
      rw [h1, Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨heE, heU⟩)]; omega
    have hcard' : c ≤ ((U \ Fix) \ E').card := by
      have := Finset.card_le_card h2
      rw [Finset.card_erase_of_mem (by simp [hfU, hfF, hfE])] at this
      omega
    have hEN' : ∀ x ∈ E', x < N := by
      intro x hx
      rcases (hmemE' x).mp hx with rfl | ⟨hx, -⟩
      · exact hU _ hfU
      · exact hEN x hx
    have hEF' : ∀ x ∈ E', x ∉ U → x ∉ Fix := by
      intro x hx hxU
      rcases (hmemE' x).mp hx with rfl | ⟨hx, -⟩
      · exact absurd hfU hxU
      · exact hEF x hx hxU
    obtain ⟨π', hfix, hN, hE⟩ := exists_perm N U Fix hU c E' hc' hEN' hEF' hcard'
    refine ⟨π' * σ, fun x hx => ?_, fun x => ?_, fun x hx => ?_⟩
    · have hxe : x ≠ e := fun h => heF (h ▸ hx)
      have hxf : x ≠ f := fun h => hfF (h ▸ hx)
      rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_of_ne_of_ne hxe hxf, hfix x hx]
    · rw [Equiv.Perm.mul_apply, hN]
      have heN : e < N := hEN e heE
      have hfN : f < N := hU f hfU
      rw [hσ]
      by_cases hxe : x = e
      · subst hxe; simp [heN, hfN]
      · by_cases hxf : x = f
        · subst hxf; simp [heN, hfN]
        · rw [Equiv.swap_apply_of_ne_of_ne hxe hxf]
    · rw [Equiv.Perm.mul_apply]
      exact hE _ (Finset.mem_image_of_mem σ hx)

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Perm
