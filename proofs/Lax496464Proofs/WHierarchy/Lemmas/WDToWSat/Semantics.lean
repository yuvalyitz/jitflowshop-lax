import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output

/-! # Witnesses among the elements of `U`

For `φ = ∀ xs ψ` with `ψ` quantifier-free and every variable of `ψ` in `xs`:

* `sat_iff_cnf`: `A ⊨ φ(S)` iff the CNF holds for every assignment `ε` of universe elements to the
  positions `0, …, r-1`;
* `witness_iff`: a witness of weight `k` exists iff one exists whose tuples use only elements of
  `U` and for which the CNF holds for every assignment of elements of `U` (`UWit`). The elements
  outside `U` are isolated and, as `U` contains `|x| + s·k + r` elements (or all of them), they can be
  swapped into `U` (`Perm.exists_perm`, `Perm.cnfHolds_perm`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Semantics

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Perm
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output

/-- A witness among the elements of `U`. -/
def UWit (A : Structure) (D : Data) (x : List ℕ) (k : ℕ) : Prop :=
  ∃ S : Finset (List ℕ), S.card = k ∧ (∀ t ∈ S, t.length = D.s ∧ ∀ a ∈ t, a ∈ U D x) ∧
    ∀ ε : ℕ → ℕ, (∀ j < D.r, ε j ∈ U D x) → CnfHolds A ↑S ε D.cnf

/-- **Moving elements: the count.** -/
theorem card_move (U Fix E : Finset ℕ) (L : ℕ) (hL : ∀ e < L, e ∈ U)
    (h : (∀ e ∈ E, e ∈ U) ∨ Fix.card + E.card ≤ L) :
    (E \ U).card ≤ ((U \ Fix) \ E).card := by
  rcases h with h | h
  · have : E \ U = ∅ := by
      ext e; simp only [Finset.mem_sdiff, Finset.notMem_empty, iff_false, not_and, not_not]
      exact h e
    rw [this]; simp
  · set rL := Finset.range L
    have h1 : (E \ U).card ≤ (E \ rL).card :=
      Finset.card_le_card (Finset.sdiff_subset_sdiff le_rfl fun e he => hL e (by simpa [rL] using he))
    have h2 := Finset.card_sdiff_add_card_inter E rL
    have h3 : rL \ (Fix ∪ (E ∩ rL)) ⊆ (U \ Fix) \ E := by
      intro e he
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, not_or, not_and, rL,
        Finset.mem_range] at he ⊢
      exact ⟨⟨hL e he.1, he.2.1⟩, fun hE => he.2.2 hE he.1⟩
    have h4 := Finset.le_card_sdiff (Fix ∪ (E ∩ rL)) rL
    have h5 := Finset.card_union_le Fix (E ∩ rL)
    have h6 := Finset.card_le_card h3
    have h7 : rL.card = L := Finset.card_range L
    omega

section
variable {xs : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF) (hv : ∀ v ∈ ψ.freeVars, v ∈ xs)
include hq hv

omit hq in
theorem mem_dedup_of_free {v : ℕ} (h : v ∈ ψ.freeVars) : v ∈ xs.dedup := List.mem_dedup.mpr (hv v h)

/-- The positions of the CNF are below `r`. -/
theorem idxs_lt : ∀ C ∈ (dataOf xs ψ s).cnf, ∀ l ∈ C, ∀ j ∈ l.atom.idxs,
    j < (dataOf xs ψ s).r := by
  intro C hC l hl j hj
  obtain ⟨a, ha, hla⟩ := mem_cnf xs.dedup ψ true hq C hC l hl
  have hfa := freeVars_of_mem_atoms ψ hq a ha
  simp only [dataOf]
  rw [hla] at hj
  rcases isAtom_of_mem_atoms ψ a ha with ⟨i, ys, rfl⟩ | ⟨ys, rfl⟩ | ⟨u, w, rfl⟩
  · simp only [renameAtom, Atom.idxs, List.mem_map] at hj
    obtain ⟨v, hv', rfl⟩ := hj
    exact List.idxOf_lt_length_iff.mpr
      (mem_dedup_of_free hv (hfa v (by simp [Formula.freeVars, hv'])))
  · simp only [renameAtom, Atom.idxs, List.mem_map] at hj
    obtain ⟨v, hv', rfl⟩ := hj
    exact List.idxOf_lt_length_iff.mpr
      (mem_dedup_of_free hv (hfa v (by simp [Formula.freeVars, hv'])))
  · simp only [renameAtom, Atom.idxs, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · exact List.idxOf_lt_length_iff.mpr
        (mem_dedup_of_free hv (hfa u (by simp [Formula.freeVars])))
    · exact List.idxOf_lt_length_iff.mpr
        (mem_dedup_of_free hv (hfa w (by simp [Formula.freeVars])))

/-- **Satisfaction of `∀ xs ψ` through the CNF.** -/
theorem sat_iff_cnf (A : Structure) (S : Set (List ℕ)) :
    Sat A S (Formula.allBlock xs ψ) (fun _ => 0) ↔
      ∀ ε : ℕ → ℕ, (∀ j < (dataOf xs ψ s).r, ε j < A.size) → CnfHolds A S ε (dataOf xs ψ s).cnf := by
  have hv' : ∀ v ∈ ψ.freeVars, v ∈ xs.dedup := fun v h => mem_dedup_of_free hv h
  have hidx := idxs_lt (s := s) hq hv
  rw [sat_allBlock]
  constructor
  · intro h ε hε
    let ρ : Assignment := fun v => if v ∈ xs then ε (xs.dedup.idxOf v) else 0
    have hs := h ρ (fun v hvx => by simp [ρ, hvx]) (fun v hvx => by
      simp only [ρ, if_pos hvx]
      exact hε _ (List.idxOf_lt_length_iff.mpr (List.mem_dedup.mpr hvx)))
    have := (cnfHolds_iff A S xs.dedup ρ ψ true hq hv').mpr (by simpa using hs)
    refine (cnfHolds_congr fun C hC l hl j hj => ?_).mp this
    have hj' : j < xs.dedup.length := hidx C hC l hl j hj
    have hmem : xs.dedup.getD j 0 ∈ xs.dedup := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']; exact List.getElem_mem hj'
    simp only [posVal, ρ, if_pos (List.mem_dedup.mp hmem)]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
    exact List.Nodup.idxOf_getElem (List.nodup_dedup xs) j hj'
  · intro h ρ h1 h2
    have := h (posVal xs.dedup ρ) fun j hj => by
      have hj' : j < xs.dedup.length := hj
      have hmem : xs.dedup.getD j 0 ∈ xs.dedup := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']; exact List.getElem_mem hj'
      exact h2 _ (List.mem_dedup.mp hmem)
    simpa using (cnfHolds_iff A S xs.dedup ρ ψ true hq hv').mp this

end

/-! ### Swapping into `U` -/

section Swap
variable {x : List ℕ} {A : Structure} {k : ℕ} {bl : List (List ℕ)} (he : Enc x A k bl) (D : Data)
include he

theorem lt_of_mem_U {a : ℕ} (h : a ∈ U D x) : a < A.size := by
  rw [← he.NW_eq]; exact lt_of_mem_UW h

theorem mem_U_of_mem {a : ℕ} (h : a ∈ x) (ha : a < A.size) : a ∈ U D x :=
  mem_UW_of_mem h (by rw [he.NW_eq]; exact ha)

omit he in
theorem range_U : ∀ e < LW D.s D.r x, e ∈ (U D x).toFinset :=
  fun _ h => List.mem_toFinset.mpr (mem_UW_of_lt h)

/-- Either `U` is the whole universe or it has the full count. -/
theorem LW_cases : (∀ e < A.size, e ∈ U D x) ∨ LW D.s D.r x = x.length + D.s * k + D.r := by
  unfold LW
  rw [he.NW_eq, he.kW_eq]
  rcases le_total A.size (x.length + D.s * k + D.r) with h | h
  · left; intro e he'; exact mem_UW_of_lt (by unfold LW; rw [he.NW_eq, he.kW_eq, min_eq_left h]; exact he')
  · right; exact min_eq_right h

theorem active_mem {e : ℕ} (h : Active A e) : e ∈ x.toFinset :=
  List.mem_toFinset.mpr (he.mem_of_active h)

end Swap

/-- The elements of the tuples of a set of tuples. -/
def elems (S : Finset (List ℕ)) : Finset ℕ := S.biUnion List.toFinset

theorem card_elems_le {S : Finset (List ℕ)} {s : ℕ} (h : ∀ t ∈ S, t.length = s) :
    (elems S).card ≤ S.card * s := by
  unfold elems
  refine Finset.card_biUnion_le.trans ?_
  have := Finset.sum_le_card_nsmul S (fun t => t.toFinset.card) s
    fun t ht => (List.toFinset_card_le t).trans (h t ht).le
  simpa using this

theorem mem_elems {S : Finset (List ℕ)} {a : ℕ} : a ∈ elems S ↔ ∃ t ∈ S, a ∈ t := by
  simp [elems]

theorem imgS_coe (π : Equiv.Perm ℕ) (S : Finset (List ℕ)) :
    imgS π (↑S : Set (List ℕ)) = ↑(S.image fun t => t.map π) := by
  ext t; simp [imgS]

/-- **A witness of weight `k` exists iff one exists among the elements of `U`.** -/
theorem witness_iff {xs : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF)
    (hv : ∀ v ∈ ψ.freeVars, v ∈ xs) {x : List ℕ} {A : Structure} {k : ℕ} {bl : List (List ℕ)}
    (he : Enc x A k bl) :
    Witness A (Formula.allBlock xs ψ) s k ↔
      (Formula.allBlock xs ψ).Fits A.arities s ∧ UWit A (dataOf xs ψ s) x k := by
  set D := dataOf xs ψ s with hD
  have hDs : D.s = s := rfl
  have hsat := sat_iff_cnf (s := s) hq hv A
  unfold Witness UWit
  refine and_congr_right fun _ => ?_
  have hUN : ∀ u ∈ (U D x).toFinset, u < A.size := fun u hu =>
    lt_of_mem_U he D (List.mem_toFinset.mp hu)
  constructor
  · rintro ⟨S, hcard, htup, hS⟩
    have hall := (hsat ↑S).mp hS
    set E := elems S
    have hEN : ∀ e ∈ E, e < A.size := fun e h => by
      obtain ⟨t, ht, het⟩ := mem_elems.mp h; exact (htup t ht).2 e het
    have hEF : ∀ e ∈ E, e ∉ (U D x).toFinset → e ∉ x.toFinset := fun e h hU hx =>
      hU (List.mem_toFinset.mpr (mem_U_of_mem he D (List.mem_toFinset.mp hx) (hEN e h)))
    have hcnt : (E \ (U D x).toFinset).card ≤ (((U D x).toFinset \ x.toFinset) \ E).card := by
      refine card_move _ _ _ (LW D.s D.r x) (range_U D) ?_
      rcases LW_cases he D with h | h
      · exact Or.inl fun e h' => List.mem_toFinset.mpr (h e (hEN e h'))
      · right
        have h1 : E.card ≤ S.card * s := card_elems_le (fun t ht => (htup t ht).1)
        have h2 := List.toFinset_card_le x
        rw [h, hDs]
        rw [hcard] at h1
        have : k * s = s * k := Nat.mul_comm _ _
        omega
    obtain ⟨π, hfix, hN, hE⟩ := exists_perm A.size _ _ hUN _ E rfl hEN hEF hcnt
    have hact : ∀ e, Active A e → π e = e := fun e h => hfix e (active_mem he h)
    refine ⟨S.image fun t => t.map π, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ (map_injective π)]; exact hcard
    · intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      refine ⟨by rw [List.length_map]; exact (htup u hu).1, fun a ha => ?_⟩
      obtain ⟨e, he', rfl⟩ := List.mem_map.mp ha
      exact List.mem_toFinset.mp (hE e (mem_elems.mpr ⟨u, hu, he'⟩))
    · intro ε hε
      have h1 := hall (fun j => π.symm (ε j)) fun j hj => by
        have := lt_of_mem_U he D (hε j hj)
        rw [← hN, Equiv.apply_symm_apply]; exact this
      rw [cnfHolds_perm hact, imgS_coe] at h1
      have : (π ∘ fun j => π.symm (ε j)) = ε := funext fun j => by simp
      rwa [this] at h1
  · rintro ⟨S, hcard, htup, hS⟩
    refine ⟨S, hcard, fun t ht => ⟨(htup t ht).1, fun a ha => lt_of_mem_U he D ((htup t ht).2 a ha)⟩,
      (hsat ↑S).mpr fun ε hε => ?_⟩
    set E := (Finset.range D.r).image ε
    set Fix := x.toFinset ∪ elems S
    have hEN : ∀ e ∈ E, e < A.size := fun e h => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h; exact hε j (Finset.mem_range.mp hj)
    have hSU : ∀ e ∈ elems S, e ∈ U D x := fun e h => by
      obtain ⟨t, ht, het⟩ := mem_elems.mp h; exact (htup t ht).2 e het
    have hEF : ∀ e ∈ E, e ∉ (U D x).toFinset → e ∉ Fix := fun e h hU hx => by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hU (List.mem_toFinset.mpr (mem_U_of_mem he D (List.mem_toFinset.mp hx) (hEN e h)))
      · exact hU (List.mem_toFinset.mpr (hSU e hx))
    have hcnt : (E \ (U D x).toFinset).card ≤ (((U D x).toFinset \ Fix) \ E).card := by
      refine card_move _ _ _ (LW D.s D.r x) (range_U D) ?_
      rcases LW_cases he D with h | h
      · exact Or.inl fun e h' => List.mem_toFinset.mpr (h e (hEN e h'))
      · right
        have h1 : (elems S).card ≤ S.card * D.s := card_elems_le (fun t ht => (htup t ht).1)
        have h2 := List.toFinset_card_le x
        have h3 : Fix.card ≤ x.toFinset.card + (elems S).card := Finset.card_union_le _ _
        have h4 : E.card ≤ D.r := (Finset.card_image_le).trans (by simp)
        rw [h]
        rw [hcard] at h1
        have : k * D.s = D.s * k := Nat.mul_comm _ _
        omega
    obtain ⟨π, hfix, -, hE⟩ := exists_perm A.size _ _ hUN _ E rfl hEN hEF hcnt
    have hact : ∀ e, Active A e → π e = e := fun e h =>
      hfix e (Finset.mem_union_left _ (active_mem he h))
    have h1 := hS (π ∘ ε) fun j hj => List.mem_toFinset.mp
      (hE _ (Finset.mem_image_of_mem ε (Finset.mem_range.mpr hj)))
    rw [cnfHolds_perm hact ↑S ε, imgS_eq ↑S fun t ht e het =>
      hfix e (Finset.mem_union_right _ (mem_elems.mpr ⟨t, ht, het⟩))]
    exact h1

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Semantics
