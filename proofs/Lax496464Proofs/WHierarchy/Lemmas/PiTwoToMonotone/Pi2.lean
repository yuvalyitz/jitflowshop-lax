import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax
import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Perm
import Lax496464.WH_B3_LogicProblems

/-! # A `Π₂`-sentence on positions, and witnesses among the elements of `U`

For `φ = ∀ xs ∃ ys ψ` (`ψ` quantifier-free, every free variable of `ψ` in `xs` or `ys`):

* `sat_iff_pi2`: `A ⊨ φ(S)` iff for every assignment of universe elements to the universal
  positions there is one to the existential positions satisfying the renamed `ψ` (`AllEx · · (· < N)`).
* `pi2_perm`: `AllEx` is invariant under permutations of the universe fixing the active elements.
* `pi2_compress`: when the tuples of `S` use elements of `U` only, the elements range over `U`
  instead of the universe without changing `AllEx`: elements outside `U` are isolated and can be
  swapped into `U`, which contains `|x| + s·k + r` elements (or all of them).
* `witness_iff`: a witness of weight `k` exists iff one exists among the elements of `U` for which
  `AllEx` holds with the elements ranging over `U`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Pi2

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Perm
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Perm (Active imgS exists_perm imgS_eq map_injective)
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Semantics (card_move elems card_elems_le mem_elems imgS_coe)

/-- **The `∀∃` condition on positions**, the elements ranging over `Dm`. -/
def AllEx (D : Data) (A : Structure) (S : Set (List ℕ)) (Dm : ℕ → Prop) : Prop :=
  ∀ ε : ℕ → ℕ, (∀ j, D.q ≤ j → j < D.r → Dm (ε j)) →
    ∃ ε' : ℕ → ℕ, (∀ j, D.q ≤ j → j < D.r → ε' j = ε j) ∧ (∀ j < D.q, Dm (ε' j)) ∧
      Sat A S D.ψ ε'

/-! ### Positions -/

section Pos
variable {xs ys : List ℕ}

theorem getD_mem_of_lt {l : List ℕ} {j : ℕ} (h : j < l.length) : l.getD j 0 ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

theorem idxOf_ys {v : ℕ} (h : v ∈ ys) : (posList xs ys).idxOf v = ys.dedup.idxOf v :=
  List.idxOf_append_of_mem (List.mem_dedup.mpr h)

theorem idxOf_xs {v : ℕ} (h : v ∉ ys) :
    (posList xs ys).idxOf v = ys.dedup.length + xs.dedup.idxOf v :=
  List.idxOf_append_of_notMem (fun h' => h (List.mem_dedup.mp h'))

theorem getD_pos_lt {j : ℕ} (h : j < ys.dedup.length) :
    (posList xs ys).getD j 0 = ys.dedup.getD j 0 := by
  unfold posList
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem getD_pos_ge {j : ℕ} (h : ys.dedup.length ≤ j) :
    (posList xs ys).getD j 0 = xs.dedup.getD (j - ys.dedup.length) 0 := by
  unfold posList
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

theorem getD_idxOf_self {l : List ℕ} {v : ℕ} (h : v ∈ l) : l.getD (l.idxOf v) 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (List.idxOf_lt_length_iff.mpr h)]
  simp

end Pos

section Sentence
variable {xs ys : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF)
  (hv : ∀ v ∈ ψ.freeVars, v ∈ xs ∨ v ∈ ys)
include hq hv

/-- **Satisfaction of `∀ xs ∃ ys ψ` on positions.** -/
theorem sat_iff_pi2 (A : Structure) (S : Set (List ℕ)) (ρ : Assignment) :
    Sat A S (Formula.allBlock xs (Formula.exBlock ys ψ)) ρ ↔
      AllEx (dataOf xs ys ψ s) A S (· < A.size) := by
  set D := dataOf xs ys ψ s with hD
  have hDq : D.q = ys.dedup.length := rfl
  have hDr : D.r = ys.dedup.length + xs.dedup.length := rfl
  have hDψ : D.ψ = rename (posList xs ys).idxOf ψ := rfl
  rw [sat_allBlock]
  simp only [sat_exBlock]
  unfold AllEx
  rw [hDψ]
  constructor
  · intro h ε hε
    let ρ1 : Assignment := fun v => if v ∈ xs then ε (ys.dedup.length + xs.dedup.idxOf v) else ρ v
    obtain ⟨ρ2, h2o, h2r, h2s⟩ := h ρ1 (fun v hvx => by simp [ρ1, hvx]) (fun v hvx => by
      simp only [ρ1, if_pos hvx]
      refine hε _ (by rw [hDq]; omega) ?_
      rw [hDr]
      have := List.idxOf_lt_length_iff.mpr (List.mem_dedup.mpr hvx)
      omega)
    refine ⟨fun j => if j < D.q then ρ2 ((posList xs ys).getD j 0) else ε j,
      fun j hj _ => by simp [show ¬ j < D.q by omega], fun j hj => ?_, ?_⟩
    · simp only [if_pos hj]
      rw [getD_pos_lt (by rw [← hDq]; exact hj)]
      exact h2r _ (List.mem_dedup.mp (getD_mem_of_lt (by rw [← hDq]; exact hj)))
    · rw [sat_rename A S _ _ ψ hq]
      refine (sat_congr A S ψ fun v hvf => ?_).mpr h2s
      simp only [Function.comp]
      by_cases hy : v ∈ ys
      · have hlt : ys.dedup.idxOf v < D.q := by
          rw [hDq]; exact List.idxOf_lt_length_iff.mpr (List.mem_dedup.mpr hy)
        rw [idxOf_ys hy, if_pos hlt, getD_pos_lt (by rw [← hDq]; exact hlt),
          getD_idxOf_self (List.mem_dedup.mpr hy)]
      · have hx : v ∈ xs := (hv v hvf).resolve_right hy
        rw [idxOf_xs hy, if_neg (by rw [hDq]; omega), h2o v hy]
        simp [ρ1, hx]
  · intro h ρ1 h1o h1r
    obtain ⟨ε', he1, he2, he3⟩ := h (fun j => ρ1 ((posList xs ys).getD j 0)) (fun j hj1 hj2 => by
      rw [getD_pos_ge (by rw [← hDq]; exact hj1)]
      refine h1r _ (List.mem_dedup.mp (getD_mem_of_lt ?_))
      rw [hDq, hDr] at *; omega)
    refine ⟨fun v => if v ∈ ys then ε' ((posList xs ys).idxOf v) else ρ1 v,
      fun v hvy => by simp [hvy], fun v hvy => ?_, ?_⟩
    · simp only [if_pos hvy]
      rw [idxOf_ys hvy]
      exact he2 _ (by rw [hDq]; exact List.idxOf_lt_length_iff.mpr (List.mem_dedup.mpr hvy))
    · rw [sat_rename A S _ _ ψ hq] at he3
      refine (sat_congr A S ψ fun v hvf => ?_).mp he3
      simp only [Function.comp]
      by_cases hy : v ∈ ys
      · simp [hy]
      · have hx : v ∈ xs := (hv v hvf).resolve_right hy
        have hi := List.idxOf_lt_length_iff.mpr (List.mem_dedup.mpr hx)
        rw [if_neg hy, idxOf_xs hy, he1 _ (by rw [hDq]; omega) (by rw [hDr]; omega)]
        rw [getD_pos_ge (by omega), Nat.add_sub_cancel_left,
          getD_idxOf_self (List.mem_dedup.mpr hx)]

end Sentence

/-! ### Permutations and compression -/

section Perm
variable {D : Data} {A : Structure} (hψ : D.ψ.IsQF)
include hψ

/-- **`AllEx` is invariant under an automorphism** of the universe. -/
theorem pi2_perm {π : Equiv.Perm ℕ} (hπ : ∀ e, Active A e → π e = e)
    (hN : ∀ e, π e < A.size ↔ e < A.size) {S : Set (List ℕ)}
    (h : AllEx D A S (· < A.size)) : AllEx D A (imgS π S) (· < A.size) := by
  intro ε hε
  obtain ⟨ε', h1, h2, h3⟩ := h (fun j => π.symm (ε j)) fun j hj1 hj2 => by
    have : ε j < A.size := hε j hj1 hj2
    show π.symm (ε j) < A.size
    rw [← hN, Equiv.apply_symm_apply]; exact this
  refine ⟨π ∘ ε', fun j hj1 hj2 => by simp [h1 j hj1 hj2], fun j hj => by
    simp only [Function.comp]; rw [hN]; exact h2 j hj, ?_⟩
  exact (sat_perm hπ S D.ψ ε' hψ).mp h3

/-- The room left in `U` for elements to be moved in. -/
structure Room (A : Structure) (U : Finset ℕ) (Fx : Finset ℕ) (L : ℕ) : Prop where
  lt : ∀ u ∈ U, u < A.size
  low : ∀ e < L, e ∈ U
  act : ∀ e, Active A e → e ∈ Fx
  fx : ∀ e ∈ Fx, e < A.size → e ∈ U

/-- **Compression**: the elements may range over `U` instead of the universe. -/
theorem pi2_compress {U Fx : Finset ℕ} {L : ℕ} (hR : Room A U Fx L) {S : Finset (List ℕ)}
    (hSU : ∀ e ∈ elems S, e ∈ U)
    (hroom : (∀ e < A.size, e ∈ U) ∨ Fx.card + (elems S).card + D.r ≤ L) :
    AllEx D A ↑S (· < A.size) ↔ AllEx D A ↑S (· ∈ U) := by
  constructor
  · intro h ε hε
    obtain ⟨ε', h1, h2, h3⟩ := h ε fun j hj1 hj2 => hR.lt _ (hε j hj1 hj2)
    set Ev := (Finset.range D.q).image ε' with hEv
    set Fix := Fx ∪ elems S ∪ (Finset.Ico D.q D.r).image ε with hFix
    have hEN : ∀ e ∈ Ev, e < A.size := fun e he => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he; exact h2 j (Finset.mem_range.mp hj)
    have hEF : ∀ e ∈ Ev, e ∉ U → e ∉ Fix := by
      intro e he hU hF
      rcases Finset.mem_union.mp hF with hF | hF
      · rcases Finset.mem_union.mp hF with hF | hF
        · exact hU (hR.fx e hF (hEN e he))
        · exact hU (hSU e hF)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hF
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        exact hU (hε j hj1 hj2)
    have hcnt : (Ev \ U).card ≤ ((U \ Fix) \ Ev).card := by
      refine card_move _ _ _ L hR.low ?_
      rcases hroom with hall | hle
      · exact Or.inl fun e he => hall e (hEN e he)
      · right
        have h1 : Fix.card ≤ Fx.card + (elems S).card + (D.r - D.q) := by
          refine (Finset.card_union_le _ _).trans ?_
          refine Nat.add_le_add ((Finset.card_union_le _ _)) ?_
          exact Finset.card_image_le.trans (by simp)
        have h2 : Ev.card ≤ D.q := Finset.card_image_le.trans (by simp)
        have : D.q ≤ D.r := by unfold Data.r; omega
        omega
    obtain ⟨π, hfix, hN, hE⟩ := exists_perm A.size U Fix hR.lt _ Ev rfl hEN hEF hcnt
    have hact : ∀ e, Active A e → π e = e := fun e he =>
      hfix e (Finset.mem_union_left _ (Finset.mem_union_left _ (hR.act e he)))
    refine ⟨π ∘ ε', fun j hj1 hj2 => ?_, fun j hj => hE _ (Finset.mem_image_of_mem _
      (Finset.mem_range.mpr hj)), ?_⟩
    · simp only [Function.comp, h1 j hj1 hj2]
      exact hfix _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _
        (Finset.mem_Ico.mpr ⟨hj1, hj2⟩)))
    · have := (sat_perm hact (↑S) D.ψ ε' hψ).mp h3
      rwa [imgS_eq (↑S) fun t ht e het =>
        hfix e (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_elems.mpr ⟨t, ht, het⟩)))]
        at this
  · intro h ε hε
    set Ev := (Finset.Ico D.q D.r).image ε with hEv
    set Fix := Fx ∪ elems S with hFix
    have hEN : ∀ e ∈ Ev, e < A.size := fun e he => by
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      exact hε j hj1 hj2
    have hEF : ∀ e ∈ Ev, e ∉ U → e ∉ Fix := by
      intro e he hU hF
      rcases Finset.mem_union.mp hF with hF | hF
      · exact hU (hR.fx e hF (hEN e he))
      · exact hU (hSU e hF)
    have hcnt : (Ev \ U).card ≤ ((U \ Fix) \ Ev).card := by
      refine card_move _ _ _ L hR.low ?_
      rcases hroom with hall | hle
      · exact Or.inl fun e he => hall e (hEN e he)
      · right
        have h1 : Fix.card ≤ Fx.card + (elems S).card := Finset.card_union_le _ _
        have h2 : Ev.card ≤ D.r - D.q := Finset.card_image_le.trans (by simp)
        omega
    obtain ⟨π, hfix, hN, hE⟩ := exists_perm A.size U Fix hR.lt _ Ev rfl hEN hEF hcnt
    have hact : ∀ e, Active A e → π e = e := fun e he =>
      hfix e (Finset.mem_union_left _ (hR.act e he))
    obtain ⟨ε1, h1, h2, h3⟩ := h (π ∘ ε) fun j hj1 hj2 =>
      hE _ (Finset.mem_image_of_mem _ (Finset.mem_Ico.mpr ⟨hj1, hj2⟩))
    refine ⟨π.symm ∘ ε1, fun j hj1 hj2 => by simp [h1 j hj1 hj2], fun j hj => ?_, ?_⟩
    · have := hR.lt _ (h2 j hj)
      simp only [Function.comp]
      rw [← hN, Equiv.apply_symm_apply]; exact this
    · have hact' : ∀ e, Active A e → π.symm e = e := fun e he => by
        conv_lhs => rw [← hact e he]
        simp
      have := (sat_perm hact' (↑S) D.ψ ε1 hψ).mp h3
      rwa [imgS_eq (↑S) fun t ht e het => by
        have := hfix e (Finset.mem_union_right _ (mem_elems.mpr ⟨t, ht, het⟩))
        conv_lhs => rw [← this]
        simp] at this

end Perm

/-! ### Witnesses -/

section Witness
variable {xs ys : List ℕ} {ψ : Formula} {s : ℕ} (hq : ψ.IsQF)
  (hv : ∀ v ∈ ψ.freeVars, v ∈ xs ∨ v ∈ ys)
include hq hv

/-- **A witness of weight `k` exists iff one exists among the elements of `U`** for which the
`∀∃` condition holds with the elements ranging over `U`. -/
theorem witness_iff {A : Structure} {k : ℕ} {U Fx : Finset ℕ} {L : ℕ} (hR : Room A U Fx L)
    (hroom : (∀ e < A.size, e ∈ U) ∨ Fx.card + s * k + (dataOf xs ys ψ s).r ≤ L) :
    Witness A (Formula.allBlock xs (Formula.exBlock ys ψ)) s k ↔
      ψ.Fits A.arities s ∧ ∃ S : Finset (List ℕ), S.card = k ∧
        (∀ t ∈ S, t.length = s ∧ ∀ a ∈ t, a ∈ U) ∧ AllEx (dataOf xs ys ψ s) A ↑S (· ∈ U) := by
  set D := dataOf xs ys ψ s with hD
  have hψ : D.ψ.IsQF := isQF_rename _ ψ hq
  have hsat := fun S => sat_iff_pi2 (s := s) hq hv A S (fun _ => 0)
  unfold Witness
  rw [fits_allBlock, fits_exBlock]
  refine and_congr_right fun _ => ?_
  have hroom' : ∀ S : Finset (List ℕ), S.card = k → (∀ t ∈ S, t.length = s) →
      (∀ e < A.size, e ∈ U) ∨ Fx.card + (elems S).card + D.r ≤ L := by
    intro S hc hl
    rcases hroom with h | h
    · exact Or.inl h
    · right
      have := card_elems_le hl
      rw [hc] at this
      have : k * s = s * k := Nat.mul_comm _ _
      omega
  constructor
  · rintro ⟨S, hcard, htup, hS⟩
    have hpi := (hsat ↑S).mp hS
    set E := elems S
    have hEN : ∀ e ∈ E, e < A.size := fun e h => by
      obtain ⟨t, ht, het⟩ := mem_elems.mp h; exact (htup t ht).2 e het
    have hEF : ∀ e ∈ E, e ∉ U → e ∉ Fx := fun e h hU hx => hU (hR.fx e hx (hEN e h))
    have hcnt : (E \ U).card ≤ ((U \ Fx) \ E).card := by
      refine card_move _ _ _ L hR.low ?_
      rcases hroom with h | h
      · exact Or.inl fun e h' => h e (hEN e h')
      · right
        have h1 : E.card ≤ S.card * s := card_elems_le (fun t ht => (htup t ht).1)
        rw [hcard] at h1
        have : k * s = s * k := Nat.mul_comm _ _
        omega
    obtain ⟨π, hfix, hN, hE⟩ := exists_perm A.size U Fx hR.lt _ E rfl hEN hEF hcnt
    have hact : ∀ e, Active A e → π e = e := fun e h => hfix e (hR.act e h)
    set S' := S.image fun t => t.map π
    have htup' : ∀ t ∈ S', t.length = s ∧ ∀ a ∈ t, a ∈ U := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      refine ⟨by rw [List.length_map]; exact (htup u hu).1, fun a ha => ?_⟩
      obtain ⟨e, he', rfl⟩ := List.mem_map.mp ha
      exact hE e (mem_elems.mpr ⟨u, hu, he'⟩)
    have hcard' : S'.card = k := by
      rw [Finset.card_image_of_injective _ (map_injective π)]; exact hcard
    refine ⟨S', hcard', htup', ?_⟩
    have hpi' : AllEx D A ↑S' (· < A.size) := by
      rw [← imgS_coe]; exact pi2_perm hψ hact hN hpi
    exact (pi2_compress hψ hR (fun e he => by
      obtain ⟨t, ht, het⟩ := mem_elems.mp he; exact (htup' t ht).2 e het)
      (hroom' S' hcard' fun t ht => (htup' t ht).1)).mp hpi'
  · rintro ⟨S, hcard, htup, hpi⟩
    refine ⟨S, hcard, fun t ht => ⟨(htup t ht).1, fun a ha => hR.lt _ ((htup t ht).2 a ha)⟩, ?_⟩
    rw [hsat]
    exact (pi2_compress hψ hR (fun e he => by
      obtain ⟨t, ht, het⟩ := mem_elems.mp he; exact (htup t ht).2 e het)
      (hroom' S hcard fun t ht => (htup t ht).1)).mpr hpi

end Witness

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Pi2
