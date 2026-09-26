import Lax496464.HittingSetHardness
import Mathlib.Tactic

/-!
# Correctness of the construction

A hitting set of size `vars F` meets each of the `vars F` disjoint pairs in exactly one
element, so it is a truth assignment; it meets the set of a clause exactly when that
assignment satisfies the clause.
-/

namespace Lax496464Proofs.HittingSet.Correct

open Lax429075.CNF Lax496464.HittingSet Lax496464.HittingSetFromSat

/-! ### The bound on the indices -/

theorem index_lt_foldr {l : List Literal} {a : ℕ} {x : Literal} (hx : x ∈ l) :
    x.index < l.foldr (fun l n => max (l.index + 1) n) a := by
  induction l with
  | nil => simp at hx
  | cons y t ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | hx'
      · omega
      · have := ih hx'; omega

theorem foldr_max_le {l : List Literal} {a M : ℕ} (ha : a ≤ M)
    (h : ∀ x ∈ l, x.index + 1 ≤ M) : l.foldr (fun l n => max (l.index + 1) n) a ≤ M := by
  induction l with
  | nil => simpa
  | cons y t ih =>
      simp only [List.foldr_cons]
      have := h y (List.mem_cons_self ..)
      have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
      omega

theorem index_lt_bound {F : Formula} {C : Clause} {l : Literal} (hC : C ∈ F) (hl : l ∈ C) :
    l.index < bound F :=
  index_lt_foldr (List.mem_flatMap.mpr ⟨C, hC, hl⟩)

theorem bound_le {F : Formula} {M : ℕ} (hM : 1 ≤ M)
    (h : ∀ C ∈ F, ∀ l ∈ C, l.index + 1 ≤ M) : bound F ≤ M :=
  foldr_max_le hM fun x hx => by
    obtain ⟨C, hC, hl⟩ := List.mem_flatMap.mp hx
    exact h C hC x hl

theorem two_le_vars (F : Formula) : 2 ≤ vars F := le_max_right _ _

theorem bound_le_vars (F : Formula) : bound F ≤ vars F := le_max_left _ _

theorem elem_lt {F : Formula} {C : Clause} {l : Literal} (hC : C ∈ F) (hl : l ∈ C) :
    elem l < 2 * vars F := by
  have := index_lt_bound hC hl
  have := bound_le_vars F
  unfold elem; split_ifs <;> omega

/-! ### The sets -/

theorem sets_getD_pair (F : Formula) {j : ℕ} (hj : j < vars F) :
    (sets F).getD j [] = [2 * j, 2 * j + 1] := by
  unfold sets
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hj)]
  simp [List.getElem?_map, List.getElem?_range hj]

theorem sets_getD_clause (F : Formula) {c : ℕ} (hc : c < F.length) :
    (sets F).getD (vars F + c) [] = (F.getD c []).map elem := by
  unfold sets
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp [List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]

theorem inst_n (F : Formula) : (inst F).n = 2 * vars F := rfl

theorem inst_m (F : Formula) : (inst F).m = vars F + F.length := rfl

theorem mem_F_iff (F : Formula) (j : Fin (inst F).m) (i : Fin (inst F).n) :
    i ∈ (inst F).F j ↔ (i : ℕ) ∈ (sets F).getD j [] := by
  change i ∈ (Finset.univ.filter fun i : Fin (inst F).n => (i : ℕ) ∈ (sets F).getD j []) ↔ _
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The element of `x_v` or of `¬x_v`, according to the truth value `b`. -/
def elemOf (v : ℕ) (b : Bool) : ℕ := 2 * v + if b then 0 else 1

theorem elemOf_lt {F : Formula} {v : ℕ} (hv : v < vars F) (b : Bool) : elemOf v b < (inst F).n := by
  rw [inst_n]; unfold elemOf; split_ifs <;> omega

theorem elemOf_inj {v w : ℕ} {b c : Bool} (h : elemOf v b = elemOf w c) : v = w := by
  unfold elemOf at h; split_ifs at h <;> omega

/-! ### From an assignment to a hitting set -/

/-- The hitting set of an assignment: the element of the true literal of every variable. -/
def ofAssignment (F : Formula) (ρ : Assignment) : Finset (Fin (inst F).n) :=
  (Finset.univ : Finset (Fin (vars F))).map
    ⟨fun v : Fin (vars F) => ⟨elemOf v (ρ v), elemOf_lt v.isLt _⟩,
     fun _v _w h => Fin.ext (elemOf_inj (Fin.mk.inj_iff.mp h))⟩

theorem card_ofAssignment (F : Formula) (ρ : Assignment) : (ofAssignment F ρ).card = vars F := by
  simp [ofAssignment]

theorem mem_ofAssignment {F : Formula} {ρ : Assignment} {i : Fin (inst F).n} :
    i ∈ ofAssignment F ρ ↔ ∃ v < vars F, elemOf v (ρ v) = i := by
  unfold ofAssignment
  rw [Finset.mem_map]
  constructor
  · rintro ⟨v, -, hv⟩; exact ⟨v, v.isLt, by rw [← hv]; rfl⟩
  · rintro ⟨v, hv, he⟩; exact ⟨⟨v, hv⟩, Finset.mem_univ _, Fin.ext he⟩

theorem hits_of_assignment {F : Formula} {ρ : Assignment} (hρ : eval F ρ = true)
    (j : Fin (inst F).m) : ∃ i ∈ ofAssignment F ρ, i ∈ (inst F).F j := by
  obtain ⟨j, hj⟩ := j
  by_cases hjv : j < vars F
  · refine ⟨⟨elemOf j (ρ j), elemOf_lt hjv _⟩, mem_ofAssignment.mpr ⟨j, hjv, rfl⟩, ?_⟩
    rw [mem_F_iff]
    simp only [sets_getD_pair F hjv]
    simp only [elemOf]; split_ifs <;> simp
  · have hj' : j - vars F < F.length := by
      have : j < (inst F).m := hj
      simp only [inst] at this; omega
    have hjj : j = vars F + (j - vars F) := by omega
    obtain ⟨C, hCF⟩ : ∃ C, F.getD (j - vars F) [] = C := ⟨_, rfl⟩
    have hCmem : C ∈ F := by
      rw [← hCF, List.getD_eq_getElem _ _ hj']; exact List.getElem_mem hj'
    have hsat : C.any (fun l => l.eval ρ) = true := by
      unfold eval at hρ
      exact (List.all_eq_true.mp hρ) C hCmem
    obtain ⟨l, hl, hle⟩ := List.any_eq_true.mp hsat
    have hlt := elem_lt hCmem hl
    refine ⟨⟨elem l, hlt⟩, ?_, ?_⟩
    · refine mem_ofAssignment.mpr ⟨l.index, ?_, ?_⟩
      · have := index_lt_bound hCmem hl; have := bound_le_vars F; omega
      · show elemOf l.index (ρ l.index) = elemOf l.index l.positive
        unfold Literal.eval at hle
        by_cases hp : l.positive
        · rw [if_pos hp] at hle; rw [hle, hp]
        · rw [if_neg hp] at hle
          have hp' : l.positive = false := by simpa using hp
          have hle' : ρ l.index = false := by simpa using hle
          rw [hle', hp']
    · rw [mem_F_iff]
      simp only
      conv_lhs => rw [hjj]
      rw [sets_getD_clause F hj', hCF]
      exact List.mem_map.mpr ⟨l, hl, rfl⟩

/-! ### From a hitting set to an assignment -/

/-- The pair of an element: its variable. -/
def pairOf {n : ℕ} (i : Fin n) : ℕ := (i : ℕ) / 2

theorem pair_hit {F : Formula} {H : Finset (Fin (inst F).n)}
    (hH : ∀ j : Fin (inst F).m, ∃ i ∈ H, i ∈ (inst F).F j) {v : ℕ} (hv : v < vars F) :
    ∃ i ∈ H, (i : ℕ) = 2 * v ∨ (i : ℕ) = 2 * v + 1 := by
  obtain ⟨i, hi, hmem⟩ := hH ⟨v, by rw [inst_m]; omega⟩
  refine ⟨i, hi, ?_⟩
  rw [mem_F_iff] at hmem
  simp only [sets_getD_pair F hv, List.mem_cons, List.not_mem_nil, or_false]
    at hmem
  exact hmem

/-- Each fibre of a hitting set over the pairs is nonempty, so with `vars F` elements each
has exactly one. -/
theorem fibre_card_eq_one {F : Formula} {H : Finset (Fin (inst F).n)}
    (hcard : H.card = vars F)
    (hH : ∀ j : Fin (inst F).m, ∃ i ∈ H, i ∈ (inst F).F j) {v : ℕ} (hv : v < vars F) :
    (H.filter fun i => pairOf i = v).card = 1 := by
  have hsum : H.card = ∑ w ∈ Finset.range (vars F), (H.filter fun i => pairOf i = w).card := by
    refine Finset.card_eq_sum_card_fiberwise fun i _ => ?_
    simp only [Finset.mem_coe, Finset.mem_range, pairOf]
    have : (i : ℕ) < 2 * vars F := i.isLt
    omega
  have hpos : ∀ w ∈ Finset.range (vars F), 1 ≤ (H.filter fun i => pairOf i = w).card := by
    intro w hw
    obtain ⟨i, hi, hiw⟩ := pair_hit hH (Finset.mem_range.mp hw)
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, by simp only [pairOf]; omega⟩⟩
  by_contra hne
  have hge : 2 ≤ (H.filter fun i => pairOf i = v).card := by
    have := hpos v (Finset.mem_range.mpr hv); omega
  have hle : ∑ w ∈ Finset.range (vars F), (1 + if w = v then 1 else 0) ≤
      ∑ w ∈ Finset.range (vars F), (H.filter fun i => pairOf i = w).card := by
    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hwv
    · subst hwv; omega
    · have := hpos w hw; omega
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (vars F)) v] at hle
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
    Finset.mem_range.mpr hv, if_true] at hle
  omega

theorem not_both {F : Formula} {H : Finset (Fin (inst F).n)}
    (hcard : H.card = vars F)
    (hH : ∀ j : Fin (inst F).m, ∃ i ∈ H, i ∈ (inst F).F j) {v : ℕ} (hv : v < vars F)
    {i i' : Fin (inst F).n} (hi : i ∈ H) (hi' : i' ∈ H) (h1 : (i : ℕ) = 2 * v)
    (h2 : (i' : ℕ) = 2 * v + 1) : False := by
  have h := fibre_card_eq_one hcard hH hv
  have hsub : ({i, i'} : Finset (Fin (inst F).n)) ⊆ H.filter fun i => pairOf i = v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hi, by simp only [pairOf]; omega⟩
    · exact Finset.mem_filter.mpr ⟨hi', by simp only [pairOf]; omega⟩
  have hne : i ≠ i' := fun h => by rw [h] at h1; omega
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at this
  omega

/-- The assignment of a hitting set: a variable is true when the element of its positive
literal is in the set. -/
def toAssignment (F : Formula) (H : Finset (Fin (inst F).n)) : Assignment :=
  fun v => if h : 2 * v < (inst F).n then decide (⟨2 * v, h⟩ ∈ H) else false

theorem eval_of_hittingSet {F : Formula} {H : Finset (Fin (inst F).n)}
    (hcard : H.card = vars F)
    (hH : ∀ j : Fin (inst F).m, ∃ i ∈ H, i ∈ (inst F).F j) :
    eval F (toAssignment F H) = true := by
  unfold eval
  refine List.all_eq_true.mpr fun C hC => ?_
  obtain ⟨c, hc, hCc⟩ := List.getElem_of_mem hC
  obtain ⟨i, hi, hmem⟩ := hH ⟨vars F + c, by rw [inst_m]; omega⟩
  rw [mem_F_iff] at hmem
  simp only [sets_getD_clause F hc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc,
    Option.getD_some, hCc] at hmem
  obtain ⟨l, hl, hli⟩ := List.mem_map.mp hmem
  refine List.any_eq_true.mpr ⟨l, hl, ?_⟩
  have hidx : l.index < vars F := by
    have := index_lt_bound hC hl; have := bound_le_vars F; omega
  have h2 : 2 * l.index < (inst F).n := by rw [inst_n]; omega
  unfold Literal.eval toAssignment
  rw [dif_pos h2]
  by_cases hp : l.positive
  · simp only [hp, if_true, decide_eq_true_eq]
    have : (⟨2 * l.index, h2⟩ : Fin (2 * vars F)) = i := by
      apply Fin.ext; rw [← hli, elem]; simp [hp]
    subst this; exact hi
  · have hp' : l.positive = false := by simpa using hp
    simp only [hp', Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true', decide_eq_false_iff_not]
    intro hin
    have hi' : (i : ℕ) = 2 * l.index + 1 := by rw [← hli, elem]; simp [hp]
    exact not_both hcard hH hidx hin hi rfl hi'

/-! ### Together -/

/--
---
conclusion: Lax496464.HittingSetHardness.fromSat_correct
---
A satisfying assignment gives the set of the elements of its true literals, one per
variable; conversely a hitting set of size `vars F` meets each of the `vars F` disjoint
pairs in exactly one element, which fixes an assignment, and meeting the set of a clause
is satisfying the clause.
-/
theorem fromSat_correct (F : Formula) : Satisfiable F ↔ (inst F).HasHittingSet (vars F) := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨ofAssignment F ρ, card_ofAssignment F ρ, hits_of_assignment hρ⟩
  · rintro ⟨H, hcard, hH⟩
    exact ⟨toAssignment F H, eval_of_hittingSet hcard hH⟩

end Lax496464Proofs.HittingSet.Correct
