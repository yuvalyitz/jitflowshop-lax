import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks
import Lax496464.WH_C3_WeightedSat

/-! # The monotone CNF formula and its weighted satisfiability

The formula of the reduction, over blocks `b < W = (k+1)^D` and values `v < C = (N+1)^D`. The
variable `Z(b, v) = 1 + b + W·v` says that block `b` has the values `v`; the variable `0` is a
*dummy* that no satisfying assignment of weight `W` can set.

* for every block `b`, the clause `⋁_v Z(b, v)` (`blockClause`);
* for every two blocks with values in `Conflict`, the clause `⋁_{e ≠ v₁} Z(b₁, e) ∨ ⋁_{e ≠ v₂} Z(b₂, e)`,
  i.e. `¬(Z(b₁,v₁) ∧ Z(b₂,v₂))` under exactly one value per block; for the other pairs the clause
  of block `b₁` (`xClause`, every clause padded with the dummy to the same length);
* for every `za < P`, the clause of the `Z(b, v)` with `good za b v zb` for some `zb < Q`
  (`mClause`).

All literals are positive. `weightSat_iff`: the formula has a satisfying assignment of weight `W`
iff there is a valid `t` with `∀ za < P, ∃ zb < Q, Truth za zb t` — given that `good` is sound for
consistent blocks and complete for the canonical ones. Weight `W` and one true variable per block
force exactly one per block, which reads off `t` (`Blocks.exists_valid`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf

open Lax429075.CNF Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The parameters of the formula. -/
structure Par where
  /-- The weight of the witness. -/
  k : ℕ
  /-- The number of tuple codes. -/
  N : ℕ
  /-- The number of slots of a block. -/
  D : ℕ
  /-- The number of universal assignments. -/
  P : ℕ
  /-- The number of existential assignments. -/
  Q : ℕ

variable (π : Par)

/-- The number of blocks. -/
def Par.W : ℕ := (π.k + 1) ^ π.D

/-- The number of values of a block. -/
def Par.C : ℕ := (π.N + 1) ^ π.D

/-- The variable of block `b` with values `v`. -/
def Par.zv (b v : ℕ) : ℕ := 1 + b + π.W * v

/-- The indices of block `b`. -/
abbrev Par.bd (b : ℕ) : List ℕ := digits (π.k + 1) π.D b

/-- The values `v`. -/
abbrev Par.vd (v : ℕ) : List ℕ := digits (π.N + 1) π.D v

/-- The two blocks with values are in conflict. -/
def Par.cf (b1 v1 b2 v2 : ℕ) : Bool :=
  decide (Conflict π.k π.N π.D (π.bd b1) (π.vd v1) (π.bd b2) (π.vd v2))

/-- A positive literal. -/
def lp (c : ℕ) : Literal := ⟨c, true⟩

/-- The clause of block `b`. -/
def Par.blockClause (b : ℕ) : Clause := (List.range π.C).map fun e => lp (π.zv b e)

/-- The clause of two blocks with values. -/
def Par.xClause (b1 v1 b2 v2 : ℕ) : Clause :=
  (List.range π.C).map (fun e => lp (if !π.cf b1 v1 b2 v2 || e != v1 then π.zv b1 e else 0)) ++
    (List.range π.C).map (fun e => lp (if π.cf b1 v1 b2 v2 && e != v2 then π.zv b2 e else 0))

/-- The clauses of all pairs of blocks with values. -/
def Par.xClauses : Formula :=
  (List.range π.W).flatMap fun b1 => (List.range π.C).flatMap fun v1 =>
    (List.range π.W).flatMap fun b2 => (List.range π.C).map fun v2 => π.xClause b1 v1 b2 v2

/-- The clause of the universal assignment `za`. -/
def Par.mClause (good : ℕ → ℕ → ℕ → ℕ → Bool) (za : ℕ) : Clause :=
  (List.range π.W).flatMap fun b => (List.range π.C).flatMap fun v =>
    (List.range π.Q).map fun zb => lp (if good za b v zb then π.zv b v else 0)

/-- **The formula.** -/
def Par.alpha (good : ℕ → ℕ → ℕ → ℕ → Bool) : Formula :=
  (List.range π.W).map π.blockClause ++ π.xClauses ++ (List.range π.P).map (π.mClause good)

theorem isMonotone_alpha (good : ℕ → ℕ → ℕ → ℕ → Bool) : IsMonotone (π.alpha good) := by
  intro C hC l hl
  simp only [Par.alpha, Par.xClauses, Par.blockClause, Par.xClause, Par.mClause, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_range] at hC
  rcases hC with (⟨b, -, rfl⟩ | ⟨b1, -, v1, -, b2, -, v2, -, rfl⟩) | ⟨za, -, rfl⟩
  · simp only [List.mem_map] at hl; obtain ⟨e, -, rfl⟩ := hl; rfl
  · simp only [List.mem_append, List.mem_map] at hl
    rcases hl with ⟨e, -, rfl⟩ | ⟨e, -, rfl⟩ <;> rfl
  · simp only [List.mem_flatMap, List.mem_map] at hl
    obtain ⟨b, -, v, -, zb, -, rfl⟩ := hl; rfl

/-! ### Variables -/

theorem zv_inj {b v b' v' : ℕ} (hb : b < π.W) (hb' : b' < π.W) (h : π.zv b v = π.zv b' v') :
    b = b' ∧ v = v' := by
  unfold Par.zv at h
  have hW : 0 < π.W := by omega
  have e1 : (b + π.W * v) % π.W = b := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
  have e2 : (b' + π.W * v') % π.W = b' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb']
  have h' : b + π.W * v = b' + π.W * v' := by omega
  have hbb : b = b' := by rw [← e1, ← e2, h']
  subst hbb
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hW (by omega)⟩

theorem zv_ne_zero (b v : ℕ) : π.zv b v ≠ 0 := by unfold Par.zv; omega

theorem W_pos : 0 < π.W := pow_pos (by omega) _

theorem mem_vars (good : ℕ → ℕ → ℕ → ℕ → Bool) {b v : ℕ} (hb : b < π.W) (hv : v < π.C) :
    π.zv b v ∈ vars (π.alpha good) := by
  unfold vars
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_map]
  refine ⟨π.blockClause b, ?_, lp (π.zv b v), ?_, rfl⟩
  · simp only [Par.alpha, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl ⟨b, hb, rfl⟩)
  · simp only [Par.blockClause, List.mem_map, List.mem_range]; exact ⟨v, hv, rfl⟩

/-! ### Satisfaction -/

theorem eval_iff (F : Formula) (ρ : Assignment) :
    eval F ρ = true ↔ ∀ C ∈ F, ∃ l ∈ C, Literal.eval l ρ = true := by
  simp [eval, List.all_eq_true, List.any_eq_true]

theorem lp_eval (c : ℕ) (T : Finset ℕ) : Literal.eval (lp c) (fun i => decide (i ∈ T)) = true ↔
    c ∈ T := by
  simp only [lp, Literal.eval, if_true]
  exact ⟨of_decide_eq_true, decide_eq_true⟩

section Main
variable (good : ℕ → ℕ → ℕ → ℕ → Bool) (Truth : ℕ → ℕ → List ℕ → Prop)

/-- **Weighted satisfiability of the formula.** -/
theorem weightSat_iff (hD : 1 ≤ π.D)
    (hsound : ∀ t, Valid π.k π.N t → ∀ za < π.P, ∀ b < π.W, ∀ v < π.C, ∀ zb < π.Q,
      Consistent π.k t (π.bd b) (π.vd v) → good za b v zb = true → Truth za zb t)
    (hcomplete : ∀ t, Valid π.k π.N t → ∀ za < π.P, ∀ zb < π.Q, Truth za zb t →
      ∃ b < π.W, good za b (canon π.k π.N π.D t b) zb = true) :
    WeightSat (π.alpha good) π.W ↔
      ∃ t, Valid π.k π.N t ∧ ∀ za < π.P, ∃ zb < π.Q, Truth za zb t := by
  constructor
  · rintro ⟨T, hsub, hcard, hev⟩
    rw [eval_iff] at hev
    have hcl : ∀ C ∈ π.alpha good, ∃ l ∈ C, l.index ∈ T := by
      intro C hC
      obtain ⟨l, hl, he⟩ := hev C hC
      refine ⟨l, hl, ?_⟩
      have hpos : l.positive = true := isMonotone_alpha π good C hC l hl
      simpa [Literal.eval, hpos] using he
    -- one value per block
    have hblk : ∀ b < π.W, ∃ v < π.C, π.zv b v ∈ T := by
      intro b hb
      obtain ⟨l, hl, hT⟩ := hcl _ (by
        simp only [Par.alpha, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl ⟨b, hb, rfl⟩))
      simp only [Par.blockClause, List.mem_map, List.mem_range] at hl
      obtain ⟨e, he, rfl⟩ := hl
      exact ⟨e, he, hT⟩
    choose! v hv hvT using hblk
    set I := (Finset.range π.W).image fun b => π.zv b (v b) with hI
    have hIT : I ⊆ T := by
      intro c hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      exact hvT b (Finset.mem_range.mp hb)
    have hIc : I.card = π.W := by
      rw [hI, Finset.card_image_of_injOn fun b hb b' hb' h =>
        (zv_inj π (Finset.mem_range.mp hb) (Finset.mem_range.mp hb') h).1]
      simp
    have hIT' : I = T := Finset.eq_of_subset_of_card_le hIT (by rw [hIc, hcard])
    have huniq : ∀ b < π.W, ∀ e, π.zv b e ∈ T → e = v b := by
      intro b hb e he
      rw [← hIT'] at he
      obtain ⟨b', hb', h⟩ := Finset.mem_image.mp he
      obtain ⟨rfl, rfl⟩ := zv_inj π (Finset.mem_range.mp hb') hb h
      rfl
    have h0 : (0 : ℕ) ∉ T := by
      intro h; rw [← hIT'] at h
      obtain ⟨b', -, h⟩ := Finset.mem_image.mp h
      exact zv_ne_zero π _ _ h
    -- no conflicts
    have hnc : ∀ b1 < π.W, ∀ b2 < π.W, ¬ Conflict π.k π.N π.D (π.bd b1) (π.vd (v b1))
        (π.bd b2) (π.vd (v b2)) := by
      intro b1 hb1 b2 hb2 hcf
      have hcf' : π.cf b1 (v b1) b2 (v b2) = true := by simp [Par.cf, hcf]
      obtain ⟨l, hl, hT⟩ := hcl (π.xClause b1 (v b1) b2 (v b2)) (by
        simp only [Par.alpha, Par.xClauses, List.mem_append, List.mem_flatMap, List.mem_map,
          List.mem_range]
        exact Or.inl (Or.inr ⟨b1, hb1, v b1, hv b1 hb1, b2, hb2, v b2, hv b2 hb2, rfl⟩))
      simp only [Par.xClause, List.mem_append, List.mem_map, List.mem_range] at hl
      rcases hl with ⟨e, he, rfl⟩ | ⟨e, he, rfl⟩
      · by_cases hne : e = v b1
        · simp [lp, hcf', hne] at hT; exact h0 hT
        · simp [lp, hcf', hne] at hT; exact hne (huniq b1 hb1 e hT)
      · by_cases hne : e = v b2
        · simp [lp, hcf', hne] at hT; exact h0 hT
        · simp [lp, hcf', hne] at hT; exact hne (huniq b2 hb2 e hT)
    obtain ⟨t, ht, hcons⟩ := exists_valid hD v hnc
    refine ⟨t, ht, fun za hza => ?_⟩
    obtain ⟨l, hl, hT⟩ := hcl (π.mClause good za) (by
      simp only [Par.alpha, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨za, hza, rfl⟩)
    simp only [Par.mClause, List.mem_flatMap, List.mem_map, List.mem_range] at hl
    obtain ⟨b, hb, e, he, zb, hzb, rfl⟩ := hl
    simp only [lp] at hT
    split_ifs at hT with hg
    · have := huniq b hb e hT
      subst this
      exact ⟨zb, hzb, hsound t ht za hza b hb (v b) he zb hzb (hcons b hb) hg⟩
    · exact absurd hT h0
  · rintro ⟨t, ht, hall⟩
    set T := (Finset.range π.W).image fun b => π.zv b (canon π.k π.N π.D t b) with hT
    have hmemT : ∀ b < π.W, π.zv b (canon π.k π.N π.D t b) ∈ T := fun b hb =>
      Finset.mem_image_of_mem _ (Finset.mem_range.mpr hb)
    refine ⟨T, fun c hc => ?_, ?_, ?_⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      exact mem_vars π good (Finset.mem_range.mp hb) (canon_lt ht b)
    · rw [hT, Finset.card_image_of_injOn fun b hb b' hb' h =>
        (zv_inj π (Finset.mem_range.mp hb) (Finset.mem_range.mp hb') h).1]
      simp
    · rw [eval_iff]
      intro C hC
      simp only [Par.alpha, Par.xClauses, List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_range] at hC
      rcases hC with (⟨b, hb, rfl⟩ | ⟨b1, hb1, v1, hv1, b2, hb2, v2, hv2, rfl⟩) | ⟨za, hza, rfl⟩
      · refine ⟨lp (π.zv b (canon π.k π.N π.D t b)), ?_, (lp_eval _ _).mpr (hmemT b hb)⟩
        simp only [Par.blockClause, List.mem_map, List.mem_range]
        exact ⟨_, canon_lt ht b, rfl⟩
      · have hnc : ¬ Conflict π.k π.N π.D (π.bd b1) (π.vd (canon π.k π.N π.D t b1))
            (π.bd b2) (π.vd (canon π.k π.N π.D t b2)) :=
          no_conflict ht (length_digits _ _ _) (length_digits _ _ _) (canon_consistent ht b1)
            (canon_consistent ht b2)
        by_cases hcf : π.cf b1 v1 b2 v2 = true
        · by_cases h1 : v1 = canon π.k π.N π.D t b1
          · have h2 : v2 ≠ canon π.k π.N π.D t b2 := by
              intro h2; subst h1; subst h2
              exact hnc (by simpa [Par.cf] using hcf)
            refine ⟨lp (π.zv b2 (canon π.k π.N π.D t b2)), ?_, (lp_eval _ _).mpr (hmemT b2 hb2)⟩
            simp only [Par.xClause, List.mem_append, List.mem_map, List.mem_range]
            refine Or.inr ⟨_, canon_lt ht b2, ?_⟩
            rw [if_pos (by simp [hcf, Ne.symm h2])]
          · refine ⟨lp (π.zv b1 (canon π.k π.N π.D t b1)), ?_, (lp_eval _ _).mpr (hmemT b1 hb1)⟩
            simp only [Par.xClause, List.mem_append, List.mem_map, List.mem_range]
            refine Or.inl ⟨_, canon_lt ht b1, ?_⟩
            rw [if_pos (by simp [Ne.symm h1])]
        · refine ⟨lp (π.zv b1 (canon π.k π.N π.D t b1)), ?_, (lp_eval _ _).mpr (hmemT b1 hb1)⟩
          simp only [Par.xClause, List.mem_append, List.mem_map, List.mem_range]
          refine Or.inl ⟨_, canon_lt ht b1, ?_⟩
          rw [if_pos (by simp [hcf])]
      · obtain ⟨zb, hzb, htr⟩ := hall za hza
        obtain ⟨b, hb, hg⟩ := hcomplete t ht za hza zb hzb htr
        refine ⟨lp (π.zv b (canon π.k π.N π.D t b)), ?_, (lp_eval _ _).mpr (hmemT b hb)⟩
        simp only [Par.mClause, List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨b, hb, _, canon_lt ht b, zb, hzb, by rw [if_pos hg]⟩

end Main

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
