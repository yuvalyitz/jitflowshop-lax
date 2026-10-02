import Lax496464Proofs.Model.Sorted
import Lax496464Proofs.Model.Section6_Uniform
import Lax496464Proofs.Model.ConsecutiveOnes

namespace Lax496464Proofs

/-!
# Section 6.2: the Integer Program, and Lemma 5 as a Statement About Its Matrix

For `FF(1,m)|pⱼ = p, proper|∑wⱼZⱼ` the paper writes an ILP over binary variables `xⱼ`
(job `j` selected), maximizing `∑ wⱼxⱼ` subject to

* (6) `∑_{i ≤ j} xᵢ ≤ ⌊sⱼ/p⌋` for every job `j` — Condition 1 under uniform `p`;
* (7) `∑_{sᵢ ≤ sⱼ < dᵢ} xᵢ ≤ m` for every job `j` — Condition 2, read at each start time.

It then asserts *"It is easy to see that any feasible solution `𝐱` to our ILP corresponds to
a feasible solution `Z` … and vice versa"* without proof, and proves (Lemma 5) that the
`2n × n` constraint matrix has the consecutive ones property, which — by results it cites —
makes the LP relaxation integral.

This file proves the unproved correspondence (`ilp_correct`, `ilp_optimum`) and Lemma 5 at
the level of the matrix (`lemma5`). The implication "consecutive ones ⟹ totally unimodular"
is a cited literature fact and is an axiom in `Assumptions.lean`; integrality of the LP and
its polynomial-time solution are what the paper uses TU for, and are running-time matters
not stated here.

**Two assumptions, both explicit.** `0 < p`, so that `⌊sⱼ/p⌋` means what it says. And
`hs : ∀ j, 0 ≤ sⱼ`: constraint (6) is imposed for *every* job, so a job with `sⱼ < 0` would
make it read `∑_{i ≤ j} xᵢ ≤ ⌊sⱼ/p⌋ < 0`, unsatisfiable even at `𝐱 = 0` although `∅` is a
feasible solution. Such a job can never be just-in-time and can be deleted beforehand, so
the assumption is harmless — but the correspondence is false without it. This package's
model deliberately allows negative start times (`README.md`, "Start times are `ℤ`"), which
is why it surfaces here. Neither assumption involves properness: the correspondence holds
for every uniform-`p` instance, and only Lemma 5 needs the instance to be proper.
-/

namespace FlexFlowJIT

namespace EstFFJ

open _root_.Matrix Lax496464Proofs.Matrix

variable {E : EstFFJ}

/-! ## 1. The integer program -/

variable (E) in
/-- The `2n × n` constraint matrix: rows `inl j` are constraint (6), rows `inr j` are
constraint (7). -/
def ilpMatrix : Matrix (Fin E.n ⊕ Fin E.n) (Fin E.n) ℤ
  | Sum.inl j, i => if i ≤ j then 1 else 0
  | Sum.inr j, i => if E.st i ≤ E.st j ∧ E.st j < (E.d i : ℤ) then 1 else 0

variable (E) in
/-- The right-hand sides: `⌊sⱼ/p⌋` for (6), `m` for (7). -/
def ilpRhs (p : ℕ) : Fin E.n ⊕ Fin E.n → ℤ
  | Sum.inl j => E.st j / p
  | Sum.inr _ => E.numMachines

/-- The `0/1` vector of a job set. -/
def indicator (Z : Finset (Fin E.n)) : Fin E.n → ℤ := fun i => if i ∈ Z then 1 else 0

/-- Multiplying a `0/1` row by an indicator counts the selected jobs in the row. -/
private lemma sum_boole_indicator (Z : Finset (Fin E.n)) (P : Fin E.n → Prop)
    [DecidablePred P] :
    ∑ i, (if P i then (1 : ℤ) else 0) * indicator Z i = ((Z.filter P).card : ℤ) := by
  classical
  have h : ∀ i, (if P i then (1 : ℤ) else 0) * indicator Z i
      = if i ∈ Z.filter P then 1 else 0 := by
    intro i
    by_cases h1 : P i <;> by_cases h2 : i ∈ Z <;> simp [indicator, h1, h2]
  simp_rw [h]
  rw [Finset.sum_boole]
  congr 2
  ext i
  simp

lemma ilpMatrix_mulVec_inl (Z : Finset (Fin E.n)) (j : Fin E.n) :
    (E.ilpMatrix *ᵥ indicator Z) (Sum.inl j) = ((Z.filter (fun i => i ≤ j)).card : ℤ) := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_boole_indicator Z _

lemma ilpMatrix_mulVec_inr (Z : Finset (Fin E.n)) (j : Fin E.n) :
    (E.ilpMatrix *ᵥ indicator Z) (Sum.inr j)
      = ((Z.filter (fun i => E.st i ≤ E.st j ∧ E.st j < (E.d i : ℤ))).card : ℤ) := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_boole_indicator Z _

/-! ## 2. The correspondence the paper calls easy -/

/-- **A job set is feasible exactly when its indicator vector satisfies the ILP.** -/
theorem ilp_correct {p : ℕ} (hp : ∀ i, E.p i = p) (hp0 : 0 < p)
    (hq : ∀ i, 0 < E.q i) (hs : ∀ j, 0 ≤ E.st j) (Z : Finset (Fin E.n)) :
    E.toFFJ.Feasible Z ↔ ∀ r, (E.ilpMatrix *ᵥ indicator Z) r ≤ E.ilpRhs p r := by
  classical
  have hp0' : (0 : ℤ) < p := by exact_mod_cast hp0
  -- the prefix sums of `p` are counts
  have hsum : ∀ j : Fin E.n,
      ∑ i ∈ Z.filter (fun i => i ≤ j), (E.p i : ℤ)
        = ((Z.filter (fun i => i ≤ j)).card : ℤ) * p := by
    intro j
    rw [Finset.sum_congr rfl (fun i _ => by rw [hp i]), Finset.sum_const, nsmul_eq_mul]
  -- row (7) at `j` is the set running at `sⱼ`
  have hrun : ∀ j : Fin E.n,
      Z.filter (fun i => E.st i ≤ E.st j ∧ E.st j < (E.d i : ℤ))
        = E.toFFJ.running Z (E.toFFJ.s j) := fun _ => rfl
  rw [E.toFFJ.feasible_iff Z, preprocessable_iff_from_zero]
  constructor
  · rintro ⟨hpre, hsch⟩ (j | j)
    · rw [ilpMatrix_mulVec_inl]
      change ((Z.filter (fun i => i ≤ j)).card : ℤ) ≤ E.st j / p
      rw [Int.le_ediv_iff_mul_le hp0']
      rcases (Z.filter (fun i => i ≤ j)).eq_empty_or_nonempty with he | hne
      · rw [he]; simpa using hs j
      · -- read Condition 1 at the last selected job up to `j`
        obtain ⟨k, hk, hmax⟩ := (Z.filter (fun i => i ≤ j)).exists_max_image id hne
        obtain ⟨hkZ, hkj⟩ := Finset.mem_filter.mp hk
        have hsame : Z.filter (fun i => i ≤ k) = Z.filter (fun i => i ≤ j) := by
          ext x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hx, hxk⟩; exact ⟨hx, le_trans hxk hkj⟩
          · rintro ⟨hx, hxj⟩; exact ⟨hx, hmax x (Finset.mem_filter.mpr ⟨hx, hxj⟩)⟩
        have h1 := hpre k hkZ
        rw [hsame, hsum j] at h1
        have h2 := E.st_mono hkj
        omega
    · rw [ilpMatrix_mulVec_inr]
      change ((Z.filter _).card : ℤ) ≤ (E.numMachines : ℤ)
      rw [hrun j]
      have := FFJ.card_running_le_of_mSchedulable hsch (E.toFFJ.s j)
      exact_mod_cast this
  · intro h
    -- stated at the index type, so the two rows can be read off `h` by rewriting
    have hinl : ∀ j : Fin E.n, ((Z.filter (fun i => i ≤ j)).card : ℤ) * p ≤ E.st j := by
      intro j
      have h1 := h (Sum.inl j)
      rw [ilpMatrix_mulVec_inl] at h1
      change _ ≤ E.st j / p at h1
      rwa [Int.le_ediv_iff_mul_le hp0'] at h1
    have hinr : ∀ j : Fin E.n, (E.toFFJ.running Z (E.toFFJ.s j)).card ≤ E.numMachines := by
      intro j
      have h1 := h (Sum.inr j)
      rw [ilpMatrix_mulVec_inr, hrun j] at h1
      change _ ≤ (E.numMachines : ℤ) at h1
      exact_mod_cast h1
    refine ⟨fun j _ => ?_,
      (FFJ.mSchedulable_iff_card_running_start_le (fun i _ => hq i)).mpr fun j _ => hinr j⟩
    rw [hsum j]
    have := hinl j
    omega

/-- Every `0/1` vector is the indicator of the jobs it selects. -/
lemma eq_indicator {x : Fin E.n → ℤ} (hx : ∀ i, x i = 0 ∨ x i = 1) :
    x = indicator (Finset.univ.filter (fun i => x i = 1)) := by
  funext i
  simp only [indicator, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hx i with h | h <;> simp [h]

lemma objective_indicator (Z : Finset (Fin E.n)) :
    ∑ i, (E.w i : ℤ) * indicator Z i = (E.wt Z : ℤ) := by
  classical
  simp only [indicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp [wt]

/-- **The ILP's optimum is the problem's optimum.** A binary vector satisfying (6) and (7)
with objective value `W` exists exactly when a feasible job set of weight `W` does. -/
theorem ilp_optimum {p : ℕ} (hp : ∀ i, E.p i = p) (hp0 : 0 < p)
    (hq : ∀ i, 0 < E.q i) (hs : ∀ j, 0 ≤ E.st j) (W : ℕ) :
    (∃ x : Fin E.n → ℤ, (∀ i, x i = 0 ∨ x i = 1) ∧
        (∀ r, (E.ilpMatrix *ᵥ x) r ≤ E.ilpRhs p r) ∧ ∑ i, (E.w i : ℤ) * x i = W) ↔
      ∃ Z : Finset (Fin E.n), E.toFFJ.Feasible Z ∧ E.wt Z = W := by
  constructor
  · rintro ⟨x, hbin, hcon, hobj⟩
    refine ⟨Finset.univ.filter (fun i => x i = 1), ?_, ?_⟩
    · rw [ilp_correct hp hp0 hq hs, ← eq_indicator hbin]
      exact hcon
    · rw [eq_indicator hbin, objective_indicator] at hobj
      exact_mod_cast hobj
  · rintro ⟨Z, hZ, hw⟩
    refine ⟨indicator Z, fun i => ?_, (ilp_correct hp hp0 hq hs Z).mp hZ, ?_⟩
    · by_cases h : i ∈ Z <;> simp [indicator, h]
    · rw [objective_indicator, hw]

/-! ## 3. Lemma 5 -/

/-- **Lemma 5.** On a proper instance the ILP's `2n × n` constraint matrix has the
consecutive ones property. Rows (6) are prefixes; rows (7) are the jobs running at `sⱼ`,
which `FFJ.running_convex` shows form a block of consecutive indices. -/
theorem lemma5 (h : E.toFFJ.Proper) : Matrix.HasConsecutiveOnes E.ilpMatrix := by
  refine ⟨fun r c => ?_, fun r c₁ c c₂ h1 h2 hc1 hc2 => ?_⟩
  · rcases r with j | j <;> simp only [ilpMatrix] <;> split_ifs <;> simp
  · rcases r with j | j
    · simp only [ilpMatrix] at hc1 hc2 ⊢
      have hc2j : c₂ ≤ j := by
        split_ifs at hc2 with hh
        · exact hh
        · exact absurd hc2 (by omega)
      rw [if_pos (le_trans h2 hc2j)]
    · simp only [ilpMatrix] at hc1 hc2 ⊢
      have hr1 : E.st c₁ ≤ E.st j ∧ E.st j < (E.d c₁ : ℤ) := by
        split_ifs at hc1 with hh
        · exact hh
        · exact absurd hc1 (by omega)
      have hr2 : E.st c₂ ≤ E.st j ∧ E.st j < (E.d c₂ : ℤ) := by
        split_ifs at hc2 with hh
        · exact hh
        · exact absurd hc2 (by omega)
      have hrun := FFJ.running_convex h (Z := Finset.univ) (t := E.st j)
        (FFJ.mem_running.mpr ⟨Finset.mem_univ c₁, hr1.1, hr1.2⟩)
        (FFJ.mem_running.mpr ⟨Finset.mem_univ c₂, hr2.1, hr2.2⟩)
        (Finset.mem_univ c) (E.st_mono h1) (E.st_mono h2)
      obtain ⟨-, h3, h4⟩ := FFJ.mem_running.mp hrun
      rw [if_pos ⟨h3, h4⟩]


end EstFFJ

end FlexFlowJIT

end Lax496464Proofs
