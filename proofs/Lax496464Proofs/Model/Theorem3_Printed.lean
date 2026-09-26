import Lax496464Proofs.Model.Lemma3_Literal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

namespace Lax496464Proofs

/-!
# Theorem 3, second bullet: the printed recursion computes the right optimum

`Lemma3_Literal.lean` shows that recursion (5), exactly as printed, does not maintain Lemma 3's
invariant "`Tⱼ[x⃗, W']` is the least load of a solution whose profile is `x⃗`". This file proves
that it maintains the invariant the algorithm actually needs, and that its answer is correct:

* **soundness** (`litReach_sound`) — every entry the printed recursion derives is witnessed by
  a feasible solution of that weight and at most that load, whose profile is *at most* `x⃗`
  coordinatewise (the coordinates the shift leaves free are genuinely zero, so any value there
  over-counts, and over-counting busy machines only makes the `∑ xᵢ ≤ m` check stricter);
* **completeness** (`litReach_complete`) — every feasible solution is derived, with its exact
  profile, since the printed recursion only omits constraints;
* **the read-off** (`theorem3_printed_readoff`) — a weight `W'` has a finite entry after the
  last job exactly when a feasible solution of weight `W'` exists.

The hypotheses are the paper's standing ones for Section 5: positive weights and second-stage
times, `q_max` bounding every `qⱼ`, and distinct start times (Section 4's normalization,
`Section4_Distinct.lean`, supplies them).
-/

namespace FlexFlowJIT

namespace EstFFJ

variable {E : EstFFJ} {qmax : ℕ}

/-! ## 1. Helpers -/

lemma sum_Icc_one_eq_sum_fin (N : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc 1 N, f i = ∑ c : Fin N, f ((c : ℕ) + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun c => f (c + 1)) N, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

lemma decAt_apply {q : ℕ} (x : Fin q → ℕ) (c₀ c : Fin q) :
    decAt x c₀ c = if c = c₀ then x c - 1 else x c := by
  unfold decAt
  by_cases h : c = c₀
  · subst h; simp
  · simp [h]

lemma sum_decAt {q : ℕ} (x : Fin q → ℕ) (c₀ : Fin q) (h : 1 ≤ x c₀) :
    (∑ c, decAt x c₀ c) + 1 = ∑ c, x c := by
  classical
  have h1 : ∑ c, decAt x c₀ c = (x c₀ - 1) + ∑ c ∈ Finset.univ.erase c₀, x c := by
    rw [← Finset.add_sum_erase _ (decAt x c₀) (Finset.mem_univ c₀), decAt_apply, if_pos rfl]
    congr 1
    exact Finset.sum_congr rfl fun c hc => by
      rw [decAt_apply, if_neg (Finset.mem_erase.mp hc).1]
  have h2 : ∑ c, x c = x c₀ + ∑ c ∈ Finset.univ.erase c₀, x c :=
    (Finset.add_sum_erase _ x (Finset.mem_univ c₀)).symm
  omega

variable (E) in
/-- The reference time after the first `t` jobs: `s_t`, with the paper's `s₀ = 0`. -/
def refTime (t : ℕ) : ℤ := if h : 0 < t ∧ t ≤ E.n then E.st ⟨t - 1, by omega⟩ else 0

lemma refTime_succ (k : Fin E.n) : E.refTime ((k : ℕ) + 1) = E.st k := by
  have h : 0 < (k : ℕ) + 1 ∧ (k : ℕ) + 1 ≤ E.n := ⟨by omega, k.isLt⟩
  simp only [refTime, dif_pos h]
  congr 1

lemma st_le_refTime {t : ℕ} (ht : t ≤ E.n) {z : Fin E.n} (hz : (z : ℕ) < t) :
    E.st z ≤ E.refTime t := by
  have h : 0 < t ∧ t ≤ E.n := ⟨by omega, ht⟩
  simp only [refTime, dif_pos h]
  exact E.st_mono (Fin.le_def.mpr (by simp; omega))

lemma delta_eq (k : Fin E.n) (hk : 0 < (k : ℕ)) :
    (E.delta k : ℤ) = E.st k - E.refTime k := by
  have h : 0 < (k : ℕ) ∧ (k : ℕ) ≤ E.n := ⟨hk, le_of_lt k.isLt⟩
  have hs : E.sBefore k = E.refTime k := by
    simp only [sBefore, refTime, dif_neg (by omega : ¬ (k : ℕ) = 0), dif_pos h]
  have hle : E.refTime k ≤ E.st k := by
    simp only [refTime, dif_pos h]
    exact E.st_mono (Fin.le_def.mpr (by simp))
  unfold delta
  rw [hs, Int.toNat_of_nonneg (by omega)]

lemma dueProfile_empty (t : ℤ) (i : ℕ) : E.toFFJ.dueProfile ∅ t i = 0 := by
  unfold FFJ.dueProfile
  rw [Finset.filter_empty, Finset.card_empty]

/-- **Moving the reference time from `s_{k−1}` to `sₖ`.** For jobs before `k`, coordinate `c`
of the new profile is coordinate `δₖ + c` of the old one — or zero, past `q_max`. -/
lemma profile_step (hqmax : ∀ i, E.q i ≤ qmax) {k : Fin E.n} {Z : Finset (Fin E.n)}
    (hZ : ∀ z ∈ Z, (z : ℕ) < k) (c : ℕ) :
    E.toFFJ.dueProfile Z (E.st k) (c + 1) =
      if E.delta k + c < qmax then
        E.toFFJ.dueProfile Z (E.refTime k) (E.delta k + c + 1) else 0 := by
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hkpos
  · have hZe : Z = ∅ := Finset.eq_empty_of_forall_notMem fun z hz => by
      have := hZ z hz; omega
    subst hZe
    split_ifs
    · exact (dueProfile_empty _ _).trans (dueProfile_empty _ _).symm
    · exact dueProfile_empty _ _
  · have hshift := FFJ.dueProfile_shift (I := E.toFFJ) (Z := Z) (delta_eq k hkpos) (c + 1)
    rw [hshift]
    split_ifs with hlt
    · congr 1
    · refine FFJ.dueProfile_eq_zero (qmax := qmax)
        (fun z hz => st_le_refTime (le_of_lt k.isLt) (hZ z hz)) (fun z _ => hqmax z) ?_
      omega

/-! ## 2. Soundness: every derived entry is witnessed -/

/-- **Soundness of the printed recursion**, with the invariant it really maintains: a
solution of that weight and at most that load exists, whose profile is at most `x⃗`. -/
theorem litReach_sound (hq : ∀ i, 0 < E.q i) (hqmax : ∀ i, E.q i ≤ qmax)
    (hdist : ∀ i j : Fin E.n, i < j → E.st i < E.st j)
    {t : ℕ} {x : Fin qmax → ℕ} {W : ℕ} {P : ℤ} (h : E.LitReach qmax t x W P) :
    ∃ Z : Finset (Fin E.n), (∀ z ∈ Z, (z : ℕ) < t) ∧ E.toFFJ.Feasible Z ∧ E.wt Z = W ∧
      E.toFFJ.pload Z ≤ P ∧
      ∀ c : Fin qmax, E.toFFJ.dueProfile Z (E.refTime t) ((c : ℕ) + 1) ≤ x c := by
  induction h with
  | init =>
    exact ⟨∅, by simp, E.toFFJ.feasible_empty, rfl, by simp [FFJ.pload],
      fun c => (dueProfile_empty _ _).trans_le (Nat.zero_le _)⟩
  | zero t =>
    exact ⟨∅, by simp, E.toFFJ.feasible_empty, rfl, by simp [FFJ.pload],
      fun c => (dueProfile_empty _ _).trans_le (Nat.zero_le _)⟩
  | @skip k x y W P hcap hW hshift h ih =>
    obtain ⟨Z, hZt, hZf, hZw, hZp, hZx⟩ := ih
    refine ⟨Z, fun z hz => by have := hZt z hz; omega, hZf, hZw, hZp, fun c => ?_⟩
    rw [refTime_succ, profile_step hqmax hZt]
    split_ifs with hlt
    · calc E.toFFJ.dueProfile Z (E.refTime k) (E.delta k + c + 1)
          ≤ y ⟨E.delta k + c, hlt⟩ := hZx ⟨E.delta k + c, hlt⟩
        _ = x ⟨E.delta k + c - E.delta k, _⟩ := hshift ⟨E.delta k + c, hlt⟩ (by simp)
        _ = x c := congrArg x (Fin.ext (by simp))
    · exact Nat.zero_le _
  | @take k x y W P c₀ hc hxc hcap hW hwW hshift h hfit ih =>
    obtain ⟨Z, hZt, hZf, hZw, hZp, hZx⟩ := ih
    have hkZ : k ∉ Z := fun hk => by have := hZt k hk; omega
    have hlast : ∀ i ∈ Z, E.toFFJ.s i < E.toFFJ.s k := fun i hi =>
      hdist i k (Fin.lt_def.mpr (hZt i hi))
    -- the profile of `Z` at `sₖ` is below the decremented vector
    have hZdec : ∀ c : Fin qmax,
        E.toFFJ.dueProfile Z (E.st k) ((c : ℕ) + 1) ≤ decAt x c₀ c := by
      intro c
      rw [profile_step hqmax hZt]
      split_ifs with hlt
      · calc E.toFFJ.dueProfile Z (E.refTime k) (E.delta k + c + 1)
            ≤ y ⟨E.delta k + c, hlt⟩ := hZx ⟨E.delta k + c, hlt⟩
          _ = decAt x c₀ ⟨E.delta k + c - E.delta k, _⟩ :=
              hshift ⟨E.delta k + c, hlt⟩ (by simp)
          _ = decAt x c₀ c := congrArg (decAt x c₀) (Fin.ext (by simp))
      · exact Nat.zero_le _
    have hbk : ∀ z ∈ Z, E.toFFJ.s z ≤ E.st k := fun z hz => le_of_lt (hlast z hz)
    have hNk : ∀ z ∈ Z, (E.toFFJ.d z : ℤ) ≤ E.st k + qmax := fun z hz => by
      have h1 : E.st z = (E.d z : ℤ) - E.q z := rfl
      have h2 : E.st z ≤ E.st k := hbk z hz
      have h3 := hqmax z
      change (E.d z : ℤ) ≤ E.st k + qmax
      omega
    -- a machine is free at `sₖ`
    have hroom : (E.toFFJ.running Z (E.toFFJ.s k)).card < E.numMachines := by
      change (E.toFFJ.running Z (E.st k)).card < E.numMachines
      have hsum := FFJ.card_running_eq_sum (I := E.toFFJ) (Z := Z) (t := E.st k) (N := qmax)
        hbk hNk
      rw [sum_Icc_one_eq_sum_fin] at hsum
      have hle : ∑ c : Fin qmax, E.toFFJ.dueProfile Z (E.st k) ((c : ℕ) + 1)
          ≤ ∑ c, decAt x c₀ c := Finset.sum_le_sum fun c _ => hZdec c
      have hdec := sum_decAt x c₀ hxc
      omega
    refine ⟨insert k Z, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simp
      · have := hZt z hz; omega
    · refine FFJ.feasible_insert hq hkZ hZf hlast ?_ hroom
      change E.toFFJ.pload Z + (E.p k : ℤ) ≤ E.st k
      omega
    · have hins : E.wt (insert k Z) = E.w k + E.wt Z := by
        simp only [wt]
        exact Finset.sum_insert hkZ
      omega
    · exact (FFJ.pload_insert (I := E.toFFJ) hkZ).trans_le (add_le_add_left hZp _)
    · intro c
      rw [refTime_succ]
      have hins := FFJ.dueProfile_insert_start (I := E.toFFJ) (t := E.st k) hkZ rfl
        ((c : ℕ) + 1)
      refine le_of_eq_of_le hins ?_
      have hZc := hZdec c
      rw [decAt_apply] at hZc
      by_cases hcc : c = c₀
      · subst hcc
        have hq' : (c : ℕ) + 1 = E.toFFJ.q k := hc
        rw [if_pos rfl] at hZc
        rw [if_pos hq']
        omega
      · have hq' : ¬ ((c : ℕ) + 1 = E.toFFJ.q k) := fun h' =>
          hcc (Fin.ext (by change (c : ℕ) + 1 = E.q k at h'; omega))
        rw [if_neg hcc] at hZc
        rw [if_neg hq']
        omega

/-! ## 3. Completeness: every feasible solution is derived, with its exact profile -/

/-- **Completeness of the printed recursion.** For a feasible `Z`, the part of `Z` among the
first `t` jobs is derived after `t` steps, with its true profile, weight and load. -/
theorem litReach_complete (hq : ∀ i, 0 < E.q i) (hw : ∀ i, 0 < E.w i)
    (hqmax : ∀ i, E.q i ≤ qmax) {Z : Finset (Fin E.n)} (hZ : E.toFFJ.Feasible Z) :
    ∀ t : ℕ, t ≤ E.n → E.LitReach qmax t
      (fun c => E.toFFJ.dueProfile
        (Z.filter fun z : Fin E.n => (z : ℕ) < t : Finset (Fin E.n)) (E.refTime t) ((c : ℕ) + 1))
      (E.wt (Z.filter fun z : Fin E.n => (z : ℕ) < t))
      (E.toFFJ.pload (Z.filter fun z : Fin E.n => (z : ℕ) < t : Finset (Fin E.n))) := by
  obtain ⟨hpre, hsch⟩ := (E.toFFJ.feasible_iff Z).mp hZ
  have hpre0 := (preprocessable_iff_from_zero Z).mp hpre
  intro t
  induction t with
  | zero =>
    intro _
    have h0 : (Z.filter fun z : Fin E.n => (z : ℕ) < 0) = ∅ :=
      Finset.filter_false_of_mem fun z _ => by omega
    convert (LitReach.init (E := E) (qmax := qmax)) using 1
    · funext c
      simp only [h0]
      exact dueProfile_empty _ _
    · simp only [h0]; rfl
    · simp only [h0]; simp [FFJ.pload]
  | succ k ih =>
    intro hk
    have ih := ih (by omega)
    set kk : Fin E.n := ⟨k, by omega⟩ with hkk
    set Zk := Z.filter fun z : Fin E.n => (z : ℕ) < k with hZk
    have hkZk : kk ∉ Zk := fun h => by
      have := (Finset.mem_filter.mp h).2
      simp [hkk] at this
    have hZkZ : Zk ⊆ Z := Finset.filter_subset _ _
    -- the capacity check holds for any part of `Z` among the first `k + 1` jobs
    have hcapY : ∀ Y ⊆ Z, (∀ z ∈ Y, (z : ℕ) ≤ k) →
        ∑ c : Fin qmax, E.toFFJ.dueProfile Y (E.st kk) ((c : ℕ) + 1) ≤ E.numMachines := by
      intro Y hYZ hYk
      have hb : ∀ z ∈ Y, E.toFFJ.s z ≤ E.st kk := fun z hz =>
        E.st_mono (Fin.le_def.mpr (by change (z : ℕ) ≤ k; exact hYk z hz))
      have hN : ∀ z ∈ Y, (E.toFFJ.d z : ℤ) ≤ E.st kk + qmax := fun z hz => by
        have h1 : E.st z = (E.d z : ℤ) - E.q z := rfl
        have h2 : E.st z ≤ E.st kk := hb z hz
        have h3 := hqmax z
        change (E.d z : ℤ) ≤ E.st kk + qmax
        omega
      have hsum := FFJ.card_running_eq_sum (I := E.toFFJ) (Z := Y) (t := E.st kk)
        (N := qmax) hb hN
      rw [sum_Icc_one_eq_sum_fin] at hsum
      have hle := FFJ.card_running_le_of_mSchedulable
        (FFJ.MSchedulable.subset (h := hsch) (hsub := hYZ)) (E.st kk)
      exact hsum.symm.trans_le hle
    -- profiles of `Zk` at `s_{k−1}` and `sₖ` differ by the shift
    have hshiftZk : ∀ i : Fin qmax, E.delta kk ≤ (i : ℕ) →
        E.toFFJ.dueProfile Zk (E.refTime k) ((i : ℕ) + 1) =
          E.toFFJ.dueProfile Zk (E.st kk) ((i : ℕ) - E.delta kk + 1) := by
      intro i hi
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · have hZe : Zk = ∅ := Finset.eq_empty_of_forall_notMem fun z hz => by
          have := (Finset.mem_filter.mp hz).2; omega
        rw [hZe]
        exact (dueProfile_empty _ _).trans (dueProfile_empty _ _).symm
      · rw [FFJ.dueProfile_shift (I := E.toFFJ) (Z := Zk) (delta_eq kk hkpos)]
        congr 1
        omega
    by_cases hkZ : kk ∈ Z
    · -- job `k` is selected: the take rule
      have hZeq : (Z.filter fun z : Fin E.n => (z : ℕ) < k + 1) = insert kk Zk := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_insert, hZk, hkk, Fin.ext_iff]
        constructor
        · rintro ⟨hz, hzk⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hzk with h | h
          · exact Or.inr ⟨hz, h⟩
          · exact Or.inl h
        · rintro (h | ⟨hz, h⟩)
          · refine ⟨?_, by omega⟩
            have : z = kk := Fin.ext h
            rw [this]; exact hkZ
          · exact ⟨hz, by omega⟩
      set c₀ : Fin qmax := ⟨E.q kk - 1, by have := hq kk; have := hqmax kk; omega⟩ with hc₀
      have hins : ∀ c : ℕ, E.toFFJ.dueProfile (insert kk Zk : Finset (Fin E.n)) (E.st kk) c
          = E.toFFJ.dueProfile Zk (E.st kk) c + (if c = E.q kk then 1 else 0) :=
        fun c => FFJ.dueProfile_insert_start (I := E.toFFJ) (t := E.st kk) hkZk rfl c
      have hwt : E.wt (insert kk Zk) = E.w kk + E.wt Zk := by
        simp only [wt]; exact Finset.sum_insert hkZk
      have hfil : Z.filter (fun i => i ≤ kk) = insert kk Zk := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_insert, hZk, Fin.le_def, hkk, Fin.ext_iff]
        constructor
        · rintro ⟨hz, hzk⟩
          rcases Nat.lt_or_eq_of_le hzk with h | h
          · exact Or.inr ⟨hz, h⟩
          · exact Or.inl h
        · rintro (h | ⟨hz, h⟩)
          · refine ⟨?_, le_of_eq h⟩
            have : z = kk := Fin.ext h
            rw [this]; exact hkZ
          · exact ⟨hz, le_of_lt h⟩
      have hfit : E.toFFJ.pload Zk + E.p kk ≤ E.st kk := by
        have hs := hpre0 kk hkZ
        rw [hfil, Finset.sum_insert hkZk] at hs
        change (0 : ℤ) + ((E.p kk : ℤ) + ∑ i ∈ Zk, (E.p i : ℤ)) ≤ E.st kk at hs
        change ∑ i ∈ Zk, (E.p i : ℤ) + (E.p kk : ℤ) ≤ E.st kk
        omega
      have hd := LitReach.take (E := E) (qmax := qmax) (k := kk)
        (x := fun c =>
          E.toFFJ.dueProfile (insert kk Zk : Finset (Fin E.n)) (E.st kk) ((c : ℕ) + 1))
        (y := fun c => E.toFFJ.dueProfile Zk (E.refTime k) ((c : ℕ) + 1))
        (W := E.wt (insert kk Zk)) (P := E.toFFJ.pload Zk) c₀
        (by simp only [hc₀]; have := hq kk; omega)
        (by
          change 1 ≤ E.toFFJ.dueProfile (insert kk Zk : Finset (Fin E.n)) (E.st kk)
            ((E.q kk - 1) + 1)
          rw [hins, if_pos (by have := hq kk; omega)]
          omega)
        (hcapY _ (Finset.insert_subset hkZ hZkZ) (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | hz
          · simp [hkk]
          · exact le_of_lt (Finset.mem_filter.mp hz).2))
        (by rw [hwt]; have := hw kk; omega)
        (by rw [hwt]; omega)
        (fun i hi => by
          rw [hshiftZk i hi, decAt_apply]
          have hins' := hins ((i : ℕ) - E.delta kk + 1)
          have hqk := hq kk
          split_ifs with hic
          · have hv : (i : ℕ) - E.delta kk = E.q kk - 1 := congrArg Fin.val hic
            rw [if_pos (by omega)] at hins'
            change E.toFFJ.dueProfile Zk (E.st kk) ((i : ℕ) - E.delta kk + 1) =
              E.toFFJ.dueProfile (insert kk Zk : Finset (Fin E.n)) (E.st kk)
                ((i : ℕ) - E.delta kk + 1) - 1
            omega
          · have hv : (i : ℕ) - E.delta kk ≠ E.q kk - 1 := fun h => hic (Fin.ext h)
            rw [if_neg (by omega)] at hins'
            change E.toFFJ.dueProfile Zk (E.st kk) ((i : ℕ) - E.delta kk + 1) =
              E.toFFJ.dueProfile (insert kk Zk : Finset (Fin E.n)) (E.st kk)
                ((i : ℕ) - E.delta kk + 1)
            omega)
        (by rw [hwt, Nat.add_sub_cancel_left]; exact ih)
        hfit
      convert hd using 1
      · funext c
        simp only [hZeq]
        rw [show E.refTime (k + 1) = E.st kk from refTime_succ kk]
      · simp only [hZeq]
      · simp only [hZeq]
        exact FFJ.pload_insert (I := E.toFFJ) hkZk
    · -- job `k` is not selected
      have hZeq : (Z.filter fun z : Fin E.n => (z : ℕ) < k + 1) = Zk := by
        ext z
        simp only [Finset.mem_filter, hZk]
        constructor
        · rintro ⟨hz, hzk⟩
          refine ⟨hz, ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hzk with h | h
          · exact h
          · exact absurd (show z = kk from Fin.ext h) (fun he => hkZ (he ▸ hz))
        · rintro ⟨hz, h⟩
          exact ⟨hz, by omega⟩
      by_cases hemp : Zk = ∅
      · convert (LitReach.zero (E := E) (qmax := qmax) (k + 1)) using 1
        · funext c
          simp only [hZeq, hemp]
          exact dueProfile_empty _ _
        · simp only [hZeq, hemp]; rfl
        · simp only [hZeq, hemp]; simp [FFJ.pload]
      · have hne : Zk.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
        have hd := LitReach.skip (E := E) (qmax := qmax) (k := kk)
          (x := fun c => E.toFFJ.dueProfile Zk (E.st kk) ((c : ℕ) + 1))
          (y := fun c => E.toFFJ.dueProfile Zk (E.refTime k) ((c : ℕ) + 1))
          (W := E.wt Zk) (P := E.toFFJ.pload Zk)
          (hcapY _ hZkZ fun z hz => le_of_lt (Finset.mem_filter.mp hz).2)
          (Finset.sum_pos (fun i _ => hw i) hne)
          (fun i hi => hshiftZk i hi)
          ih
        convert hd using 1
        · funext c
          simp only [hZeq]
          rw [show E.refTime (k + 1) = E.st kk from refTime_succ kk]
        · simp only [hZeq]
        · simp only [hZeq]

/-! ## 4. The read-off -/

/-- **Theorem 3, second bullet, its correctness.** After the last job, the printed recursion
has a finite entry at weight `W'` exactly when a feasible solution of weight `W'` exists — so
the paper's algorithm returns the optimum, even though its intermediate entries need not be
the minima Lemma 3 describes. -/
theorem theorem3_printed_readoff (hq : ∀ i, 0 < E.q i) (hw : ∀ i, 0 < E.w i)
    (hqmax : ∀ i, E.q i ≤ qmax) (hdist : ∀ i j : Fin E.n, i < j → E.st i < E.st j)
    (W : ℕ) :
    (∃ (x : Fin qmax → ℕ) (P : ℤ), E.LitReach qmax E.n x W P) ↔
      ∃ Z : Finset (Fin E.n), E.toFFJ.Feasible Z ∧ E.wt Z = W := by
  constructor
  · rintro ⟨x, P, h⟩
    obtain ⟨Z, -, hZ, hwZ, -, -⟩ := litReach_sound hq hqmax hdist h
    exact ⟨Z, hZ, hwZ⟩
  · rintro ⟨Z, hZ, rfl⟩
    have h := litReach_complete hq hw hqmax hZ E.n le_rfl
    have hfil : (Z.filter fun z : Fin E.n => (z : ℕ) < E.n) = Z :=
      Finset.filter_true_of_mem fun z _ => z.isLt
    simp only [hfil] at h
    exact ⟨_, _, h⟩


end EstFFJ

end FlexFlowJIT

end Lax496464Proofs
