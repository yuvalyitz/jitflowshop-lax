import Lax496464Proofs.Ram.Q3Digits
import Lax496464Proofs.Model.Lemma3_Profile
import Lax496464Proofs.Bridge

/-!
# Q3: Correctness of the Profile Sweep (the Semantics `Rsem`)

Three theorems about `Q3Defs.Rsem`: the base (`Rsem_zero`), the step (`Rsem_succ`, which is
`Q3Defs.Step` applied to the previous stage), and the read-off (`Rsem_final`).  Unlike the
existing Section-5 development, jobs may *tie* in start time (`δ = 0`); the two insertion
lemmas of `Model/Lemma2_Sweep.lean` are therefore re-proved with a non-strict hypothesis
(`preprocessable_insert`, `feasible_insert`).
-/

namespace Lax496464Proofs.Ram.Q3Model

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Sweep Lax496464.Profile
  Lax496464.EstOrder Lax496464.Conditions
open Lax496464Proofs.Bridge Lax496464Proofs.Ram.Q3Defs Lax496464Proofs.Ram.Q3Digits
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

/-! ## 1. Bridge to the development's model -/

section Bridge

variable {I : Instance}

theorem feasible_iff_pre_card (hq : ∀ j : I.Job, 0 < I.q j) (Z : Finset I.Job) :
    Feasible I Z ↔ Preprocessable I Z ∧ ∀ t : ℤ, (running I Z t).card ≤ I.machines := by
  refine (feasible_iff_model Z).trans ?_
  refine ((model I).feasible_iff Z).trans ?_
  exact and_congr Iff.rfl (FFJ.mSchedulable_iff_card_running_le (I := model I) (fun j _ => hq j))

theorem pload_nonneg' (Z : Finset I.Job) : 0 ≤ pload I Z :=
  Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _

theorem pload_insert' {Z : Finset I.Job} {j : I.Job} (hj : j ∉ Z) :
    pload I (insert j Z) = pload I Z + I.p j := by
  rw [pload, pload, Finset.sum_insert hj]; ring

theorem feasible_empty' : Feasible I (∅ : Finset I.Job) :=
  (feasible_iff_model _).mpr (model I).feasible_empty

theorem feasible_subset {Z Z' : Finset I.Job} (h : Feasible I Z) (hsub : Z' ⊆ Z) :
    Feasible I Z' :=
  (feasible_iff_model _).mpr (FFJ.Feasible.subset (I := model I) ((feasible_iff_model _).mp h) hsub)

/-! ## 2. Non-strict insertion -/

theorem preprocessable_insert {Z : Finset I.Job} {j : I.Job} (hj : j ∉ Z)
    (hlast : ∀ i ∈ Z, s i ≤ s j) (hZ : Preprocessable I Z) (hfit : pload I Z + I.p j ≤ s j) :
    Preprocessable I (insert j Z) := by
  classical
  intro j' hj'
  rw [Finset.filter_insert]
  by_cases hle : s j ≤ s j'
  · rw [if_pos hle]
    rw [Finset.sum_insert (by simp [hj])]
    have hall : Z.filter (fun i => s i ≤ s j') = Z := Finset.filter_true_of_mem
      (fun x hx => le_trans (hlast x hx) hle)
    rw [hall]
    have : s j' ≤ s j := by
      rcases Finset.mem_insert.mp hj' with rfl | hj'Z
      · exact le_rfl
      · exact hlast j' hj'Z
    have h1 : pload I Z = ∑ i ∈ Z, (I.p i : ℤ) := rfl
    have h2 : s j = s j' := le_antisymm hle this
    omega
  · rw [if_neg hle]
    rcases Finset.mem_insert.mp hj' with rfl | hj'Z
    · exact absurd le_rfl hle
    · exact hZ j' hj'Z

theorem feasible_insert (hq : ∀ i : I.Job, 0 < I.q i) {Z : Finset I.Job} {j : I.Job}
    (hjZ : j ∉ Z) (hfeas : Feasible I Z) (hlast : ∀ i ∈ Z, s i ≤ s j)
    (hcount : pload I Z + I.p j ≤ s j)
    (hroom : (running I Z (s j)).card < I.machines) :
    Feasible I (insert j Z) := by
  classical
  obtain ⟨hpre, hZle⟩ := (feasible_iff_pre_card hq Z).mp hfeas
  refine (feasible_iff_pre_card hq _).mpr ⟨preprocessable_insert hjZ hlast hpre hcount, ?_⟩
  intro t
  by_cases hja : s j ≤ t ∧ t < (I.d j : ℤ)
  · have hrun : running I (insert j Z) t = insert j (running I Z t) := by
      unfold running
      rw [Finset.filter_insert, if_pos hja]
    rw [hrun]
    have hsub : running I Z t ⊆ running I Z (s j) := by
      intro x hx
      obtain ⟨hxZ, hx1, hx2⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxZ, hlast x hxZ, by omega⟩
    have h1 := Finset.card_insert_le j (running I Z t)
    have h2 := Finset.card_le_card hsub
    omega
  · have hrun : running I (insert j Z) t = running I Z t := by
      unfold running
      rw [Finset.filter_insert, if_neg hja]
    rw [hrun]
    exact hZle t

end Bridge

/-! ## 3. Reference times -/

section Ref

variable {I : Instance}

theorem trefN_zero' : trefN I 0 = 0 := by simp [trefN]

theorem trefN_succ (k : ℕ) (hk : k < I.jobs) :
    trefN I (k + 1) = I.d ⟨k, hk⟩ - I.q ⟨k, hk⟩ := by
  simp [trefN, dv, qv, hk]

/-- Every job before position `k` starts by the reference time of stage `k`. -/
theorem s_le_tref (hest : EstOrdered I) {k : ℕ} (hk : k ≤ I.jobs) (i : I.Job)
    (hi : (i : ℕ) < k) : s i ≤ (trefN I k : ℤ) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hk' : k' < I.jobs := by omega
  rw [trefN_succ k' hk']
  have h1 : s i ≤ s (⟨k', hk'⟩ : I.Job) := hest i ⟨k', hk'⟩ (by show (i : ℕ) ≤ k'; omega)
  unfold s at h1 ⊢
  omega

theorem tref_mono (hest : EstOrdered I) (k : ℕ) (hk : k < I.jobs) :
    trefN I k ≤ trefN I (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [trefN_zero']; exact Nat.zero_le _
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk' : k' < I.jobs := by omega
    rw [trefN_succ k' hk', trefN_succ (k' + 1) hk]
    have h1 : s (⟨k', hk'⟩ : I.Job) ≤ s (⟨k' + 1, hk⟩ : I.Job) :=
      hest ⟨k', hk'⟩ ⟨k' + 1, hk⟩ (by show k' ≤ k' + 1; omega)
    unfold s at h1
    omega

end Ref

/-! ## 4. Profiles -/

section Prof

variable {I : Instance}

theorem dueProfile_insert_start' {Z : Finset I.Job} {j : I.Job} (hj : j ∉ Z) {t : ℤ}
    (hsj : s j = t) (i : ℕ) :
    dueProfile I (insert j Z) t i = dueProfile I Z t i + (if i = I.q j then 1 else 0) :=
  FFJ.dueProfile_insert_start (I := model I) hj hsj i

theorem dueProfile_shift' {Z : Finset I.Job} {t' t : ℤ} {δ : ℕ} (hδ : (δ : ℤ) = t - t')
    (i : ℕ) : dueProfile I Z t i = dueProfile I Z t' (δ + i) :=
  FFJ.dueProfile_shift (I := model I) hδ i

theorem dueProfile_eq_zero' {Z : Finset I.Job} {t : ℤ} {qm i : ℕ}
    (hb : ∀ k ∈ Z, s k ≤ t) (hqm : ∀ k ∈ Z, I.q k ≤ qm) (hi : qm < i) :
    dueProfile I Z t i = 0 :=
  FFJ.dueProfile_eq_zero (I := model I) hb hqm hi

theorem card_running_eq_sum' {Z : Finset I.Job} {t : ℤ} {N : ℕ}
    (hb : ∀ k ∈ Z, s k ≤ t) (hN : ∀ k ∈ Z, (I.d k : ℤ) ≤ t + N) :
    (running I Z t).card = ∑ i ∈ Finset.Icc 1 N, dueProfile I Z t i :=
  FFJ.card_running_eq_sum (I := model I) hb hN

theorem sum_Icc_eq_range (f : ℕ → ℕ) (N : ℕ) :
    ∑ i ∈ Finset.Icc 1 N, f i = ∑ i ∈ Finset.range N, f (i + 1) := by
  induction N with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- With positive processing times, a feasible set has at most `m` jobs due at any one time. -/
theorem dueProfile_le_machines (hq : ∀ j : I.Job, 0 < I.q j) {Z : Finset I.Job}
    (hf : Feasible I Z) (t : ℤ) (i : ℕ) : dueProfile I Z t i ≤ I.machines := by
  obtain ⟨-, hc⟩ := (feasible_iff_pre_card hq Z).mp hf
  unfold dueProfile
  refine le_trans (Finset.card_le_card ?_) (hc (t + i - 1))
  intro x hx
  obtain ⟨hxZ, hd⟩ := Finset.mem_filter.mp hx
  have := hq x
  refine Finset.mem_filter.mpr ⟨hxZ, ?_, by omega⟩
  unfold s
  omega

/-- A feasible set's profile, as a number below `bt` (no start-time bound needed). -/
theorem profile_code (hq : ∀ j : I.Job, 0 < I.q j) {qm : ℕ} {Z : Finset I.Job}
    (hf : Feasible I Z) (t : ℤ) :
    ∃ y < (I.machines + 1) ^ qm, ∀ i < qm, dig (I.machines + 1) y i = dueProfile I Z t (i + 1) := by
  obtain ⟨h1, h2⟩ := dig_sum (bb := I.machines + 1) (qm := qm) (by omega)
    (fun i => dueProfile I Z t (i + 1))
    (fun i _ => Nat.lt_succ_of_le (dueProfile_le_machines hq hf t (i + 1)))
  exact ⟨_, h1, h2⟩

/-- Digits of a bounded number: past `qm` they vanish, and so does the profile. -/
theorem dig_full {bb qm : ℕ} {y : ℕ} (hy : y < bb ^ qm) {Z : Finset I.Job} {t : ℤ}
    (hz : ∀ i, qm ≤ i → dueProfile I Z t (i + 1) = 0)
    (h : ∀ i < qm, dig bb y i = dueProfile I Z t (i + 1)) (j : ℕ) :
    dig bb y j = dueProfile I Z t (j + 1) := by
  by_cases hj : j < qm
  · exact h j hj
  · rw [dig_of_ge hy (by omega), hz j (by omega)]

/-- Shifting the reference time by `δ` divides the code by `bb ^ min δ qm`. -/
theorem dig_shift {bb qm : ℕ} {y : ℕ} {Z : Finset I.Job} {t t' : ℤ} {δ : ℕ}
    (hδ : (δ : ℤ) = t' - t)
    (hy : ∀ j, dig bb y j = dueProfile I Z t (j + 1))
    (hz : ∀ i, qm ≤ i → dueProfile I Z t (i + 1) = 0) (i : ℕ) :
    dig bb (y / bb ^ (min δ qm)) i = dueProfile I Z t' (i + 1) := by
  rw [dig_div, hy, dueProfile_shift' hδ (i + 1)]
  by_cases hd : δ ≤ qm
  · rw [Nat.min_eq_left hd]; rfl
  · have h1 : dueProfile I Z t (δ + (i + 1)) = 0 := hz (δ + i) (by omega)
    rw [Nat.min_eq_right (by omega), hz (qm + i) (by omega), h1]

theorem card_running_eq_digsum {bb qm y : ℕ} {Z : Finset I.Job} {t : ℤ}
    (hb : ∀ k ∈ Z, s k ≤ t) (hqm : ∀ k ∈ Z, I.q k ≤ qm)
    (h : ∀ i < qm, dig bb y i = dueProfile I Z t (i + 1)) :
    (running I Z t).card = digsum bb qm y := by
  have hN : ∀ k ∈ Z, (I.d k : ℤ) ≤ t + qm := fun k hk => by
    have h1 := hb k hk
    have h2 := hqm k hk
    unfold s at h1
    omega
  rw [card_running_eq_sum' hb hN, sum_Icc_eq_range]
  unfold digsum
  exact Finset.sum_congr rfl (fun i hi => (h i (Finset.mem_range.1 hi)).symm)

end Prof

/-! ## 5. The base -/

theorem Rsem_zero (I : Instance) {qm : ℕ} (x c P : ℕ) (hx : x < (I.machines + 1) ^ qm) :
    Rsem I (I.machines + 1) qm 0 x c P ↔ x = 0 ∧ c = 0 := by
  constructor
  · rintro ⟨Z, hZ, -, hcw, -, hprof⟩
    have hZe : Z = ∅ := Finset.eq_empty_of_forall_notMem fun i hi => by
      have := hZ i hi; omega
    subst hZe
    refine ⟨?_, ?_⟩
    · refine ext_of_dig (bb := I.machines + 1) (qm := qm) (by omega) hx
        (Nat.pow_pos (by omega)) (fun i hi => ?_)
      rw [← hprof i hi]
      simp [dueProfile, dig]
    · simp [weight] at hcw
      omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨∅, by simp, feasible_empty', by simp [weight], by simp [pload],
      fun i hi => by simp [dueProfile, dig]⟩

/-! ## 6. The step -/

section Step

variable {I : Instance}

theorem job_facts (j : I.Job) : pv I j = I.p j ∧ qv I j = I.q j ∧ dv I j = I.d j ∧ wv I j = I.w j := by
  simp [pv, qv, dv, wv]

theorem trefN_succ' (j : I.Job) : trefN I ((j : ℕ) + 1) = I.d j - I.q j := trefN_succ _ j.isLt

theorem succ_mp (hest : EstOrdered I) (hq : ∀ j : I.Job, 0 < I.q j) {qm : ℕ}
    (hqm : ∀ j : I.Job, I.q j ≤ qm) (k : ℕ) (hk : k < I.jobs) (x c P : ℕ)
    (hx : x < (I.machines + 1) ^ qm) :
    Rsem I (I.machines + 1) qm (k + 1) x c P →
      Step ((I.machines + 1) ^ qm) (I.machines + 1) I.machines qm
        ((I.machines + 1) ^ (min (trefN I (k + 1) - trefN I k) qm))
        ((I.machines + 1) ^ (qv I k - 1)) (pv I k) (qv I k) (dv I k) (wv I k)
        (Rsem I (I.machines + 1) qm k) x c P := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j : I.Job, (j : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨hpv, hqv, hdv, hwv⟩ := job_facts j
  rw [hpv, hqv, hdv, hwv]
  have hT1 := trefN_succ' j
  have hmono := tref_mono hest j j.isLt
  have hδ : (((trefN I ((j : ℕ) + 1) - trefN I j : ℕ)) : ℤ)
      = (trefN I ((j : ℕ) + 1) : ℤ) - (trefN I j : ℤ) := by omega
  have hbk : ∀ i : I.Job, (i : ℕ) < j → s i ≤ (trefN I j : ℤ) :=
    fun i hi => s_le_tref hest (by have := j.isLt; omega) i hi
  have hbk1 : ∀ i : I.Job, (i : ℕ) < (j : ℕ) + 1 → s i ≤ (trefN I ((j : ℕ) + 1) : ℤ) :=
    fun i hi => s_le_tref hest (by have := j.isLt; omega) i hi
  have hbb : 1 ≤ I.machines + 1 := by omega
  rintro ⟨Z, hZk, hfeas, hcw, hpl, hprof⟩
  by_cases hkZ : j ∈ Z
  · right
    obtain ⟨Z', hZ'⟩ : ∃ Z' : Finset I.Job, Z' = Z.erase j := ⟨_, rfl⟩
    have hZ'k : ∀ i ∈ Z', (i : ℕ) < j := fun i hi => by
      rw [hZ'] at hi
      obtain ⟨hne, hiZ⟩ := Finset.mem_erase.mp hi
      have h1 := hZk i hiZ
      have h3 : (i : ℕ) ≠ j := fun h => hne (Fin.ext h)
      omega
    have hjZ' : j ∉ Z' := by rw [hZ']; exact Finset.notMem_erase _ _
    have hins : insert j Z' = Z := by rw [hZ']; exact Finset.insert_erase hkZ
    have hf' : Feasible I Z' := feasible_subset hfeas (by rw [hZ']; exact Finset.erase_subset _ _)
    obtain ⟨hpreZ, hcardZ⟩ := (feasible_iff_pre_card hq Z).mp hfeas
    have hlast : ∀ i ∈ Z, s i ≤ s j := fun i hi =>
      hest i j (by show (i : ℕ) ≤ j; have := hZk i hi; omega)
    have hfitZ : pload I Z ≤ s j := by
      have := hpreZ j hkZ
      rw [Finset.filter_true_of_mem hlast] at this
      exact this
    have hsj0 : 0 ≤ s j := le_trans (pload_nonneg' Z) hfitZ
    have ht' : (trefN I ((j : ℕ) + 1) : ℤ) = s j := by
      rw [hT1]
      have := hsj0
      unfold s at this ⊢
      omega
    have hbZ : ∀ i ∈ Z, s i ≤ (trefN I ((j : ℕ) + 1) : ℤ) := fun i hi => by
      rw [ht']; exact hlast i hi
    have hzZ : ∀ i, qm ≤ i → dueProfile I Z (trefN I ((j : ℕ) + 1) : ℤ) (i + 1) = 0 :=
      fun i hi => dueProfile_eq_zero' hbZ (fun k _ => hqm k) (by omega)
    have hbZ' : ∀ i ∈ Z', s i ≤ (trefN I j : ℤ) := fun i hi => hbk i (hZ'k i hi)
    have hz' : ∀ i, qm ≤ i → dueProfile I Z' (trefN I j : ℤ) (i + 1) = 0 :=
      fun i hi => dueProfile_eq_zero' hbZ' (fun k _ => hqm k) (by omega)
    have hqj : 0 < I.q j := hq j
    have hqjlt : I.q j - 1 < qm := by have := hqm j; omega
    have hins' : ∀ i, dueProfile I Z (trefN I ((j : ℕ) + 1) : ℤ) i
        = dueProfile I Z' (trefN I ((j : ℕ) + 1) : ℤ) i + (if i = I.q j then 1 else 0) :=
      fun i => by
        have := dueProfile_insert_start' hjZ' ht'.symm i
        rwa [hins] at this
    have hx1 : 1 ≤ x / (I.machines + 1) ^ (I.q j - 1) % (I.machines + 1) := by
      have h1 := hprof (I.q j - 1) hqjlt
      have h2 := hins' (I.q j - 1 + 1)
      have h3 : I.q j - 1 + 1 = I.q j := by omega
      rw [h3] at h1 h2
      rw [if_pos rfl] at h2
      show 1 ≤ dig (I.machines + 1) x (I.q j - 1)
      omega
    have hdsZ : digsum (I.machines + 1) qm x ≤ I.machines := by
      have := card_running_eq_digsum hbZ (fun i _ => hqm i) (fun i hi => (hprof i hi).symm)
      rw [← this]
      exact hcardZ _
    obtain ⟨y, hy, hydig⟩ := profile_code hq hf' (qm := qm) (trefN I j : ℤ)
    have hyfull := dig_full hy hz' hydig
    have hsub := sub_pow (bb := I.machines + 1) (qm := qm) (k := I.q j - 1) hbb hx hqjlt hx1
    have hwZ : I.w j + weight I Z' = weight I Z := by
      unfold weight
      rw [hZ']
      exact Finset.add_sum_erase Z (fun i => I.w i) hkZ
    have hplZ : pload I Z = pload I Z' + I.p j := by
      rw [← hins]; exact pload_insert' hjZ'
    have hpn := pload_nonneg' Z'
    have hfitZ' := hfitZ
    unfold s at hfitZ'
    refine ⟨hx1, hdsZ, y, hy, ?_, (pload I Z').toNat,
      ⟨Z', hZ'k, hf', by omega, Int.self_le_toNat _, fun i hi => (hydig i hi).symm⟩, by omega, by omega⟩
    refine ext_of_dig hbb (div_lt_pow hbb hy _) hsub.1 (fun i hi => ?_)
    rw [dig_shift hδ hyfull hz' i, hsub.2 i hi, ← hprof i hi, hins' (i + 1)]
    by_cases h : i + 1 = I.q j
    · rw [if_pos h, if_pos (by omega)]; omega
    · rw [if_neg h, if_neg (by omega)]; omega
  · left
    have hZk' : ∀ i ∈ Z, (i : ℕ) < j := fun i hi => by
      have h1 := hZk i hi
      have h2 : i ≠ j := fun h => hkZ (h ▸ hi)
      have h3 : (i : ℕ) ≠ j := fun h => h2 (Fin.ext h)
      omega
    have hb : ∀ i ∈ Z, s i ≤ (trefN I j : ℤ) := fun i hi => hbk i (hZk' i hi)
    have hz : ∀ i, qm ≤ i → dueProfile I Z (trefN I j : ℤ) (i + 1) = 0 :=
      fun i hi => dueProfile_eq_zero' hb (fun k _ => hqm k) (by omega)
    obtain ⟨y, hy, hydig⟩ := profile_code hq hfeas (qm := qm) (trefN I j : ℤ)
    have hyfull := dig_full hy hz hydig
    refine ⟨y, hy, ?_, Z, hZk', hfeas, hcw, hpl, fun i hi => (hydig i hi).symm⟩
    refine ext_of_dig hbb (div_lt_pow hbb hy _) hx (fun i hi => ?_)
    rw [dig_shift hδ hyfull hz i, hprof i hi]

theorem succ_mpr (hest : EstOrdered I) (hq : ∀ j : I.Job, 0 < I.q j) {qm : ℕ}
    (hqm : ∀ j : I.Job, I.q j ≤ qm) (k : ℕ) (hk : k < I.jobs) (x c P : ℕ)
    (hx : x < (I.machines + 1) ^ qm) :
    Step ((I.machines + 1) ^ qm) (I.machines + 1) I.machines qm
        ((I.machines + 1) ^ (min (trefN I (k + 1) - trefN I k) qm))
        ((I.machines + 1) ^ (qv I k - 1)) (pv I k) (qv I k) (dv I k) (wv I k)
        (Rsem I (I.machines + 1) qm k) x c P →
    Rsem I (I.machines + 1) qm (k + 1) x c P := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j : I.Job, (j : ℕ) = k := ⟨⟨k, hk⟩, rfl⟩
  obtain ⟨hpv, hqv, hdv, hwv⟩ := job_facts j
  rw [hpv, hqv, hdv, hwv]
  have hT1 := trefN_succ' j
  have hmono := tref_mono hest j j.isLt
  have hδ : (((trefN I ((j : ℕ) + 1) - trefN I j : ℕ)) : ℤ)
      = (trefN I ((j : ℕ) + 1) : ℤ) - (trefN I j : ℤ) := by omega
  have hbk : ∀ i : I.Job, (i : ℕ) < j → s i ≤ (trefN I j : ℤ) :=
    fun i hi => s_le_tref hest (by have := j.isLt; omega) i hi
  have hbb : 1 ≤ I.machines + 1 := by omega
  rintro (⟨y, hy, hyx, Z, hZk, hfeas, hcw, hpl, hprof⟩ |
    ⟨hx1, hds, y, hy, hyx, P'', ⟨Z', hZ'k, hf', hcw', hpl', hprof'⟩, hfit1, hfit2⟩)
  · have hb : ∀ i ∈ Z, s i ≤ (trefN I j : ℤ) := fun i hi => hbk i (hZk i hi)
    have hz : ∀ i, qm ≤ i → dueProfile I Z (trefN I j : ℤ) (i + 1) = 0 :=
      fun i hi => dueProfile_eq_zero' hb (fun k _ => hqm k) (by omega)
    have hyfull := dig_full hy hz (fun i hi => (hprof i hi).symm)
    refine ⟨Z, fun i hi => by have := hZk i hi; omega, hfeas, hcw, hpl, fun i hi => ?_⟩
    subst hyx
    exact (dig_shift hδ hyfull hz i).symm
  · have hjZ' : j ∉ Z' := fun h => by have := hZ'k j h; omega
    have hbZ0 : ∀ i ∈ Z', s i ≤ (trefN I j : ℤ) := fun i hi => hbk i (hZ'k i hi)
    have hz' : ∀ i, qm ≤ i → dueProfile I Z' (trefN I j : ℤ) (i + 1) = 0 :=
      fun i hi => dueProfile_eq_zero' hbZ0 (fun k _ => hqm k) (by omega)
    have hyfull := dig_full hy hz' (fun i hi => (hprof' i hi).symm)
    have hpn := pload_nonneg' Z'
    have hfit : pload I Z' + I.p j ≤ s j := by
      unfold s
      omega
    have hsj0 : 0 ≤ s j := by omega
    have ht' : (trefN I ((j : ℕ) + 1) : ℤ) = s j := by
      rw [hT1]
      unfold s at hsj0 ⊢
      omega
    have hlast : ∀ i ∈ Z', s i ≤ s j := fun i hi =>
      hest i j (by show (i : ℕ) ≤ j; have := hZ'k i hi; omega)
    have hbZ' : ∀ i ∈ Z', s i ≤ (trefN I ((j : ℕ) + 1) : ℤ) := fun i hi => by
      rw [ht']; exact hlast i hi
    have hqj : 0 < I.q j := hq j
    have hqjlt : I.q j - 1 < qm := by have := hqm j; omega
    have hsub := sub_pow (bb := I.machines + 1) (qm := qm) (k := I.q j - 1) hbb hx hqjlt hx1
    have hprofZ' : ∀ i < qm, dig (I.machines + 1) (x - (I.machines + 1) ^ (I.q j - 1)) i
        = dueProfile I Z' (trefN I ((j : ℕ) + 1) : ℤ) (i + 1) := fun i _ => by
      rw [← hyx]; exact dig_shift hδ hyfull hz' i
    have hroom : (running I Z' (s j)).card < I.machines := by
      rw [← ht', card_running_eq_digsum hbZ' (fun i _ => hqm i) hprofZ']
      have := digsum_sub_pow hbb hx hqjlt hx1
      omega
    refine ⟨insert j Z', fun i hi => ?_, feasible_insert hq hjZ' hf' hlast hfit hroom, ?_, ?_,
      fun i hi => ?_⟩
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · omega
      · have := hZ'k i hi; omega
    · have h1 : weight I (insert j Z') = I.w j + weight I Z' := by
        unfold weight; rw [Finset.sum_insert hjZ']
      omega
    · rw [pload_insert' hjZ']
      omega
    · rw [dueProfile_insert_start' hjZ' ht'.symm, ← hprofZ' i hi, hsub.2 i hi]
      by_cases h : i + 1 = I.q j
      · have hi' : i = I.q j - 1 := by omega
        have hd1 : 1 ≤ dig (I.machines + 1) x i := by rw [hi']; exact hx1
        rw [if_pos h, if_pos hi']
        omega
      · rw [if_neg h, if_neg (by omega)]
        omega

end Step

theorem Rsem_succ (I : Instance) (hest : EstOrdered I) (hq : ∀ j : I.Job, 0 < I.q j) {qm : ℕ}
    (hqm : ∀ j : I.Job, I.q j ≤ qm) (k : ℕ) (hk : k < I.jobs) (x c P : ℕ)
    (hx : x < (I.machines + 1) ^ qm) :
    Rsem I (I.machines + 1) qm (k + 1) x c P ↔
      Step ((I.machines + 1) ^ qm) (I.machines + 1) I.machines qm
        ((I.machines + 1) ^ (min (trefN I (k + 1) - trefN I k) qm))
        ((I.machines + 1) ^ (qv I k - 1)) (pv I k) (qv I k) (dv I k) (wv I k)
        (Rsem I (I.machines + 1) qm k) x c P :=
  ⟨succ_mp hest hq hqm k hk x c P hx, succ_mpr hest hq hqm k hk x c P hx⟩

/-! ## 7. The read-off -/

theorem Rsem_final (I : Instance) (hq : ∀ j : I.Job, 0 < I.q j) {qm : ℕ}
    (_hqm : ∀ j : I.Job, I.q j ≤ qm) {INF : ℕ} (hINF0 : 0 < INF) (hINF : ∀ j : I.Job, I.d j < INF)
    (W : ℕ) :
    HasWeight I W ↔ ∃ x < (I.machines + 1) ^ qm, Rsem I (I.machines + 1) qm I.jobs x W (INF - 1) := by
  classical
  constructor
  · rintro ⟨Z, hf, hW⟩
    obtain ⟨y, hy, hydig⟩ := profile_code hq hf (qm := qm) (trefN I I.jobs : ℤ)
    refine ⟨y, hy, Z, fun i _ => i.isLt, hf, hW, ?_, fun i hi => (hydig i hi).symm⟩
    rcases Z.eq_empty_or_nonempty with rfl | hne
    · simp [pload]
    · obtain ⟨j, hjZ, hmax⟩ := Z.exists_max_image (fun i => s i) hne
      obtain ⟨hpre, -⟩ := (feasible_iff_pre_card hq Z).mp hf
      have h0 := hpre j hjZ
      rw [Finset.filter_true_of_mem hmax] at h0
      have h1 := hINF j
      have h2 : s j ≤ I.d j := by unfold s; omega
      have h3 : pload I Z ≤ s j := h0
      omega
  · rintro ⟨x, -, Z, -, hf, hcw, -, -⟩
    exact ⟨Z, hf, hcw⟩

end Lax496464Proofs.Ram.Q3Model
