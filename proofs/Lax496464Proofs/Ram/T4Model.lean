import Lax496464.Greedy
import Lax496464.EstOrder
import Lax496464Proofs.Section6

/-!
# The Greedy of Section 6.1, One Step at a Time, on Finite Sets

The machine of `Ram/T4Prog.lean` keeps the set `A` the greedy holds as a sum of two parts:
`Act`, the members of `A` that may still be running (kept in two maximum trees), and the
members that have already ended, which are only counted. This file is the pure bookkeeping:
`Inv k A Act` is what the machine keeps true before it considers job `k`, and `step_add` /
`step_drop` say that the machine's two ways of moving on are exactly `Greedy.Step`'s two cases,
with the invariant re-established.
-/

namespace Lax496464Proofs.Ram.T4Model

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Greedy Lax496464.EstOrder

variable {J : Instance}

/-- What the machine keeps true before it considers job `k`: `A` holds only earlier jobs,
`Act ⊆ A`, and everything in `A` outside `Act` is over by the start of job `k`. -/
structure Inv (J : Instance) (k : ℕ) (A Act : Finset J.Job) : Prop where
  before : ∀ i ∈ A, (i : ℕ) < k
  sub : Act ⊆ A
  over : ∀ i ∈ A, i ∉ Act → ∀ hk : k < J.jobs, (J.d i : ℤ) ≤ s (⟨k, hk⟩ : J.Job)

theorem Inv.zero : Inv J 0 ∅ ∅ :=
  ⟨fun _ h => absurd h (by simp), Finset.Subset.refl _, fun _ h => absurd h (by simp)⟩

/-- The members of `Act` still running at the start of job `k`. -/
def live (Act : Finset J.Job) (k : J.Job) : Finset J.Job :=
  Act.filter fun i => s k < (J.d i : ℤ)

theorem mem_live {Act : Finset J.Job} {k i : J.Job} : i ∈ live Act k ↔ i ∈ Act ∧ s k < (J.d i : ℤ) := by
  simp [live]

/-- **The running count is the live count.** -/
theorem running_eq (hest : EstOrdered J) {A Act : Finset J.Job} {k : J.Job}
    (hb : ∀ i ∈ A, i < k) (hsub : Act ⊆ A) (hover : ∀ i ∈ A, i ∉ Act → (J.d i : ℤ) ≤ s k) :
    running J A (s k) = live Act k := by
  ext i
  simp only [running, Finset.mem_filter, mem_live]
  constructor
  · rintro ⟨hiA, -, hlt⟩
    refine ⟨?_, hlt⟩
    by_contra hn
    have := hover i hiA hn
    omega
  · rintro ⟨hiAct, hlt⟩
    have hiA := hsub hiAct
    exact ⟨hiA, hest i k (hb i hiA).le, hlt⟩

/-- The next set, when the job is added. -/
theorem step_add (hest : EstOrdered J) {p : ℕ} {k : ℕ}
    (hk : k < J.jobs) {A Act : Finset J.Job} (hI : Inv J k A Act)
    (hcond : (((A.card : ℤ) + 1) * p ≤ s (⟨k, hk⟩ : J.Job)) ∧
      (live Act ⟨k, hk⟩).card < J.machines) :
    Step J p A (insert ⟨k, hk⟩ A) ⟨k, hk⟩ ∧
      Inv J (k + 1) (insert ⟨k, hk⟩ A) (insert ⟨k, hk⟩ (live Act ⟨k, hk⟩)) ∧
      (insert (⟨k, hk⟩ : J.Job) A).card = A.card + 1 ∧
      (insert (⟨k, hk⟩ : J.Job) (live Act ⟨k, hk⟩)).card = (live Act ⟨k, hk⟩).card + 1 := by
  have hb : ∀ i ∈ A, i < (⟨k, hk⟩ : J.Job) := fun i hi => by
    have := hI.before i hi; exact Fin.lt_def.mpr this
  have hrun := running_eq hest hb hI.sub (fun i hiA hin => hI.over i hiA hin hk)
  have hkA : (⟨k, hk⟩ : J.Job) ∉ A := fun h => by have := hI.before _ h; simp at this
  have hkL : (⟨k, hk⟩ : J.Job) ∉ live Act ⟨k, hk⟩ := fun h => hkA (hI.sub (mem_live.mp h).1)
  refine ⟨Or.inl ⟨hcond.1, by rw [hrun]; exact hcond.2, rfl⟩, ⟨?_, ?_, ?_⟩,
    Finset.card_insert_of_notMem hkA, Finset.card_insert_of_notMem hkL⟩
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp
    · have := hI.before i hi; omega
  · exact Finset.insert_subset_insert _ (fun i hi => hI.sub (mem_live.mp hi).1)
  · intro i hi hin hk1
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact absurd (Finset.mem_insert_self _ _) hin
    · have hnl : i ∉ live Act ⟨k, hk⟩ := fun h => hin (Finset.mem_insert_of_mem h)
      have hle : (J.d i : ℤ) ≤ s (⟨k, hk⟩ : J.Job) := by
        by_cases hiAct : i ∈ Act
        · by_contra hn
          exact hnl (mem_live.mpr ⟨hiAct, by omega⟩)
        · exact hI.over i hi hiAct hk
      exact hle.trans (hest ⟨k, hk⟩ ⟨k + 1, hk1⟩ (Fin.mk_le_mk.mpr (Nat.le_succ k)))

/-- The next set, when the job is added and a job of largest due date dropped. -/
theorem step_drop (hest : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) {p : ℕ} {k : ℕ}
    (hk : k < J.jobs) {A Act : Finset J.Job} (hI : Inv J k A Act)
    (hcond : s (⟨k, hk⟩ : J.Job) < ((A.card : ℤ) + 1) * p ∨
      J.machines ≤ (live Act ⟨k, hk⟩).card)
    {c : J.Job} (hc : c ∈ insert (⟨k, hk⟩ : J.Job) (live Act ⟨k, hk⟩))
    (hmax : ∀ i ∈ insert (⟨k, hk⟩ : J.Job) (live Act ⟨k, hk⟩), (J.d i : ℤ) ≤ J.d c) :
    Step J p A ((insert ⟨k, hk⟩ A).erase c) ⟨k, hk⟩ ∧
      Inv J (k + 1) ((insert ⟨k, hk⟩ A).erase c)
        ((insert ⟨k, hk⟩ (live Act ⟨k, hk⟩)).erase c) ∧
      ((insert (⟨k, hk⟩ : J.Job) A).erase c).card = A.card ∧
      ((insert (⟨k, hk⟩ : J.Job) (live Act ⟨k, hk⟩)).erase c).card = (live Act ⟨k, hk⟩).card := by
  have hb : ∀ i ∈ A, i < (⟨k, hk⟩ : J.Job) := fun i hi => by
    have := hI.before i hi; exact Fin.lt_def.mpr this
  have hrun := running_eq hest hb hI.sub (fun i hiA hin => hI.over i hiA hin hk)
  have hkA : (⟨k, hk⟩ : J.Job) ∉ A := fun h => by have := hI.before _ h; simp at this
  have hkL : (⟨k, hk⟩ : J.Job) ∉ live Act ⟨k, hk⟩ := fun h => hkA (hI.sub (mem_live.mp h).1)
  have hsk : s (⟨k, hk⟩ : J.Job) < (J.d ⟨k, hk⟩ : ℤ) := by
    have := hq ⟨k, hk⟩
    unfold s; omega
  have hLA : live Act ⟨k, hk⟩ ⊆ A := fun i hi => hI.sub (mem_live.mp hi).1
  have hcA : c ∈ insert (⟨k, hk⟩ : J.Job) A := Finset.insert_subset_insert _ hLA hc
  have hmaxA : ∀ i ∈ insert (⟨k, hk⟩ : J.Job) A, (J.d i : ℤ) ≤ J.d c := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hmax _ (Finset.mem_insert_self _ _)
    · by_cases hl : i ∈ live Act ⟨k, hk⟩
      · exact hmax i (Finset.mem_insert_of_mem hl)
      · have hle : (J.d i : ℤ) ≤ s (⟨k, hk⟩ : J.Job) := by
          by_cases hiAct : i ∈ Act
          · by_contra hn
            exact hl (mem_live.mpr ⟨hiAct, by omega⟩)
          · exact hI.over i hi hiAct hk
        have := hmax ⟨k, hk⟩ (Finset.mem_insert_self _ _)
        omega
  refine ⟨Or.inr ⟨by rw [hrun]; exact hcond, c, hcA, hmaxA, rfl⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i hi
    have hi' := (Finset.mem_erase.mp hi).2
    rcases Finset.mem_insert.mp hi' with rfl | hi'
    · simp
    · have := hI.before i hi'; omega
  · exact Finset.erase_subset_erase _ (Finset.insert_subset_insert _ hLA)
  · intro i hi hin hk1
    obtain ⟨hic, hi⟩ := Finset.mem_erase.mp hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact absurd (Finset.mem_erase.mpr ⟨hic, Finset.mem_insert_self _ _⟩) hin
    · have hnl : i ∉ live Act ⟨k, hk⟩ := fun h =>
        hin (Finset.mem_erase.mpr ⟨hic, Finset.mem_insert_of_mem h⟩)
      have hle : (J.d i : ℤ) ≤ s (⟨k, hk⟩ : J.Job) := by
        by_cases hiAct : i ∈ Act
        · by_contra hn
          exact hnl (mem_live.mpr ⟨hiAct, by omega⟩)
        · exact hI.over i hi hiAct hk
      exact hle.trans (hest ⟨k, hk⟩ ⟨k + 1, hk1⟩ (Fin.mk_le_mk.mpr (Nat.le_succ k)))
  · rw [Finset.card_erase_of_mem hcA, Finset.card_insert_of_notMem hkA]; rfl
  · rw [Finset.card_erase_of_mem hc, Finset.card_insert_of_notMem hkL]; rfl

end Lax496464Proofs.Ram.T4Model
