import Lax496464Proofs.Ram.Imp
import Lax496464.WordEncoding
import Mathlib.Data.List.GetD

/-!
# An instance as a word

The inverse of `Ram/Decode.lean`: the word a reduction has to write. `instanceWord I` is
the header followed by the four blocks, and `encodesInstance_instanceWord` says it is read
back as `I`.
-/

namespace Lax496464Proofs.Ram.InstanceWord

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.WordEncoding

variable (I : Instance)

/-- One block: a number per job, in index order. -/
def blk (f : I.Job → ℕ) : List ℕ := (List.finRange I.jobs).map f

variable {I}

@[simp] theorem length_blk (f : I.Job → ℕ) : (blk I f).length = I.jobs := by
  simp [blk]

theorem getD_blk (f : I.Job → ℕ) {j : ℕ} (hj : j < I.jobs) :
    (blk I f).getD j 0 = f ⟨j, hj⟩ := by
  simp [blk, List.getD_eq_getElem?_getD, hj]

variable (I)

/-- The word of an instance: the two counts, then the preprocessing times, the processing
times, the due dates and the weights. -/
def instanceWord : List ℕ :=
  [I.jobs, I.machines] ++ (blk I I.p ++ (blk I I.q ++ (blk I I.d ++ blk I I.w)))

/-- The word of a decision instance: the instance, then the threshold. -/
def decisionWord (W : ℕ) : List ℕ := instanceWord I ++ [W]

variable {I}

@[simp] theorem length_instanceWord : (instanceWord I).length = 2 + 4 * I.jobs := by
  simp [instanceWord]; ring

@[simp] theorem jobCount_instanceWord : jobCount (instanceWord I) = I.jobs := rfl

private theorem getD_tail {j : ℕ} :
    (instanceWord I).getD (2 + j) 0 =
      (blk I I.p ++ (blk I I.q ++ (blk I I.d ++ blk I I.w))).getD j 0 := by
  rw [instanceWord, List.getD_append_right _ _ _ _ (by simp)]
  congr 1
  simp

theorem encodesInstance_instanceWord : EncodesInstance (instanceWord I) I where
  jobCount_eq := rfl
  machineCount_eq := rfl
  length_eq := length_instanceWord
  preTime_eq := fun j => by
    rw [preTime, getD_tail, List.getD_append _ _ _ _ (by simp [j.isLt]), getD_blk _ j.isLt]
  procTime_eq := fun j => by
    have h : (2 : ℕ) + I.jobs + (j : ℕ) = 2 + (I.jobs + (j : ℕ)) := by omega
    simp only [procTime, jobCount_instanceWord, h]
    rw [getD_tail, List.getD_append_right _ _ _ _ (by simp), length_blk,
      Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by simp [j.isLt]), getD_blk _ j.isLt]
  due_eq := fun j => by
    have h : (2 : ℕ) + 2 * I.jobs + (j : ℕ) = 2 + (2 * I.jobs + (j : ℕ)) := by omega
    have h1 : 2 * I.jobs + (j : ℕ) - I.jobs = I.jobs + (j : ℕ) := by omega
    simp only [due, jobCount_instanceWord, h]
    rw [getD_tail, List.getD_append_right _ _ _ _ (by simp; omega), length_blk, h1,
      List.getD_append_right _ _ _ _ (by simp), length_blk, Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ (by simp [j.isLt]), getD_blk _ j.isLt]
  wt_eq := fun j => by
    have h : (2 : ℕ) + 3 * I.jobs + (j : ℕ) = 2 + (3 * I.jobs + (j : ℕ)) := by omega
    have h1 : 3 * I.jobs + (j : ℕ) - I.jobs = 2 * I.jobs + (j : ℕ) := by omega
    have h2 : 2 * I.jobs + (j : ℕ) - I.jobs = I.jobs + (j : ℕ) := by omega
    simp only [wt, jobCount_instanceWord, h]
    rw [getD_tail, List.getD_append_right _ _ _ _ (by simp; omega), length_blk, h1,
      List.getD_append_right _ _ _ _ (by simp; omega), length_blk, h2,
      List.getD_append_right _ _ _ _ (by simp), length_blk, Nat.add_sub_cancel_left,
      getD_blk _ j.isLt]

theorem encodesDecisionInstance_decisionWord (W : ℕ) :
    EncodesDecisionInstance (decisionWord I W) I W :=
  ⟨instanceWord I, rfl, encodesInstance_instanceWord⟩

theorem decisionWord_mem_decisionInstances (W : ℕ) :
    decisionWord I W ∈ DecisionInstances :=
  ⟨I, W, encodesDecisionInstance_decisionWord W⟩

@[simp] theorem machineCount_decisionWord (W : ℕ) :
    machineCount (decisionWord I W) = I.machines := rfl

end Lax496464Proofs.Ram.InstanceWord
