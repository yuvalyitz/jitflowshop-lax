import Lax496464Proofs.Ram.TotalRun
import Lax496464Proofs.Ram.CsrWord

/-!
# The Polynomial Bound on `totalProg`'s Running Time

`totalProg`'s cost, in each of its three cases, as a polynomial in the tape length and in the
bit-length `S` of the word bound `Bd y`. The dominant case is the valid one: the same
`costBuild`/`costDum` shape as `Corollary4.costN`, with the bit-printing stage's `S`-dependent
cost in place of the raw writes.
-/

namespace Lax496464Proofs.Ram.TotalCost

open Lax496464Proofs.Ram.Gen (costDum costJBody)

/-- The valid case's `progTail` cost, as a function of the numbers it depends on. -/
def costTail (n m L Lc R nj S : ℕ) : ℕ :=
  Lax496464Proofs.Ram.Build.costBuild n m L +
    (100 + ((2 + (((400 + 4) * Lc + 6 + 4 + 4) * R + 6)) +
      (costDum n m R + costDum n m R) +
      (3 * (42 * S + 26) + 4 * ((42 * S + 31 + 4) * nj + 6) + 30)))

theorem costTail_le (s S n m L Lc R nj : ℕ) (hs : 1 ≤ s) (hn : n ≤ s) (hm : m ≤ s) (hL : L ≤ s)
    (hLc : Lc ≤ s * s) (hR : R ≤ 3 * (s * s)) (hnj : nj ≤ 9 * (s * s * s * s)) :
    costTail n m L Lc R nj S ≤ 20000 * (s * s * s * s) * (S + 1) := by
  have h1 : costTail n m L Lc R nj S ≤
      costTail s s s (s * s) (3 * (s * s)) (9 * (s * s * s * s)) S := by
    unfold costTail Lax496464Proofs.Ram.Build.costBuild Lax496464Proofs.Ram.Build.costI costDum
      costJBody
    gcongr
  refine h1.trans ?_
  unfold costTail Lax496464Proofs.Ram.Build.costBuild Lax496464Proofs.Ram.Build.costI costDum
    costJBody
  have e1 : s ≤ s * s := Nat.le_mul_of_pos_right _ hs
  have e2 : s * s ≤ s * s * s := Nat.le_mul_of_pos_right _ hs
  have e3 : s * s * s ≤ s * s * s * s := Nat.le_mul_of_pos_right _ hs
  have e4 : 1 ≤ s * s * s * s := by nlinarith
  nlinarith [e1, e2, e3, hs, e4, Nat.zero_le S, Nat.mul_le_mul_right S e4]

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet Lax496464.Construction
open Lax496464Proofs.Ram.ScanModel (run init run_offs_last_eq_off_of_done)
open Lax496464Proofs.Ram.TotalProg (totalProg decY ValidY encodes_decY)
open Lax496464Proofs.Ram.TotalReduction (f)
open Lax496464Proofs.Ram.TotalRun
open Lax496464Proofs.Ram.CsrWord (csrWord membersOf getD_csrWord_n setCount_csrWord
  offset_csrWord_last)
open Lax496464Proofs.Ram.Program (length_memberList_le)

/-- The one polynomial bounding `totalProg`'s cost, at scale `s` (`s = 2L + 4` for a tape of
length `L`) and `S` the bit-length of the word bound. -/
def Kc (s S : ℕ) : ℕ := 20000 * (s * s * s * s) * (S + 1) + 3000 * s

theorem valid_cost_le (y : List ℕ) (hv : ValidY y) :
    12 * y.length + 10 + 30 + (2220 * y.length + 6) +
        (((1 + 4) + ((1 + 3 + 4 + 4) * ((run init y).m + 1) + 6) + (1 + 4) +
            ((1 + 3 + 4 + 4) * (run init y).off + 6)) +
          (2 + 7 + (18 * (run init y).m + 6) + (18 * (run init y).off + 9) +
              (34 * (run init y).off + 34 * (run init y).m + 20) + 13 + 6 + 6) + 20) +
        (Lax496464Proofs.Ram.Build.costBuild (universeSize (csrWord (decY y) (run init y).k))
            (setCount (csrWord (decY y) (run init y).k))
            (offset (csrWord (decY y) (run init y).k)
              (setCount (csrWord (decY y) (run init y).k))) +
          (100 + ((2 + (((400 + 4) * (memberList (decY y)).length + 6 + 4 + 4) *
              R (decY y) (run init y).k + 6)) +
            (Lax496464Proofs.Ram.Gen.costDum (decY y).n (decY y).m (R (decY y) (run init y).k) +
              Lax496464Proofs.Ram.Gen.costDum (decY y).n (decY y).m
                (R (decY y) (run init y).k)) +
            (3 * (42 * (Bd y).size + 26) +
              4 * ((42 * (Bd y).size + 31 + 4) * numJobs (decY y) (run init y).k + 6) + 30)))) ≤
      Kc (2 * y.length + 4) (Bd y).size := by
  have hv' := hv
  obtain ⟨hdone, hoff0, hOff, hMem, hSorted, hnm, hk2, hkn⟩ := hv'
  obtain ⟨hm, hoff⟩ := run_len_bounds y (hlM_Mbd y) hdone
  have hE := encodes_decY hv
  have hfoffm : (run init y).offs.getD (run init y).m 0 = (run init y).off :=
    run_offs_last_eq_off_of_done y hdone
  rw [hfoffm] at hnm
  have hPn : (decY y).n = (run init y).n := rfl
  have hPm : (decY y).m = (run init y).m := rfl
  have hn : (decY y).n ≤ 2 * y.length + 4 := by rw [hPn]; omega
  have hm' : (decY y).m ≤ 2 * y.length + 4 := by rw [hPm]; omega
  have hL' : (run init y).off ≤ 2 * y.length + 4 := by omega
  have hkP : (run init y).k ≤ (decY y).n := hkn
  have hs1 : 1 ≤ 2 * y.length + 4 := by omega
  have hmemlen : (membersOf (decY y)).length = (run init y).off := by
    have := Lax496464Proofs.Ram.CsrWord.membersOf_length_decodeInstance
      (fun j => (run init y).offs.getD j 0) (fun t => (run init y).mems.getD t 0)
      (run init y).n (run init y).m hoff0 hOff hMem hSorted
    rw [hfoffm] at this; exact this
  have hu : universeSize (csrWord (decY y) (run init y).k) = (decY y).n := getD_csrWord_n
  have hsc : setCount (csrWord (decY y) (run init y).k) = (decY y).m := setCount_csrWord
  have ho : offset (csrWord (decY y) (run init y).k) (decY y).m = (run init y).off := by
    rw [offset_csrWord_last, hmemlen]
  have hLc : (memberList (decY y)).length ≤ (2 * y.length + 4) * (2 * y.length + 4) :=
    (length_memberList_le hE).trans (Nat.mul_le_mul hn hm')
  have hR : R (decY y) (run init y).k ≤ 3 * ((2 * y.length + 4) * (2 * y.length + 4)) := by
    have h1 : (run init y).k * ((decY y).n - 1) ≤ (decY y).n * (decY y).n :=
      Nat.mul_le_mul hkP (by omega)
    have h2 : (decY y).n * (decY y).n ≤ (2 * y.length + 4) * (2 * y.length + 4) :=
      Nat.mul_le_mul hn hn
    have h3 : 1 ≤ (2 * y.length + 4) * (2 * y.length + 4) := by nlinarith
    unfold R; omega
  have hnj : numJobs (decY y) (run init y).k ≤
      9 * ((2 * y.length + 4) * (2 * y.length + 4) * (2 * y.length + 4) * (2 * y.length + 4)) := by
    have h1 : selCount (decY y) (run init y).k ≤
        3 * ((2 * y.length + 4) * (2 * y.length + 4)) * ((2 * y.length + 4) * (2 * y.length + 4)) :=
      Nat.mul_le_mul hR hLc
    have h2 : dumCount (decY y) (run init y).k ≤
        3 * ((2 * y.length + 4) * (2 * y.length + 4)) * (2 * y.length + 4) *
          (2 * y.length + 4) :=
      Nat.mul_le_mul (Nat.mul_le_mul hR hm') hn
    simp only [numJobs]
    nlinarith [h1, h2]
  have hT := costTail_le (2 * y.length + 4) (Bd y).size (decY y).n (decY y).m (run init y).off
    (memberList (decY y)).length (R (decY y) (run init y).k)
    (numJobs (decY y) (run init y).k) hs1 hn hm' hL' hLc hR hnj
  unfold costTail at hT
  rw [hsc, ho, hu]
  unfold Kc
  omega

/-- **`totalProg` runs within `Kc`, and computes `f`, on every tape.** -/
theorem totalProg_run (y : List ℕ) :
    ∃ (ext : String → ℕ) (σ' : Env),
      Run (Bd y) totalProg (initEnv ext (y.length :: y)) σ' (Kc (2 * y.length + 4) (Bd y).size) ∧
      σ'.out = f y := by
  by_cases hv : ValidY y
  · obtain ⟨σ', hrun, hout⟩ := totalProg_run_of_valid y hv
    exact ⟨extValid y, σ', hrun.mono (valid_cost_le y hv), hout⟩
  · by_cases hdone : (run init y).ph = 2
    · have hnotvalid : ¬ ((run init y).offs.getD 0 0 = 0 ∧
          Lax496464Proofs.Ram.Validate.OffsetsOkG (fun j => (run init y).offs.getD j 0)
            (run init y).m ∧
          Lax496464Proofs.Ram.Validate.MembersOkG (fun t => (run init y).mems.getD t 0)
            (run init y).n ((run init y).offs.getD (run init y).m 0) ∧
          Lax496464Proofs.Ram.Validate.SortedOkG (fun j => (run init y).offs.getD j 0)
            (fun t => (run init y).mems.getD t 0) (run init y).m
            ((run init y).offs.getD (run init y).m 0) ∧
          (run init y).n ≤ (run init y).m + (run init y).offs.getD (run init y).m 0 + 4 ∧
          2 ≤ (run init y).k ∧ (run init y).k ≤ (run init y).n) := fun h => hv ⟨hdone, h⟩
      obtain ⟨ext, σ', hrun, hout⟩ := totalProg_run_of_invalid y hdone hnotvalid
      refine ⟨ext, σ', hrun.mono ?_, hout⟩
      obtain ⟨hm, hoff⟩ := run_len_bounds y (hlM_Mbd y) hdone
      unfold Kc
      have hp : 0 < 2 * y.length + 4 := by omega
      have h4 : 1 ≤ (2 * y.length + 4) * (2 * y.length + 4) * (2 * y.length + 4) *
          (2 * y.length + 4) := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp hp) hp) hp
      have h5 := Nat.mul_le_mul_right ((Bd y).size + 1) h4
      omega
    · obtain ⟨ext, σ', hrun, hout⟩ := totalProg_run_of_unfinished y hdone
      refine ⟨ext, σ', hrun.mono ?_, hout⟩
      unfold Kc
      omega

end Lax496464Proofs.Ram.TotalCost
