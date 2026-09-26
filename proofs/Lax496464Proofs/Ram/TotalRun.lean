import Lax496464Proofs.Ram.TotalBnd
import Lax496464Proofs.Ram.Fits

/-!
# `totalProg` on every tape, case by case

The word bound `Bd y` and the three runs of `totalProg` that the `Solves` statement of
`Ram/TotalFinal.lean` combines: on a tape whose scan never finishes
(`totalProg_run_of_unfinished`), on one whose scan finishes but fails `validate`
(`totalProg_run_of_invalid`), and on a valid one (`totalProg_run_of_valid`). The bound
`Mbd y = 2 ^ (66 · (|y| + 3)) + maxEntry y + 1` is chosen before the case is known: it bounds
every entry of `y`, and it dominates the fields of `Gen.Bnd` for the recovered instance
(`TotalBnd.bnd_of_expBd`).
-/

namespace Lax496464Proofs.Ram.TotalRun

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.HittingSet Lax496464.Construction
open Lax496464Proofs.Ram.ScanModel (run init wordBound Bounded run_offs_length_of_done
  run_mems_length_of_done run_offs_last_eq_off_of_done run_encodeInstance)
open Lax496464Proofs.Ram.Fits (maxEntry le_maxEntry)
open Lax496464Proofs.Ram.TotalProg (totalProg totalProg_spec_reject_unfinished
  totalProg_spec_reject_invalid totalProg_spec_valid decY ValidY)
open Lax496464Proofs.Ram.TotalReduction (f f_eq_reject_unfinished f_eq_reject_invalid f_eq_valid
  admissible_decY)
open Lax496464Proofs.Ram.TotalBnd (ExpBd bnd_of_expBd)
open Lax496464Proofs.Ram.Gen (Bnd)
open Lax496464Proofs.Ram.CsrWord (csrWord offsetsOf membersOf offset_csrWord member_csrWord
  offset_csrWord_last csrWord_decodeInstance_eq)
open Lax496464Proofs.Ram.InstanceWord (decisionWord)
open Lax496464Proofs.Ram.BitsNat (natBits)

/-- The value bound `M` for a tape `y`: it bounds every entry of `y` (`maxEntry y`), and it is at
least `2 ^ (66 · (|y| + 3))`, so that `TotalBnd.bnd_of_expBd` applies to the instance the scan
recovers. -/
noncomputable def Mbd (y : List ℕ) : ℕ := 2 ^ (66 * (y.length + 3)) + maxEntry y + 1

noncomputable def Bd (y : List ℕ) : ℕ := wordBound (Mbd y) y.length

theorem hlM_Mbd (y : List ℕ) : ∀ v ∈ y, v ≤ Mbd y := by
  intro v hv
  have h1 := le_maxEntry hv
  have h2 : (0 : ℕ) ≤ 2 ^ (66 * (y.length + 3)) := Nat.zero_le _
  show v ≤ 2 ^ (66 * (y.length + 3)) + maxEntry y + 1
  omega

theorem Bd_gt_two (y : List ℕ) : 2 < Bd y := by
  unfold Bd
  simp only [ScanModel.wordBound]
  omega

/-- The array lengths the front end of `totalProg` needs, uniformly across every case —
`bridgeCopy`/`progTail`'s own arrays (`OFF`/`MEM`/`MJ`/`MI`/`PA`/`QA`/`DA`) are given harmless
placeholder lengths here since a tape whose scan never finishes never reaches them. -/
noncomputable def extBase (y : List ℕ) : String → ℕ :=
  fun a => if a = "a" then y.length else if a = "OFFS" then y.length + 2
    else if a = "MEMS" then Bd y else 0

theorem totalProg_run_of_unfinished (y : List ℕ) (hnot2 : (run init y).ph ≠ 2) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (Bd y) totalProg (initEnv ext (y.length :: y)) σ'
        (12 * y.length + 10 + 30 + (2220 * y.length + 6) + 30) ∧
      σ'.out = f y := by
  obtain ⟨σ', hrun, hout⟩ :=
    totalProg_spec_reject_unfinished (M := Mbd y) (B := Bd y) y (hlM_Mbd y) rfl (Bd_gt_two y)
      hnot2 (σ0 := initEnv (extBase y) (y.length :: y)) rfl rfl
      (by simp [initEnv, extBase]) (by simp [initEnv, extBase]) (by simp [initEnv, extBase])
  refine ⟨extBase y, σ', hrun, ?_⟩
  rw [hout, f_eq_reject_unfinished hnot2]

/-! ## The finished-but-invalid case

`wordBound M L := L*(L*M*2^L) + L*M*2^L + M*2^L + L + 10` turns out to be *exactly* shaped to
dominate `ScanModel.Bounded`'s own clauses at `i = L`: `Bounded`'s `offs`/`off` bound is
`i*(i*M*2^L)` — `wordBound`'s own first term; its `n`/`m`/`k`/`sz`/`mems` bound is `i*M*2^L` —
`wordBound`'s own second term — so every one of `n`, `k`, and every entry of `offs`/`mems` is
`< wordBound M L` with the whole remaining `M*2^L + L + 10` left over as slack. No new numeric
work beyond reading `Bounded`/`wordBound`'s two definitions side by side. -/

theorem run_bounds (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ Mbd y) (hdone : (run init y).ph = 2) :
    (run init y).n < Bd y ∧ (run init y).m < Bd y ∧ (run init y).k < Bd y ∧
      (run init y).off + 1 < Bd y ∧
      (∀ j ≤ (run init y).m, (run init y).offs.getD j 0 + 1 < Bd y) ∧
      (∀ t < (run init y).off, (run init y).mems.getD t 0 + 1 < Bd y) := by
  have hb := Bounded.run_take (Bounded.init (Mbd y) y.length) y hlM le_rfl y.length le_rfl
  rw [List.take_length] at hb
  obtain ⟨-, -, -, -, -, hn, hm, hk, -, hoff, hoffslen, hmemslen, hoffsmem, hmemsmem⟩ := hb
  have hoffslen' : (run init y).offs.length = (run init y).m + 1 := run_offs_length_of_done y hdone
  have hmemslen' : (run init y).mems.length = (run init y).off := run_mems_length_of_done y hdone
  have hBdeq : Bd y = wordBound (Mbd y) y.length := rfl
  refine ⟨by rw [hBdeq]; unfold ScanModel.wordBound; omega,
    by rw [hBdeq]; unfold ScanModel.wordBound; omega,
    by rw [hBdeq]; unfold ScanModel.wordBound; omega,
    by rw [hBdeq]; unfold ScanModel.wordBound; omega, ?_, ?_⟩
  · intro j hj
    have hjlt : j < (run init y).offs.length := by omega
    have hmem : (run init y).offs.getD j 0 ∈ (run init y).offs := by
      rw [List.getD_eq_getElem _ _ hjlt]
      exact List.getElem_mem hjlt
    have := hoffsmem _ hmem
    rw [hBdeq]; unfold ScanModel.wordBound; omega
  · intro t ht
    have htlt : t < (run init y).mems.length := by omega
    have hmem : (run init y).mems.getD t 0 ∈ (run init y).mems := by
      rw [List.getD_eq_getElem _ _ htlt]
      exact List.getElem_mem htlt
    have := hmemsmem _ hmem
    rw [hBdeq]; unfold ScanModel.wordBound; omega

/-- The membership-shaped companion to `run_bounds`'s indexed `hOffValB`/`hMemValB` — the same
`Bounded` clauses, read off directly without first converting to the indexed form. Needed for
`csrWord_bounds`'s `hxB` (`∀v∈csrWord P k,...`, a membership statement, not an indexed one). -/
theorem run_bounds_mem (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ Mbd y) :
    (∀ x ∈ (run init y).offs, x + 1 < Bd y) ∧ (∀ x ∈ (run init y).mems, x + 1 < Bd y) := by
  have hb := Bounded.run_take (Bounded.init (Mbd y) y.length) y hlM le_rfl y.length le_rfl
  rw [List.take_length] at hb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hoffsmem, hmemsmem⟩ := hb
  have hBdeq : Bd y = wordBound (Mbd y) y.length := rfl
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have := hoffsmem x hx; rw [hBdeq]; unfold ScanModel.wordBound; omega
  · have := hmemsmem x hx; rw [hBdeq]; unfold ScanModel.wordBound; omega

/-- **The combined word-fitting bound `checkUniverseBound` needs.** `(run init y).m` plus the
scan's own `off` counter, with four to spare, stays below `Bd y` — the same two `Bounded`
clauses `run_bounds` reads individually (its `hm`, `hoff`), combined in one `omega` call: not
just each alone, but their sum too, is dominated by `wordBound`'s own bigger terms. -/
theorem run_bounds_sum (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ Mbd y) :
    (run init y).m + (run init y).off + 4 < Bd y := by
  have hb := Bounded.run_take (Bounded.init (Mbd y) y.length) y hlM le_rfl y.length le_rfl
  rw [List.take_length] at hb
  obtain ⟨-, -, -, -, -, -, hm, -, -, hoff, -, -, -, -⟩ := hb
  have hBdeq : Bd y = wordBound (Mbd y) y.length := rfl
  rw [hBdeq]; unfold ScanModel.wordBound; omega

/-- The array lengths `totalProg` needs when the scan finishes but the result is invalid: as
`extBase`, plus `"OFF"`/`"MEM"` sized exactly to what `bridgeCopy` actually copies. -/
noncomputable def extInvalid (y : List ℕ) : String → ℕ :=
  fun a => if a = "OFF" then (run init y).m + 1 else if a = "MEM" then (run init y).off
    else extBase y a

theorem totalProg_run_of_invalid (y : List ℕ) (hdone : (run init y).ph = 2)
    (hnotvalid : ¬ ((run init y).offs.getD 0 0 = 0 ∧
        Lax496464Proofs.Ram.Validate.OffsetsOkG (fun j => (run init y).offs.getD j 0)
          (run init y).m ∧
        Lax496464Proofs.Ram.Validate.MembersOkG (fun t => (run init y).mems.getD t 0)
          (run init y).n ((run init y).offs.getD (run init y).m 0) ∧
        Lax496464Proofs.Ram.Validate.SortedOkG (fun j => (run init y).offs.getD j 0)
          (fun t => (run init y).mems.getD t 0) (run init y).m
          ((run init y).offs.getD (run init y).m 0) ∧
        (run init y).n ≤ (run init y).m + (run init y).offs.getD (run init y).m 0 + 4 ∧
        2 ≤ (run init y).k ∧ (run init y).k ≤ (run init y).n)) :
    ∃ (ext : String → ℕ) (σ' : Env), Run (Bd y) totalProg (initEnv ext (y.length :: y)) σ'
        (12 * y.length + 10 + 30 + (2220 * y.length + 6) +
          (((1 + 4) + ((1 + 3 + 4 + 4) * ((run init y).m + 1) + 6) + (1 + 4) +
              ((1 + 3 + 4 + 4) * (run init y).off + 6)) +
            (2 + 7 + (18 * (run init y).m + 6) + (18 * (run init y).off + 9) +
                (34 * (run init y).off + 34 * (run init y).m + 20) + 13 + 6 + 6) + 20) +
          60) ∧
      σ'.out = f y := by
  obtain ⟨hnB, -, hkB, -, hOffValB, hMemValB⟩ := run_bounds y (hlM_Mbd y) hdone
  have hnmB := run_bounds_sum y (hlM_Mbd y)
  obtain ⟨σ', hrun, hout⟩ :=
    totalProg_spec_reject_invalid (M := Mbd y) (B := Bd y) y (hlM_Mbd y) rfl (Bd_gt_two y) hdone
      hnotvalid hnB hkB hOffValB hMemValB hnmB (σ0 := initEnv (extInvalid y) (y.length :: y))
      (by simp [initEnv]; have := Bd_gt_two y; omega) rfl rfl
      (by simp [initEnv, extInvalid, extBase]) (by simp [initEnv, extInvalid, extBase])
      (by simp [initEnv, extInvalid, extBase]) (by simp [initEnv, extInvalid])
      (by simp [initEnv, extInvalid])
  refine ⟨extInvalid y, σ', hrun, ?_⟩
  rw [hout, f_eq_reject_invalid hdone hnotvalid]

/-! ## The valid case

Any tape the scan finishes on and `validate` accepts — a canonical encoding, or one with
trailing padding, or any other tape scanning to such a state. The instance is `decY y`, read
off the scan; the tape's *own* length controls its size (`n ≤ m + off + 4 ≤ 2·length + 4`,
`m`, `off ≤ length`), which is what makes `Bnd`'s quartic-and-up quantities dominated by
`Bd y` for `Mbd y`'s `2 ^ (66 * (length + 3))`. -/

/-- The scan's own bookkeeping never outgrows the tape: `m` and `off` are at most its length. -/
theorem run_len_bounds (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ Mbd y) (hdone : (run init y).ph = 2) :
    (run init y).m ≤ y.length ∧ (run init y).off ≤ y.length := by
  have hb := Bounded.run_take (Bounded.init (Mbd y) y.length) y hlM le_rfl y.length le_rfl
  rw [List.take_length] at hb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hoffslenb, hmemslenb, -, -⟩ := hb
  have h1 : (run init y).offs.length = (run init y).m + 1 := run_offs_length_of_done y hdone
  have h2 : (run init y).mems.length = (run init y).off := run_mems_length_of_done y hdone
  omega

theorem lt_two_pow_len {L N : ℕ} (h : N ≤ 2 * L + 4) : N < 2 ^ (L + 3) := by
  have h1 : L < 2 ^ L := Nat.lt_two_pow_self
  have h2 : (2 : ℕ) ^ (L + 3) = 8 * 2 ^ L := by rw [pow_add]; ring
  omega

/-- **`decY y` has `n`, `m`, `k` below `2 ^ (length + 3)`**, from `validate`'s own
`n ≤ m + off + 4` together with the scan's `m`, `off ≤ length`. -/
theorem expBd_decY (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ Mbd y) (hv : ValidY y) :
    ExpBd (decY y) (run init y).k (y.length + 3) := by
  obtain ⟨hdone, -, -, -, -, hnm, -, hkn⟩ := hv
  obtain ⟨hm, hoff⟩ := run_len_bounds y hlM hdone
  have hfoffm : (run init y).offs.getD (run init y).m 0 = (run init y).off :=
    run_offs_last_eq_off_of_done y hdone
  rw [hfoffm] at hnm
  refine ⟨?_, ?_, ?_⟩
  · exact lt_two_pow_len (N := (run init y).n) (by omega)
  · exact lt_two_pow_len (N := (run init y).m) (by omega)
  · exact lt_two_pow_len (N := (run init y).k) (by omega)

theorem bnd_decY (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ Mbd y) (hv : ValidY y) :
    Bnd (decY y) (run init y).k (Bd y) :=
  bnd_of_expBd (admissible_decY hv) (expBd_decY y hlM hv) (by unfold Mbd; omega)

/-- Every entry of the recovered `csrWord` is below `Bd y`: it is `[n, m] ++ offs ++ mems ++
[k]` (`csrWord_decodeInstance_eq`), each piece bounded by `run_bounds`/`run_bounds_mem`. -/
theorem csrWord_bounds_valid (y : List ℕ) (hlM : ∀ v ∈ y, v ≤ Mbd y) (hv : ValidY y) :
    ∀ v ∈ csrWord (decY y) (run init y).k, v < Bd y := by
  obtain ⟨hdone, hoff0, hOff, hMem, hSorted, -, -, -⟩ := hv
  obtain ⟨hnB, hmB, hkB, -, -, -⟩ := run_bounds y hlM hdone
  obtain ⟨hoffsMemB, hmemsMemB⟩ := run_bounds_mem y hlM
  have hlo : (run init y).offs.length = (run init y).m + 1 := run_offs_length_of_done y hdone
  have hlm : (run init y).mems.length = (run init y).offs.getD (run init y).m 0 := by
    rw [run_mems_length_of_done y hdone, run_offs_last_eq_off_of_done y hdone]
  have hcsr : csrWord (decY y) (run init y).k =
      [(run init y).n, (run init y).m] ++ (run init y).offs ++ (run init y).mems ++
        [(run init y).k] :=
    csrWord_decodeInstance_eq (fun j => (run init y).offs.getD j 0)
      (fun t => (run init y).mems.getD t 0) (run init y).n (run init y).m hoff0 hOff hMem hSorted
      (run init y).offs (run init y).mems hlo (fun j => rfl) hlm (fun t => rfl) _
  intro v hv'
  rw [hcsr] at hv'
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv'
  rcases hv' with (((rfl | rfl) | hv') | hv'') | rfl
  · exact hnB
  · exact hmB
  · have := hoffsMemB v hv'; omega
  · have := hmemsMemB v hv''; omega
  · exact hkB

/-- The array lengths `totalProg` needs on a valid tape. -/
noncomputable def extValid (y : List ℕ) : String → ℕ :=
  fun a => if a = "OFF" then (run init y).m + 1 else if a = "MEM" then (run init y).off
    else if a = "MJ" ∨ a = "MI" then (run init y).n * (run init y).m
    else if a = "PA" ∨ a = "QA" ∨ a = "DA" then numJobs (decY y) (run init y).k
    else extBase y a

/-- **The valid case of `totalProg_run`.** -/
theorem totalProg_run_of_valid (y : List ℕ) (hv : ValidY y) :
    ∃ (σ' : Env),
      Run (Bd y) totalProg (initEnv (extValid y) (y.length :: y)) σ'
        (12 * y.length + 10 + 30 + (2220 * y.length + 6) +
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
                4 * ((42 * (Bd y).size + 31 + 4) * numJobs (decY y) (run init y).k + 6) + 30))))) ∧
      σ'.out = f y := by
  have hv0 := hv
  obtain ⟨hdone, -, -, -, -, -, -, -⟩ := hv0
  obtain ⟨hnB, -, hkB, -, hOffValB, hMemValB⟩ := run_bounds y (hlM_Mbd y) hdone
  have hnmB := run_bounds_sum y (hlM_Mbd y)
  obtain ⟨σ', hrun, hout⟩ :=
    totalProg_spec_valid (M := Mbd y) (B := Bd y) y (hlM_Mbd y) rfl (Bd_gt_two y) hv
      hnB hkB hOffValB hMemValB hnmB (bnd_decY y (hlM_Mbd y) hv)
      (csrWord_bounds_valid y (hlM_Mbd y) hv) (σ0 := initEnv (extValid y) (y.length :: y))
      (by simp [initEnv]; have := Bd_gt_two y; omega) rfl rfl
      (by simp [initEnv, extValid, extBase]) (by simp [initEnv, extValid, extBase])
      (by simp [initEnv, extValid, extBase]) (by simp [initEnv, extValid])
      (by simp [initEnv, extValid]) (by simp [initEnv, extValid]) (by simp [initEnv, extValid])
      (by simp [initEnv, extValid]) (by simp [initEnv, extValid]) (by simp [initEnv, extValid])
  refine ⟨σ', hrun, ?_⟩
  rw [hout, f_eq_valid hv]

end Lax496464Proofs.Ram.TotalRun
