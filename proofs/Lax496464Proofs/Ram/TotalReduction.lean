import Lax496464Proofs.Ram.TotalProg
import Lax496464Proofs.Ram.Reduction
import Lax496464Proofs.Ram.Validate
import Lax496464Proofs.Ram.DecodeInstance

/-!
# The Reduction, as a Total Function of the Bit Tape

`Lax759944.RamPolytime` needs a function `f : List ℕ → List ℕ` that `totalProg` computes. It is
built here from what the scan recovers: `TotalProg.decY y` is the instance read off the scan's
final state (`DecodeInstance.decodeInstance`), and `f y` is the decision word of that instance
when the scan finished and `validate`'s conditions hold (`TotalProg.ValidY`), and the fixed word
of the empty instance otherwise — `totalProg`'s own two-way split.

Defining `f` from the recovered state, rather than by an existential over canonical encodings,
makes it agree with `totalProg` also on a tape with trailing padding, which scans to the same
state (`ScanModel.step` is a no-op once `ph = 2`). On a canonical tape
`natBits (encodeInstance P k)` the recovered instance is `P` itself (`f_eq`).
-/

namespace Lax496464Proofs.Ram.TotalReduction

open Lax496464.HittingSet Lax496464.Construction
open Lax496464Proofs.Ram.ScanModel (run init run_encodeInstance run_offs_length_of_done
  run_mems_length_of_done run_offs_last_eq_off_of_done)
open Lax496464Proofs.Ram.TotalProg (decY ValidY encodes_decY)
open Lax496464Proofs.Ram.CsrWord (csrWord offsetsOf membersOf csrWord_decodeInstance_eq offset_csrWord
  offset_csrWord_last member_csrWord member_csrWord_strictMono_of_sameBlock offset_csrWord_mono)
open Lax496464Proofs.Ram.BitsNat (natBits bitsNat)
open Lax496464Proofs.Ram.InstanceWord (decisionWord)
open Lax496464Proofs.Ram.Reduction (encodes_unique)
open Lax496464Proofs.Ram.Validate (OffsetsOkG MembersOkG SortedOkG SameBlockG)

/-- The three hypotheses `CsrWord.encodes_csrWord` needs to turn `csrWord P k` into a genuine
`Encodes` witness. -/
def Admissible (P : Instance) (k : ℕ) : Prop :=
  2 ≤ k ∧ k ≤ P.n ∧ P.n ≤ (csrWord P k).length

theorem encodes_of_admissible {P : Instance} {k : ℕ} (h : Admissible P k) :
    Encodes (csrWord P k) P k :=
  Lax496464Proofs.Ram.CsrWord.encodes_csrWord h.1 h.2.1 h.2.2

open Classical in
/-- **The reduction, as a total function of the bit tape.** The decision word of the instance
the scan recovers, each number in its self-delimiting code (`bitsNat`, so the output is zeros
and ones — what the Turing-machine composition needs), when the scan finished and `validate`'s seven conditions hold; the fixed
word of the empty instance otherwise. -/
noncomputable def f (y : List ℕ) : List ℕ :=
  if ValidY y then
    (decisionWord (construct (decY y) (run init y).k)
      (target (decY y) (run init y).k)).flatMap bitsNat
  else [0, 0, 0]

theorem f_eq_valid {y : List ℕ} (h : ValidY y) :
    f y = (decisionWord (construct (decY y) (run init y).k)
      (target (decY y) (run init y).k)).flatMap bitsNat := by
  rw [f, if_pos h]

theorem f_eq_reject {y : List ℕ} (h : ¬ ValidY y) : f y = [0, 0, 0] := by
  rw [f, if_neg h]

/-- A tape whose scan never finishes is rejected. -/
theorem f_eq_reject_unfinished {y : List ℕ} (hnot2 : (run init y).ph ≠ 2) : f y = [0, 0, 0] :=
  f_eq_reject fun h => hnot2 h.1

/-- A tape whose scan finishes but fails `validate` is rejected. -/
theorem f_eq_reject_invalid {y : List ℕ} (_hdone : (run init y).ph = 2)
    (hnotvalid : ¬ ((run init y).offs.getD 0 0 = 0 ∧
        OffsetsOkG (fun j => (run init y).offs.getD j 0) (run init y).m ∧
        MembersOkG (fun t => (run init y).mems.getD t 0) (run init y).n
          ((run init y).offs.getD (run init y).m 0) ∧
        SortedOkG (fun j => (run init y).offs.getD j 0) (fun t => (run init y).mems.getD t 0)
          (run init y).m ((run init y).offs.getD (run init y).m 0) ∧
        (run init y).n ≤ (run init y).m + (run init y).offs.getD (run init y).m 0 + 4 ∧
        2 ≤ (run init y).k ∧ (run init y).k ≤ (run init y).n)) :
    f y = [0, 0, 0] :=
  f_eq_reject fun h => hnotvalid h.2

/-- What the recovered instance's own `Admissible` says: `Encodes` (`encodes_decY`) already
packages `2 ≤ k`, `k ≤ n` and `n ≤ length`. -/
theorem admissible_decY {y : List ℕ} (hv : ValidY y) : Admissible (decY y) (run init y).k := by
  have hE := encodes_decY hv
  exact ⟨hE.size_bounds.1, hE.size_bounds.2, hE.universeSize_le⟩

/-- **A canonical, admissible encoding is `ValidY`.** The scan finishes (`run_encodeInstance`)
and `Encodes (csrWord P k) P k` gives each of `validate`'s seven checks, translated from
`offset (csrWord P k)`/`member (csrWord P k)` to the scan's own `offs.getD`/`mems.getD`. -/
theorem valid_of_admissible {P : Instance} {k : ℕ} (hAdm : Admissible P k) :
    ValidY (natBits (encodeInstance P k)) := by
  obtain ⟨hph, hn, hm, hk, hoffs, hmems⟩ := run_encodeInstance P k
  have hE : Encodes (csrWord P k) P k := encodes_of_admissible hAdm
  have hfoff : ∀ j ≤ P.m,
      (run init (natBits (encodeInstance P k))).offs.getD j 0 = offset (csrWord P k) j := by
    intro j hj; rw [hoffs]; exact (offset_csrWord hj).symm
  have hfmem : ∀ t < (membersOf P).length,
      (run init (natBits (encodeInstance P k))).mems.getD t 0 = member (csrWord P k) t := by
    intro t ht; rw [hmems]; exact (member_csrWord ht).symm
  have hfoffm : (run init (natBits (encodeInstance P k))).offs.getD
      (run init (natBits (encodeInstance P k))).m 0 = (membersOf P).length := by
    rw [hm, hfoff P.m le_rfl, offset_csrWord_last]
  have hoffPm : offset (csrWord P k) P.m = (membersOf P).length := offset_csrWord_last
  refine ⟨hph, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfoff 0 (by omega)]; exact hE.offset_zero
  · intro i hi
    dsimp only
    rw [hm] at hi
    rw [hfoff i (by omega), hfoff (i + 1) (by omega)]
    exact hE.offset_mono i hi
  · rw [hfoffm]
    intro u hu
    dsimp only
    rw [hn, hfmem u hu]
    exact hE.member_lt u (hoffPm ▸ hu)
  · rw [hfoffm]
    intro s hs hsb
    obtain ⟨jj, hjjm, hlo, hhi⟩ := hsb
    dsimp only at hjjm hlo hhi ⊢
    rw [hm] at hjjm
    have hlo' : offset (csrWord P k) jj ≤ s := by rw [← hfoff jj (by omega)]; exact hlo
    have hhi' : s + 1 < offset (csrWord P k) (jj + 1) := by
      rw [← hfoff (jj + 1) (by omega)]; exact hhi
    have hstep := member_csrWord_strictMono_of_sameBlock hjjm hlo' hhi'
    have hoffle : offset (csrWord P k) (jj + 1) ≤ offset (csrWord P k) P.m :=
      offset_csrWord_mono (by omega) (by omega)
    rw [hoffPm] at hoffle
    rw [hfmem s (by omega), hfmem (s + 1) (by omega)]
    exact hstep
  · rw [hn, hfoffm, hm]
    have hle := hE.universeSize_le
    rw [hE.length_eq] at hle
    omega
  · rw [hk]; exact hAdm.1
  · rw [hk, hn]; exact hAdm.2.1

/-- **On a canonical, admissible encoding, `f` is the reduction's own decision word.** The scan
recovers `csrWord P k`'s pieces verbatim (`run_encodeInstance`), so `decY` reassembles the very
same `csrWord`, and `encodes_unique` identifies the two instances. -/
theorem f_eq {P : Instance} {k : ℕ} (hAdm : Admissible P k) :
    f (natBits (encodeInstance P k)) =
      (decisionWord (construct P k) (target P k)).flatMap bitsNat := by
  have hv := valid_of_admissible hAdm
  obtain ⟨hph, hn, hm, hk, hoffs, hmems⟩ := run_encodeInstance P k
  set y := natBits (encodeInstance P k) with hydef
  obtain ⟨-, hoff0, hOff, hMem, hSorted, -, -, -⟩ := hv
  have hv := valid_of_admissible hAdm
  rw [← hydef] at hv
  have hlo : (run init y).offs.length = (run init y).m + 1 := run_offs_length_of_done _ hph
  have hlm : (run init y).mems.length = (run init y).offs.getD (run init y).m 0 := by
    rw [run_mems_length_of_done _ hph, run_offs_last_eq_off_of_done _ hph]
  have hcsr : csrWord (decY y) (run init y).k = csrWord P k := by
    unfold decY
    rw [csrWord_decodeInstance_eq (fun j => (run init y).offs.getD j 0)
      (fun t => (run init y).mems.getD t 0) (run init y).n (run init y).m hoff0 hOff hMem hSorted
      (run init y).offs (run init y).mems hlo (fun j => rfl) hlm (fun t => rfl)]
    unfold csrWord
    rw [hn, hm, hk, hoffs, hmems]
  have hE1 := encodes_decY hv
  rw [hcsr] at hE1
  have huniq := encodes_unique hE1 (encodes_of_admissible hAdm)
  rw [f_eq_valid hv, huniq.1, huniq.2]

end Lax496464Proofs.Ram.TotalReduction
