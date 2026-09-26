import Lax496464Proofs.Ram.CsrWord
import Lax496464Proofs.Ram.Validate

/-!
# Recovering an instance from a validated CSR array

`CsrWord.csrWord` builds a word from an `Instance`; `decodeInstance` goes the other way, building
an `Instance` from the offsets `foff`, the members `fmem` and the counts `n`, `m` that a scan
recovers. The conditions `Validate.validate` checks — `foff 0 = 0`, `OffsetsOkG`, `MembersOkG`,
`SortedOkG` and the size bound of `checkUniverseBound` — are what `encodes_decodeInstance` needs
to conclude that `csrWord (decodeInstance foff fmem n m) k` encodes the recovered instance.

`Instance.F j` filters to `x < n` before `Finset.attachFin`, so that `decodeInstance` is a plain
function of `foff`, `fmem`, `n`, `m`; every fact about what it computes is proved separately,
under the validated hypotheses.
-/

namespace Lax496464Proofs.Ram.CsrWord

open Lax496464.HittingSet
open Lax496464Proofs.Ram.Validate (OffsetsOkG MembersOkG SortedOkG OffsetsOkG.mono
  SortedOkG.injOn_sameBlock SortedOkG.strictMono_of_sameBlock)

variable (foff fmem : ℕ → ℕ) (n m : ℕ)

/-- An instance recovered directly from a validated CSR array: `foff`/`fmem` (the scan's own
recovered offsets/members), with `n`/`m` the recovered universe size and set count. Set `j`'s
family is the image of its member positions under `fmem`, filtered to `< n` (a no-op once
`MembersOkG` holds) so the definition needs no hypothesis at all. -/
def decodeInstance : Instance where
  n := n
  m := m
  F := fun j => (((Finset.Ico (foff j.val) (foff (j.val + 1))).image fmem).filter (· < n))
      |>.attachFin (fun _x hx => (Finset.mem_filter.mp hx).2)

/-- **A block's size, read back off `foff`.** `SortedOkG` gives injectivity of `fmem` within
one block (`SortedOkG.injOn_sameBlock`), so the image's cardinality is the block's raw length,
not just an upper bound. -/
theorem card_decodeInstance_F {j : ℕ} (hjm : j < m) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m)) :
    ((decodeInstance foff fmem n m).F ⟨j, hjm⟩).card = foff (j + 1) - foff j := by
  have hj1m : j + 1 ≤ m := hjm
  have hbound : foff (j + 1) ≤ foff m := OffsetsOkG.mono foff hOff hj1m le_rfl
  have hnoop : ∀ x ∈ (Finset.Ico (foff j) (foff (j + 1))).image fmem, x < n := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_Ico] at ht
    exact hMem t (by omega)
  show ((((Finset.Ico (foff j) (foff (j + 1))).image fmem).filter (· < n)).attachFin
    (fun x hx => (Finset.mem_filter.mp hx).2)).card = foff (j + 1) - foff j
  rw [Finset.card_attachFin, Finset.filter_true_of_mem hnoop,
    Finset.card_image_of_injOn (by
      rw [Finset.coe_Ico]; exact SortedOkG.injOn_sameBlock hSorted hjm hbound),
    Nat.card_Ico]

/-- **The offsets round-trip exactly.** By induction on `j`, chaining `card_decodeInstance_F`
through `getD_offsetsOf_succ`. -/
theorem offsetsOf_decodeInstance (hoff0 : foff 0 = 0) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m)) :
    ∀ j ≤ m, (offsetsOf (decodeInstance foff fmem n m)).getD j 0 = foff j := by
  intro j hj
  induction j with
  | zero => rw [getD_offsetsOf (P := decodeInstance foff fmem n m) (by omega)]; simp [hoff0]
  | succ j ih =>
    have hjm : j < m := by omega
    rw [getD_offsetsOf_succ (P := decodeInstance foff fmem n m) hjm, ih (by omega),
      card_decodeInstance_F foff fmem n m hjm hOff hMem hSorted]
    have := hOff j hjm
    omega

/-- **One block's members round-trip exactly, in order.** Both sides are strictly increasing
(`Instance.members`' own definition on the left, `SortedOkG` on the right) and have the same
underlying set, so `List.SortedLT.eq_of_mem_iff` (a strictly sorted list is determined by its
membership) identifies them outright — no permutation argument needed. -/
theorem members_decodeInstance {j : ℕ} (hjm : j < m) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m)) :
    ((decodeInstance foff fmem n m).members ⟨j, hjm⟩).map Fin.val =
      (List.range' (foff j) (foff (j + 1) - foff j)).map fmem := by
  set P := decodeInstance foff fmem n m with hPdef
  have hj1m : j + 1 ≤ m := hjm
  have hbound : foff j ≤ foff (j + 1) := hOff j hjm
  have hboundm : foff (j + 1) ≤ foff m := OffsetsOkG.mono foff hOff hj1m le_rfl
  have hlen : foff j + (foff (j + 1) - foff j) = foff (j + 1) := by omega
  have hLHSsorted : ((P.members ⟨j, hjm⟩).map Fin.val).SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_map]
    have hpw := (members_sortedLT P ⟨j, hjm⟩).pairwise
    exact hpw.imp (fun {a b} h => by exact_mod_cast h)
  have hRHSsorted :
      ((List.range' (foff j) (foff (j + 1) - foff j)).map fmem).SortedLT := by
    rw [List.sortedLT_iff_pairwise, List.pairwise_map]
    rw [List.range'_eq_map_range, List.pairwise_map]
    apply List.Pairwise.imp_of_mem (R := (· < ·))
    · intro a b ha hb hab
      simp only [List.mem_range] at ha hb
      have hlo' : foff j ≤ foff j + a := by omega
      have hhi' : foff j + b < foff (j + 1) := by omega
      have hs2t' : foff j + b < foff m := by omega
      have hlt' : foff j + a < foff j + b := by omega
      exact SortedOkG.strictMono_of_sameBlock hSorted hjm hlo' hhi' hs2t' hlt'
    · exact List.pairwise_lt_range
  refine List.SortedLT.eq_of_mem_iff hLHSsorted hRHSsorted fun v => ?_
  simp only [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    unfold Instance.members at hi
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hi
    have hiF : (i : ℕ) ∈ (((Finset.Ico (foff j) (foff (j + 1))).image fmem).filter (· < n)) :=
      (Finset.mem_attachFin _).mp hi
    obtain ⟨hival, -⟩ := Finset.mem_filter.mp hiF
    obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp hival
    simp only [Finset.mem_Ico] at ht
    refine ⟨t, ?_, hteq⟩
    rw [List.mem_range']
    exact ⟨t - foff j, by omega, by omega⟩
  · rintro ⟨t, ht, rfl⟩
    rw [List.mem_range'] at ht
    obtain ⟨i, hilt, hieq⟩ := ht
    have htIco : t ∈ Finset.Ico (foff j) (foff (j + 1)) := by
      simp only [Finset.mem_Ico]; omega
    have hfltn : fmem t < n := hMem t (by omega : t < foff m)
    have hmemF : fmem t ∈ (((Finset.Ico (foff j) (foff (j + 1))).image fmem).filter (· < n)) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨t, htIco, rfl⟩, hfltn⟩
    refine ⟨⟨fmem t, hfltn⟩, ?_, rfl⟩
    unfold Instance.members
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact (Finset.mem_attachFin _).mpr hmemF

theorem getD_range'_map (s L u : ℕ) (f : ℕ → ℕ) (h : u < L) :
    ((List.range' s L).map f).getD u 0 = f (s + u) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa using h)]
  simp [List.getElem_range']

/-- **The members round-trip exactly at any position inside one named block.** -/
theorem member_decodeInstance_of_block {j : ℕ} (hjm : j < m) (hoff0 : foff 0 = 0)
    (hOff : OffsetsOkG foff m) (hMem : MembersOkG fmem n (foff m))
    (hSorted : SortedOkG foff fmem m (foff m))
    {t : ℕ} (hlo : foff j ≤ t) (hhi : t < foff (j + 1)) :
    (membersOf (decodeInstance foff fmem n m)).getD t 0 = fmem t := by
  set P := decodeInstance foff fmem n m with hPdef
  have hcard : (P.F ⟨j, hjm⟩).card = foff (j + 1) - foff j :=
    card_decodeInstance_F foff fmem n m hjm hOff hMem hSorted
  have hu : t - foff j < (P.members ⟨j, hjm⟩).length := by
    rw [length_members]; omega
  have hgetD := getD_membersOf (P := P) hjm hu
  rw [members_decodeInstance foff fmem n m hjm hOff hMem hSorted,
    getD_range'_map (foff j) (foff (j + 1) - foff j) (t - foff j) fmem (by omega),
    show foff j + (t - foff j) = t by omega,
    offsetsOf_decodeInstance foff fmem n m hoff0 hOff hMem hSorted j hjm.le,
    show foff j + (t - foff j) = t by omega] at hgetD
  exact hgetD

/-- Every position below `foff m` falls in some block below `m` — `OffsetsOkG`'s own
monotonicity plus `foff 0 = 0`, by induction on the number of blocks considered. -/
theorem exists_block_of_lt (hoff0 : foff 0 = 0) (_hOff : OffsetsOkG foff m) :
    ∀ mm ≤ m, ∀ t, t < foff mm → ∃ j < mm, foff j ≤ t ∧ t < foff (j + 1) := by
  intro mm
  induction mm with
  | zero => intro _ t ht; rw [hoff0] at ht; omega
  | succ mm ih =>
    intro hmm t ht
    by_cases hc : t < foff mm
    · obtain ⟨j, hjmm, hlo, hhi⟩ := ih (by omega) t hc
      exact ⟨j, by omega, hlo, hhi⟩
    · exact ⟨mm, by omega, by omega, by omega⟩

/-- **The members round-trip exactly, everywhere.** -/
theorem member_decodeInstance (hoff0 : foff 0 = 0) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m)) :
    ∀ t < foff m, (membersOf (decodeInstance foff fmem n m)).getD t 0 = fmem t := by
  intro t ht
  obtain ⟨j, hjm, hlo, hhi⟩ := exists_block_of_lt foff m hoff0 hOff m le_rfl t ht
  exact member_decodeInstance_of_block foff fmem n m hjm hoff0 hOff hMem hSorted hlo hhi

theorem membersOf_length_decodeInstance (hoff0 : foff 0 = 0) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m)) :
    (membersOf (decodeInstance foff fmem n m)).length = foff m := by
  have hPm : (decodeInstance foff fmem n m).m = m := rfl
  rw [← offsetsOf_last, hPm,
    offsetsOf_decodeInstance foff fmem n m hoff0 hOff hMem hSorted m le_rfl]

theorem offset_decodeInstance (hoff0 : foff 0 = 0) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m)) (k : ℕ)
    {j : ℕ} (hj : j ≤ m) :
    offset (csrWord (decodeInstance foff fmem n m) k) j = foff j := by
  rw [offset_csrWord hj, offsetsOf_decodeInstance foff fmem n m hoff0 hOff hMem hSorted j hj]

theorem member_decodeInstance_csrWord (hoff0 : foff 0 = 0) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m)) (k : ℕ)
    {t : ℕ} (ht : t < foff m) :
    member (csrWord (decodeInstance foff fmem n m) k) t = fmem t := by
  have hlen := membersOf_length_decodeInstance foff fmem n m hoff0 hOff hMem hSorted
  rw [member_csrWord (by rw [hlen]; exact ht)]
  exact member_decodeInstance foff fmem n m hoff0 hOff hMem hSorted t ht

/-- **The recovered CSR word `csrWord (decodeInstance foff fmem n m) k` genuinely encodes
`decodeInstance foff fmem n m` with solution size `k`.** Everything `validate` checks
(`foff 0 = 0`, `OffsetsOkG`, `MembersOkG`, `SortedOkG`, the size bound, `2 ≤ k ≤ n`) is exactly
what `encodes_csrWord`'s own hypotheses ask for, once `n ≤ (csrWord P k).length` is unfolded via
`length_csrWord`/`membersOf_length_decodeInstance` back into `n ≤ m + foff m + 4`. -/
theorem encodes_decodeInstance (hoff0 : foff 0 = 0) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m))
    {k : ℕ} (hk2 : 2 ≤ k) (hkn : k ≤ n) (hnmB : n ≤ m + foff m + 4) :
    Encodes (csrWord (decodeInstance foff fmem n m) k) (decodeInstance foff fmem n m) k := by
  have hlen := membersOf_length_decodeInstance foff fmem n m hoff0 hOff hMem hSorted
  have hPm : (decodeInstance foff fmem n m).m = m := rfl
  have hPn : (decodeInstance foff fmem n m).n = n := rfl
  refine encodes_csrWord hk2 hkn ?_
  rw [length_csrWord, hlen, hPm, hPn]
  omega

/-- The recovered instance's offset list *is* the scan's own `offs`, given `offs` has the right
length and `foff` is read off it. -/
theorem offsetsOf_decodeInstance_eq (hoff0 : foff 0 = 0) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m))
    (offs : List ℕ) (hlen : offs.length = m + 1) (hoffs : ∀ j, foff j = offs.getD j 0) :
    offsetsOf (decodeInstance foff fmem n m) = offs := by
  have hPm : (decodeInstance foff fmem n m).m = m := rfl
  apply List.ext_getElem
  · rw [length_offsetsOf, hPm, hlen]
  · intro i h1 h2
    have hi : i ≤ m := by rw [length_offsetsOf, hPm] at h1; omega
    have := offsetsOf_decodeInstance foff fmem n m hoff0 hOff hMem hSorted i hi
    rw [List.getD_eq_getElem _ _ h1] at this
    rw [this, hoffs i, List.getD_eq_getElem _ _ h2]

/-- Likewise the recovered instance's flat member list is the scan's own `mems`. -/
theorem membersOf_decodeInstance_eq (hoff0 : foff 0 = 0) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m))
    (mems : List ℕ) (hlen : mems.length = foff m) (hmems : ∀ t, fmem t = mems.getD t 0) :
    membersOf (decodeInstance foff fmem n m) = mems := by
  have hl := membersOf_length_decodeInstance foff fmem n m hoff0 hOff hMem hSorted
  apply List.ext_getElem
  · rw [hl, hlen]
  · intro i h1 h2
    have hi : i < foff m := by rw [hl] at h1; exact h1
    have := member_decodeInstance foff fmem n m hoff0 hOff hMem hSorted i hi
    rw [List.getD_eq_getElem _ _ h1] at this
    rw [this, hmems i, List.getD_eq_getElem _ _ h2]

/-- **The recovered CSR word, spelled out from the scan's own lists.** -/
theorem csrWord_decodeInstance_eq (hoff0 : foff 0 = 0) (hOff : OffsetsOkG foff m)
    (hMem : MembersOkG fmem n (foff m)) (hSorted : SortedOkG foff fmem m (foff m))
    (offs mems : List ℕ) (hlo : offs.length = m + 1) (hoffs : ∀ j, foff j = offs.getD j 0)
    (hlm : mems.length = foff m) (hmems : ∀ t, fmem t = mems.getD t 0) (k : ℕ) :
    csrWord (decodeInstance foff fmem n m) k = [n, m] ++ offs ++ mems ++ [k] := by
  unfold csrWord
  rw [offsetsOf_decodeInstance_eq foff fmem n m hoff0 hOff hMem hSorted offs hlo hoffs,
    membersOf_decodeInstance_eq foff fmem n m hoff0 hOff hMem hSorted mems hlm hmems]
  rfl

end Lax496464Proofs.Ram.CsrWord
