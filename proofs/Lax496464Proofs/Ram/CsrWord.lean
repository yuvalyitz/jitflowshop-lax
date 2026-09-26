import Lax496464.HittingSet
import Mathlib.Data.List.GetD
import Mathlib.Data.List.FinRange
import Lax496464Proofs.Ram.PartialSums

/-!
# The numeric CSR word of a Hitting Set instance

`HittingSet.Encodes` says when a word `x` presents an instance `P` with solution size `k`;
nothing in the concept builds such a word *from* `P` and `k`. `csrWord P k` is that word —
the two counts, the offsets as the partial sums of the sets' sizes, the members set by set
in the order of the universe, and the solution size — and `encodes_csrWord` is the fact
that it does what `Encodes` asks. This is the other half of the correspondence the reduction's
input side needs: `Ram/ReadHS.lean` reads a word into the arrays a machine wants, and this
produces the word an actual instance is presented by.
-/

namespace Lax496464Proofs.Ram.CsrWord

open Lax496464.HittingSet

variable (P : Instance)

/-- The size of each set, in the order of the universe of sets. -/
def sizes : List ℕ := (List.finRange P.m).map fun j => (P.F j).card

/-- The offsets: the partial sums of the sizes, `P.m + 1` of them. -/
def offsetsOf : List ℕ := (sizes P).partialSums

/-- The members, set by set, each in the order of the universe. -/
def membersOf : List ℕ := (List.finRange P.m).flatMap fun j => (P.members j).map Fin.val

variable {P}

@[simp] theorem length_sizes : (sizes P).length = P.m := by simp [sizes]

@[simp] theorem length_offsetsOf : (offsetsOf P).length = P.m + 1 := by
  rw [offsetsOf, Lax496464Proofs.Ram.PartialSums.length_partialSums, length_sizes]

theorem length_members (j : Fin P.m) : (P.members j).length = (P.F j).card := by
  unfold Instance.members
  have hnodup : ((List.finRange P.n).filter (fun i => decide (i ∈ P.F j))).Nodup :=
    (List.nodup_finRange P.n).filter _
  have htoFinset : ((List.finRange P.n).filter (fun i => decide (i ∈ P.F j))).toFinset =
      P.F j := by
    ext i
    simp
  rw [← List.toFinset_card_of_nodup hnodup, htoFinset]

theorem length_membersOf : (membersOf P).length = (sizes P).sum := by
  unfold membersOf sizes
  rw [List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [length_members]

/-! ## Reading a position back off a concatenation of blocks -/

section FlatMapGetD

variable {α : Type*} (blocks : List (List α)) (d : α)

/-- The length of everything before block `j`. -/
def blockStart (j : ℕ) : ℕ := ((blocks.take j).map List.length).sum

theorem blockStart_zero : blockStart blocks 0 = 0 := by simp [blockStart]

theorem blockStart_succ {j : ℕ} (hj : j < blocks.length) :
    blockStart blocks (j + 1) = blockStart blocks j + (blocks.getD j []).length := by
  unfold blockStart
  rw [List.take_add_one]
  have hj' : blocks[j]? = some (blocks.getD j []) := by
    rw [List.getD_eq_getElem?_getD]
    rcases h : blocks[j]? with _ | l
    · exact absurd (List.getElem?_eq_none_iff.mp h) (by omega)
    · simp
  rw [hj']
  simp

theorem getD_flatMap_of_lt {j u : ℕ} (hj : j < blocks.length) (hu : u < (blocks.getD j []).length) :
    (blocks.flatMap id).getD (blockStart blocks j + u) d = (blocks.getD j []).getD u d := by
  induction j generalizing blocks with
  | zero =>
    rw [blockStart_zero, Nat.zero_add]
    rcases blocks with _ | ⟨b, bs⟩
    · simp at hj
    · have hub : u < b.length := by simpa using hu
      show (b ++ bs.flatMap id).getD u d = b.getD u d
      rw [List.getD_append _ _ _ _ hub]
  | succ j ih =>
    rcases blocks with _ | ⟨b, bs⟩
    · simp at hj
    · have hj' : j < bs.length := by simpa using Nat.lt_of_succ_lt_succ hj
      have hbs : (b :: bs).getD (j + 1) [] = bs.getD j [] := by simp
      rw [hbs] at hu ⊢
      have hstart : blockStart (b :: bs) (j + 1) = b.length + blockStart bs j := by
        simp [blockStart]
      rw [hstart, show b.length + blockStart bs j + u = b.length + (blockStart bs j + u) by ring]
      show (b ++ bs.flatMap id).getD (b.length + (blockStart bs j + u)) d =
        (bs.getD j []).getD u d
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.add_sub_cancel_left]
      exact ih bs hj' hu

end FlatMapGetD

theorem sum_take_le (l : List ℕ) (n : ℕ) : (l.take n).sum ≤ l.sum := by
  conv_rhs => rw [← List.take_append_drop n l]
  rw [List.sum_append]
  omega

/-- The offset at `j` is the total size of the first `j` sets. -/
theorem getD_offsetsOf {j : ℕ} (hj : j ≤ P.m) :
    (offsetsOf P).getD j 0 = ((sizes P).take j).sum := by
  unfold offsetsOf
  rw [List.getD_eq_getElem?_getD]
  have hjlt : j < (sizes P).partialSums.length := by
    rw [Lax496464Proofs.Ram.PartialSums.length_partialSums, length_sizes]; omega
  rw [List.getElem?_eq_getElem hjlt, Lax496464Proofs.Ram.PartialSums.getElem_partialSums hjlt]
  rfl

/-- The `j`-th block of members, using a raw index with a totality fallback. -/
def blk (P : Instance) (j : ℕ) : List ℕ :=
  if h : j < P.m then (P.members ⟨j, h⟩).map Fin.val else []

theorem membersOf_eq_flatMap_range : membersOf P = (List.range P.m).flatMap (blk P) := by
  unfold membersOf blk
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  refine List.flatMap_congr fun j _ => ?_
  simp

theorem length_blk {j : ℕ} (hj : j < P.m) : (blk P j).length = (P.F ⟨j, hj⟩).card := by
  unfold blk
  rw [dif_pos hj, List.length_map]
  exact length_members ⟨j, hj⟩

theorem getElem?_finRange {n i : ℕ} :
    (List.finRange n)[i]? = if h : i < n then some ⟨i, h⟩ else none := by
  show (List.ofFn (fun k : Fin n => k))[i]? = _
  rw [List.getElem?_ofFn]

theorem getD_sizes {j : ℕ} (hj : j < P.m) : (sizes P).getD j 0 = (P.F ⟨j, hj⟩).card := by
  unfold sizes
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, getElem?_finRange, dif_pos hj]
  rfl

theorem getD_offsetsOf_succ {j : ℕ} (hj : j < P.m) :
    (offsetsOf P).getD (j + 1) 0 = (offsetsOf P).getD j 0 + (P.F ⟨j, hj⟩).card := by
  rw [getD_offsetsOf (by omega), getD_offsetsOf hj.le, List.take_add_one]
  rcases h : (sizes P)[j]? with _ | v
  · exact absurd (List.getElem?_eq_none_iff.mp h) (by simpa using hj)
  · have hveq : v = (P.F ⟨j, hj⟩).card := by
      have := getD_sizes (P := P) hj
      rw [List.getD_eq_getElem?_getD, h] at this
      simpa using this
    simp [hveq]

theorem blockStart_eq_offsetsOf (j : ℕ) (hj : j ≤ P.m) :
    blockStart ((List.range P.m).map (blk P)) j = (offsetsOf P).getD j 0 := by
  induction j with
  | zero => rw [blockStart_zero, getD_offsetsOf (by omega)]; simp
  | succ j ih =>
    have hj' : j < P.m := by omega
    have hstep : blockStart ((List.range P.m).map (blk P)) (j + 1) =
        blockStart ((List.range P.m).map (blk P)) j +
          (((List.range P.m).map (blk P)).getD j []).length := by
      apply blockStart_succ (blocks := (List.range P.m).map (blk P)) (j := j)
      simp; omega
    have hgetD : ((List.range P.m).map (blk P)).getD j [] = blk P j := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj']
      rfl
    rw [hstep, hgetD, length_blk hj', ih hj'.le, getD_offsetsOf_succ hj']

theorem flatMap_blk_eq_map_flatMap :
    (List.range P.m).flatMap (blk P) = ((List.range P.m).map (blk P)).flatMap id := by
  rw [List.flatMap_map]
  simp

theorem getD_membersOf {j : ℕ} (hj : j < P.m) {u : ℕ} (hu : u < (P.members ⟨j, hj⟩).length) :
    (membersOf P).getD ((offsetsOf P).getD j 0 + u) 0 =
      ((P.members ⟨j, hj⟩).map Fin.val).getD u 0 := by
  rw [membersOf_eq_flatMap_range, flatMap_blk_eq_map_flatMap, ← blockStart_eq_offsetsOf j hj.le]
  have hjb : j < ((List.range P.m).map (blk P)).length := by simp; omega
  have hgetD : ((List.range P.m).map (blk P)).getD j [] = blk P j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
    rfl
  have hub : u < (((List.range P.m).map (blk P)).getD j []).length := by
    rw [hgetD, length_blk hj, ← length_members ⟨j, hj⟩]; exact hu
  rw [getD_flatMap_of_lt ((List.range P.m).map (blk P)) 0 hjb hub, hgetD]
  unfold blk; rw [dif_pos hj]

/-! ## The word -/

variable (P) (k : ℕ)

/-- The numeric CSR word of an instance `P` with solution size `k`: the two counts, the
offsets, the members set by set, and the solution size. -/
def csrWord : List ℕ := [P.n, P.m] ++ offsetsOf P ++ membersOf P ++ [k]

variable {P k}

theorem csrWord_eq : csrWord P k = [P.n, P.m] ++ (offsetsOf P ++ (membersOf P ++ [k])) := by
  unfold csrWord; simp [List.append_assoc]

theorem getD_csrWord_n : (csrWord P k).getD 0 0 = P.n := by
  rw [csrWord_eq]; rfl

theorem getD_csrWord_m : (csrWord P k).getD 1 0 = P.m := by
  rw [csrWord_eq]; rfl

theorem getD_csrWord_offset {j : ℕ} (hj : j ≤ P.m) :
    (csrWord P k).getD (2 + j) 0 = (offsetsOf P).getD j 0 := by
  rw [csrWord_eq]
  have h1 : (2 : ℕ) ≤ ([P.n, P.m] : List ℕ).length := by simp
  rw [show (2 : ℕ) + j = ([P.n, P.m] : List ℕ).length + j by simp,
    List.getD_append_right _ _ _ _ (by simp)]
  have h2 : j < (offsetsOf P).length := by rw [length_offsetsOf]; omega
  rw [show ([P.n, P.m] : List ℕ).length + j - ([P.n, P.m] : List ℕ).length = j by omega,
    List.getD_append _ _ _ _ (by simpa using h2)]

theorem getD_csrWord_member {t : ℕ} (ht : t < (membersOf P).length) :
    (csrWord P k).getD (3 + P.m + t) 0 = (membersOf P).getD t 0 := by
  rw [csrWord_eq]
  have he : (3 : ℕ) + P.m + t = ([P.n, P.m] : List ℕ).length + ((offsetsOf P).length + t) := by
    rw [length_offsetsOf]; simp; omega
  rw [he, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getD_append _ _ _ _ (by simpa using ht)]

theorem getD_csrWord_k : (csrWord P k).getD (3 + P.m + (membersOf P).length) 0 = k := by
  rw [csrWord_eq]
  have he : (3 : ℕ) + P.m + (membersOf P).length =
      ([P.n, P.m] : List ℕ).length + ((offsetsOf P).length + (membersOf P).length) := by
    rw [length_offsetsOf]; simp; omega
  rw [he, List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil, Nat.add_sub_cancel_left]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem length_csrWord : (csrWord P k).length = 4 + P.m + (membersOf P).length := by
  rw [csrWord_eq]
  simp [length_offsetsOf]
  omega

theorem offsetsOf_last : (offsetsOf P).getD P.m 0 = (membersOf P).length := by
  rw [getD_offsetsOf le_rfl, show P.m = (sizes P).length from length_sizes.symm,
    List.take_length, length_membersOf]

/-- **The word encodes `P` with solution size `k`**, provided `2 ≤ k ≤ P.n`. -/
theorem offset_csrWord {j : ℕ} (hj : j ≤ P.m) :
    offset (csrWord P k) j = (offsetsOf P).getD j 0 := by
  rw [offset]; exact getD_csrWord_offset hj

theorem setCount_csrWord : setCount (csrWord P k) = P.m := by
  rw [setCount]; exact getD_csrWord_m

theorem member_csrWord {t : ℕ} (ht : t < (membersOf P).length) :
    member (csrWord P k) t = (membersOf P).getD t 0 := by
  rw [member, setCount_csrWord]; exact getD_csrWord_member ht

theorem offset_csrWord_last : offset (csrWord P k) P.m = (membersOf P).length := by
  rw [offset_csrWord le_rfl, offsetsOf_last]

theorem getD_offsetsOf_succ' (j : Fin P.m) :
    (offsetsOf P).getD ((j : ℕ) + 1) 0 = (offsetsOf P).getD (j : ℕ) 0 + (P.F j).card :=
  getD_offsetsOf_succ j.2

theorem encodes_csrWord (hk2 : 2 ≤ k) (hkn : k ≤ P.n)
    (hPn : P.n ≤ (csrWord P k).length) : Encodes (csrWord P k) P k where
  universeSize_eq := getD_csrWord_n
  setCount_eq := getD_csrWord_m
  length_eq := by rw [offset_csrWord_last, length_csrWord]
  offset_zero := by rw [offset_csrWord (by omega), getD_offsetsOf (by omega)]; simp
  offset_mono := by
    intro j hj
    rw [offset_csrWord hj.le, offset_csrWord hj, getD_offsetsOf_succ hj]
    omega
  member_lt := by
    intro t ht
    rw [offset_csrWord_last] at ht
    rw [member_csrWord ht]
    unfold membersOf at ht ⊢
    rw [List.getD_eq_getElem?_getD]
    rcases h : ((List.finRange P.m).flatMap fun j => (P.members j).map Fin.val)[t]? with _ | v
    · exact absurd (List.getElem?_eq_none_iff.mp h) (by omega)
    · have hmem : v ∈ (List.finRange P.m).flatMap fun j => (P.members j).map Fin.val :=
        List.mem_of_getElem? h
      simp only [List.mem_flatMap, List.mem_map] at hmem
      obtain ⟨j, -, i, -, hveq⟩ := hmem
      simp only [Option.getD_some]
      omega
  mem_iff := by
    intro j i
    have hj := j.2
    constructor
    · intro hmem
      have hmemL : (i : ℕ) ∈ (P.members j).map Fin.val := by
        simp only [List.mem_map]
        refine ⟨i, ?_, rfl⟩
        unfold Instance.members
        simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
        exact hmem
      obtain ⟨u, hu, hveq⟩ := List.mem_iff_getElem.mp hmemL
      have hult : u < ((P.members j).map Fin.val).length := hu
      have hult' : u < (P.members j).length := by simpa using hult
      have hcard : u < (P.F j).card := by rw [← length_members j]; exact hult'
      refine ⟨(offsetsOf P).getD j 0 + u, ?_, ?_, ?_⟩
      · rw [offset_csrWord hj.le]; omega
      · rw [offset_csrWord hj, getD_offsetsOf_succ' j]; omega
      · have hub : (offsetsOf P).getD (j : ℕ) 0 + u < (membersOf P).length := by
          rw [length_membersOf]
          calc (offsetsOf P).getD (j : ℕ) 0 + u
              < (offsetsOf P).getD (j : ℕ) 0 + (P.F j).card := by omega
            _ = (offsetsOf P).getD ((j : ℕ) + 1) 0 := (getD_offsetsOf_succ' j).symm
            _ = ((sizes P).take ((j : ℕ) + 1)).sum := getD_offsetsOf (Nat.succ_le_of_lt j.2)
            _ ≤ (sizes P).sum := sum_take_le (sizes P) _
        rw [member_csrWord hub, getD_membersOf j.2 hult']
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]
        simpa using hveq
    · rintro ⟨t, ht1, ht2, ht3⟩
      rw [offset_csrWord (le_of_lt j.2)] at ht1
      rw [offset_csrWord j.2, getD_offsetsOf_succ' j] at ht2
      set u := t - (offsetsOf P).getD (j : ℕ) 0 with hu
      have htu : t = (offsetsOf P).getD (j : ℕ) 0 + u := by omega
      have hult : u < (P.F j).card := by omega
      have hult' : u < (P.members j).length := by rw [length_members]; exact hult
      have hmemval : (membersOf P).getD t 0 = ((P.members j).map Fin.val).getD u 0 := by
        rw [htu]; exact getD_membersOf j.2 hult'
      have hub : t < (membersOf P).length := by
        rw [length_membersOf]
        calc t = (offsetsOf P).getD (j : ℕ) 0 + u := htu
          _ < (offsetsOf P).getD (j : ℕ) 0 + (P.F j).card := by omega
          _ = (offsetsOf P).getD ((j : ℕ) + 1) 0 := (getD_offsetsOf_succ' j).symm
          _ = ((sizes P).take ((j : ℕ) + 1)).sum := getD_offsetsOf (Nat.succ_le_of_lt j.2)
          _ ≤ (sizes P).sum := sum_take_le (sizes P) _
      rw [member_csrWord hub, hmemval] at ht3
      have hmem2 : (i : ℕ) ∈ ((P.members j).map Fin.val) := by
        rw [← ht3, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem
          (by simpa using hult')]
        exact List.getElem_mem _
      simp only [List.mem_map] at hmem2
      obtain ⟨i', hi', hival⟩ := hmem2
      have hii : i' = i := Fin.ext hival
      rw [← hii]
      have hi'' := hi'
      unfold Instance.members at hi''
      simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hi''
      exact hi''
  solutionSize_eq := by
    rw [solutionSize, setCount_csrWord, offset_csrWord_last, getD_csrWord_k]
  size_bounds := ⟨hk2, hkn⟩
  universeSize_le := hPn

/-! ## `csrWord`'s members are strictly increasing within their own block

`Instance.members` filters `List.finRange`, in place, in ascending order — never reordering or
repeating an element — so each block of `membersOf P` is strictly increasing on its own, a fact
`Encodes`'s own four data clauses don't state (they only bound and order the *offsets*). This is
the extra fact `Ram/Validate.lean`'s strengthened check (`checkSorted`) needs to accept every
genuine encoding. -/

theorem offsetsOf_mono {P : Instance} {i j : ℕ} (hij : i ≤ j) (hjm : j ≤ P.m) :
    (offsetsOf P).getD i 0 ≤ (offsetsOf P).getD j 0 := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    simp [hi0]
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · have hprev := ih (by omega) (by omega)
      have hstep := getD_offsetsOf_succ (P := P) (j := j) (by omega)
      omega
    · have hi : i = j + 1 := by omega
      simp [hi]

theorem offset_csrWord_mono {P : Instance} {k i j : ℕ} (hij : i ≤ j) (hjm : j ≤ P.m) :
    offset (csrWord P k) i ≤ offset (csrWord P k) j := by
  rw [offset_csrWord (hij.trans hjm), offset_csrWord hjm]
  exact offsetsOf_mono hij hjm

theorem members_sortedLT (P : Instance) (j : Fin P.m) : (P.members j).SortedLT := by
  unfold Instance.members
  have h1 : (List.finRange P.n).SortedLT := by
    rw [← List.ofFn_id (n := P.n)]
    exact List.sortedLT_ofFn_iff.mpr strictMono_id
  have h2 : ((List.finRange P.n).filter (fun i => decide (i ∈ P.F j))).Sublist
      (List.finRange P.n) := List.filter_sublist
  exact (h1.pairwise.sublist h2).sortedLT

theorem members_map_val_getD_lt {P : Instance} (j : Fin P.m) {u : ℕ}
    (hu : u + 1 < (P.members j).length) :
    ((P.members j).map Fin.val).getD u 0 < ((P.members j).map Fin.val).getD (u + 1) 0 := by
  have hpw : (P.members j).Pairwise (· < ·) := (members_sortedLT P j).pairwise
  have hpw' : ((P.members j).map Fin.val).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact hpw.imp (fun {a b} h => by exact_mod_cast h)
  have hsl' : ((P.members j).map Fin.val).SortedLT := hpw'.sortedLT
  have hulen' : u < ((P.members j).map Fin.val).length := by
    simp only [List.length_map]; omega
  have hu1len' : u + 1 < ((P.members j).map Fin.val).length := by
    simp only [List.length_map]; omega
  have h1 := hsl'.strictMono_get (a := ⟨u, hulen'⟩) (b := ⟨u + 1, hu1len'⟩) (by simp)
  have e1 : ((P.members j).map Fin.val).get ⟨u, hulen'⟩ =
      ((P.members j).map Fin.val).getD u 0 := by
    rw [List.getD_eq_getElem?_getD, List.get_eq_getElem, List.getElem?_eq_getElem hulen']
    rfl
  have e2 : ((P.members j).map Fin.val).get ⟨u + 1, hu1len'⟩ =
      ((P.members j).map Fin.val).getD (u + 1) 0 := by
    rw [List.getD_eq_getElem?_getD, List.get_eq_getElem, List.getElem?_eq_getElem hu1len']
    rfl
  rwa [e1, e2] at h1

/-- **The payoff.** Any two adjacent positions `s`, `s + 1` that both fall inside the same
block `jj` (per the block's own offsets, `s + 1` not yet past `offset (jj + 1)`) hold strictly
increasing members. -/
theorem member_csrWord_strictMono_of_sameBlock {P : Instance} {k jj s : ℕ} (hjj : jj < P.m)
    (hlo : offset (csrWord P k) jj ≤ s) (hhi : s + 1 < offset (csrWord P k) (jj + 1)) :
    member (csrWord P k) s < member (csrWord P k) (s + 1) := by
  set u := s - offset (csrWord P k) jj with hudef
  have hsu : s = offset (csrWord P k) jj + u := by omega
  have hs1u : s + 1 = offset (csrWord P k) jj + (u + 1) := by omega
  have hcard : (P.F ⟨jj, hjj⟩).card = (P.members ⟨jj, hjj⟩).length :=
    (length_members ⟨jj, hjj⟩).symm
  have hstep : offset (csrWord P k) (jj + 1) = offset (csrWord P k) jj + (P.F ⟨jj, hjj⟩).card := by
    rw [offset_csrWord (by omega), offset_csrWord hjj.le, getD_offsetsOf_succ hjj]
  have hu1len : u + 1 < (P.members ⟨jj, hjj⟩).length := by rw [← hcard]; omega
  have hulen : u < (P.members ⟨jj, hjj⟩).length := by omega
  have hoffle : offset (csrWord P k) (jj + 1) ≤ offset (csrWord P k) P.m :=
    offset_csrWord_mono (by omega) (by omega)
  have hmemlast : offset (csrWord P k) P.m = (membersOf P).length := offset_csrWord_last
  have hsbound : s + 1 < (membersOf P).length := by omega
  have keyU : (membersOf P).getD s 0 = ((P.members ⟨jj, hjj⟩).map Fin.val).getD u 0 := by
    have h := getD_membersOf hjj hulen
    rw [show (offsetsOf P).getD jj 0 = offset (csrWord P k) jj from (offset_csrWord hjj.le).symm]
      at h
    rw [hsu]; exact h
  have keyU1 : (membersOf P).getD (s + 1) 0 =
      ((P.members ⟨jj, hjj⟩).map Fin.val).getD (u + 1) 0 := by
    have h := getD_membersOf hjj hu1len
    rw [show (offsetsOf P).getD jj 0 = offset (csrWord P k) jj from (offset_csrWord hjj.le).symm]
      at h
    rw [hs1u]; exact h
  have hmember_s : member (csrWord P k) s = ((P.members ⟨jj, hjj⟩).map Fin.val).getD u 0 := by
    rw [member_csrWord (by omega)]; exact keyU
  have hmember_s1 : member (csrWord P k) (s + 1) =
      ((P.members ⟨jj, hjj⟩).map Fin.val).getD (u + 1) 0 := by
    rw [member_csrWord (by omega)]; exact keyU1
  rw [hmember_s, hmember_s1]
  exact members_map_val_getD_lt ⟨jj, hjj⟩ hu1len

end Lax496464Proofs.Ram.CsrWord
