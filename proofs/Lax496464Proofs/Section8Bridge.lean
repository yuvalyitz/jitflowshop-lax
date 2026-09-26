import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.FinRange
import Lax496464Proofs.Bridge
import Lax496464Proofs.Transport
import Lax496464Proofs.Model.Lemma7to9_Extract
import Lax496464.Construction

/-!
# Numbering the jobs of Section 8's construction

`Model/Theorem1_FromHittingSet.lean` names the constructed jobs structurally: a selection
job is a triple (segment, set, element of that set), a dummy a triple (segment, set,
element of the universe). The concepts number them `0, …, N−1`, because the construction's
output is a word. This file is the bijection between the two namings.

The numbering lays the jobs out in three blocks: the `R·|memberList|` selection jobs first,
then the `R·m·n` jobs of the first dummy family, then the `R·m·n` of the second. Inside a
block the index is mixed radix — `element + n·set + (m·n)·segment` for a dummy, and
`position in memberList + |memberList|·segment` for a selection job — which is exactly what
`Construction.slot` takes apart.
-/

namespace Lax496464Proofs.Section8Bridge

open Lax496464.HittingSet Lax496464.Construction
open FlexFlowJIT Transport

/-- The development's Hitting Set instance belonging to a concept instance. -/
abbrev hs (P : Lax496464.HittingSet.Instance) : HSInstance := ⟨P.n, P.m, P.F⟩

variable {P : Lax496464.HittingSet.Instance} {k : ℕ}

/-! ## 1. The list of membership pairs -/

/-- The number of selection jobs per segment. -/
abbrev L (P : Lax496464.HittingSet.Instance) : ℕ := (memberList P).length


/-- Every membership pair occurs in the list. -/
theorem mem_memberList {j : Fin P.m} {i : Fin P.n} (hi : i ∈ P.F j) :
    ((j : ℕ), (i : ℕ)) ∈ memberList P := by
  rw [memberList, List.mem_flatMap]
  refine ⟨j, List.mem_finRange j, ?_⟩
  rw [List.mem_map]
  refine ⟨i, ?_, rfl⟩
  rw [Instance.members, List.mem_filter]
  exact ⟨List.mem_finRange i, by simpa using hi⟩

/-- The position of a selection job's membership pair in the list. -/
def selPos (s : (hs P).SelIdx) : ℕ := (memberList P).idxOf ((s.1 : ℕ), (s.2.val : ℕ))

theorem selPos_lt (s : (hs P).SelIdx) : selPos s < L P :=
  List.idxOf_lt_length_iff.mpr (mem_memberList s.2.2)

theorem getD_selPos (s : (hs P).SelIdx) :
    (memberList P).getD (selPos s) (0, 0) = ((s.1 : ℕ), (s.2.val : ℕ)) := by
  rw [List.getD_eq_getElem _ _ (selPos_lt s)]
  exact List.getElem_idxOf _

theorem selPos_injective : Function.Injective (selPos (P := P)) := by
  intro s t h
  have hs' := getD_selPos s
  have ht' := getD_selPos t
  rw [h, ht'] at hs'
  obtain ⟨j₁, i₁⟩ := s
  obtain ⟨j₂, i₂⟩ := t
  simp only [Prod.mk.injEq] at hs'
  obtain ⟨hj, hi⟩ := hs'
  obtain rfl : j₁ = j₂ := Fin.ext hj.symm
  obtain rfl : i₁ = i₂ := Subtype.ext (Fin.ext hi.symm)
  rfl

/-- The list has one entry per selection index. -/
theorem length_memberList : L P = Fintype.card (hs P).SelIdx := by
  classical
  have hlen : ∀ j : Fin P.m, (P.members j).length = (P.F j).card := by
    intro j
    have h : (P.members j).length = (Finset.univ.filter (fun i => i ∈ P.F j)).card := rfl
    rw [h, Finset.filter_univ_mem]
  have hcard : Fintype.card (hs P).SelIdx = ∑ j : Fin P.m, (P.F j).card := by
    show Fintype.card (Σ j : Fin P.m, {i : Fin P.n // i ∈ P.F j}) = _
    rw [Fintype.card_sigma]
    exact Finset.sum_congr rfl fun j _ => Fintype.card_coe _
  rw [hcard, L, memberList, List.length_flatMap]
  simp only [List.length_map]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  exact Finset.sum_congr rfl fun j _ => hlen j


/-! ## 2. The numbering -/

theorem R_eq : Theorem1.R (hs P) k = Lax496464.Construction.R P k := rfl

/-- The index of a dummy inside its block: element, then set, then segment. -/
def dumIdx (P : Lax496464.HittingSet.Instance) (k : ℕ)
    (r : Fin (Theorem1.R (hs P) k)) (j : Fin P.m) (i : Fin P.n) : ℕ :=
  (i : ℕ) + P.n * (j : ℕ) + (P.m * P.n) * (r : ℕ)

/-- The number of a job: the selection jobs first, then the two dummy blocks. -/
def enc (P : Lax496464.HittingSet.Instance) (k : ℕ) : Theorem1.Jobs (hs P) k → ℕ
  | .inl (r, s) => selPos s + L P * (r : ℕ)
  | .inr (.inl (r, j, i)) => selCount P k + dumIdx P k r j i
  | .inr (.inr (r, j, i)) => selCount P k + dumCount P k + dumIdx P k r j i

theorem dumIdx_eq (r : Fin (Theorem1.R (hs P) k)) (j : Fin P.m) (i : Fin P.n) :
    dumIdx P k r j i = (i : ℕ) + P.n * ((j : ℕ) + P.m * (r : ℕ)) := by
  simp only [dumIdx]; ring

theorem lt_mul (j : Fin P.m) (i : Fin P.n) : (i : ℕ) + P.n * (j : ℕ) < P.m * P.n := by
  have h1 : (i : ℕ) < P.n := i.isLt
  have h2 : (j : ℕ) + 1 ≤ P.m := j.isLt
  calc (i : ℕ) + P.n * (j : ℕ) < P.n * (j : ℕ) + P.n := by omega
    _ = P.n * ((j : ℕ) + 1) := by ring
    _ ≤ P.n * P.m := Nat.mul_le_mul_left _ h2
    _ = P.m * P.n := Nat.mul_comm _ _

theorem dumIdx_lt (r : Fin (Theorem1.R (hs P) k)) (j : Fin P.m) (i : Fin P.n) :
    dumIdx P k r j i < dumCount P k := by
  have hr : (r : ℕ) + 1 ≤ Lax496464.Construction.R P k := r.isLt
  have h := lt_mul j i
  calc dumIdx P k r j i < (P.m * P.n) * (r : ℕ) + P.m * P.n := by
        simp only [dumIdx]; omega
    _ = (P.m * P.n) * ((r : ℕ) + 1) := by ring
    _ ≤ (P.m * P.n) * (Lax496464.Construction.R P k) := Nat.mul_le_mul_left _ hr
    _ = dumCount P k := by simp only [dumCount]; ring

theorem selPos_add_lt (r : Fin (Theorem1.R (hs P) k)) (s : (hs P).SelIdx) :
    selPos s + L P * (r : ℕ) < selCount P k := by
  have hr : (r : ℕ) + 1 ≤ Lax496464.Construction.R P k := r.isLt
  have h := selPos_lt s
  calc selPos s + L P * (r : ℕ) < L P * (r : ℕ) + L P := by omega
    _ = L P * ((r : ℕ) + 1) := by ring
    _ ≤ L P * (Lax496464.Construction.R P k) := Nat.mul_le_mul_left _ hr
    _ = selCount P k := by simp only [selCount, L]; ring

theorem enc_lt (x : Theorem1.Jobs (hs P) k) : enc P k x < numJobs P k := by
  rcases x with ⟨r, s⟩ | ⟨r, j, i⟩ | ⟨r, j, i⟩
  · have := selPos_add_lt r s
    simp only [enc, numJobs]
    omega
  · have := dumIdx_lt r j i
    simp only [enc, numJobs]
    omega
  · have := dumIdx_lt r j i
    simp only [enc, numJobs]
    omega

/-! ## 3. What `slot` makes of a number -/

theorem slot_sel (r : Fin (Theorem1.R (hs P) k)) (s : (hs P).SelIdx) :
    slot P k (enc P k (.inl (r, s))) = (0, (r : ℕ), (s.1 : ℕ), (s.2.val : ℕ)) := by
  have hpos := selPos_lt s
  have hL : 0 < L P := Nat.lt_of_le_of_lt (Nat.zero_le _) hpos
  have hlt := selPos_add_lt r s
  simp only [enc, slot, hlt, if_true]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hpos,
    Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hpos, Nat.zero_add, getD_selPos]

theorem slot_dumA (r : Fin (Theorem1.R (hs P) k)) (j : Fin P.m) (i : Fin P.n) :
    slot P k (enc P k (.inr (.inl (r, j, i)))) = (1, (r : ℕ), (j : ℕ), (i : ℕ)) := by
  have hn : 0 < P.n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hmn : 0 < P.m * P.n := Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_mul j i)
  have hv := dumIdx_lt r j i
  have hnot : ¬ (selCount P k + dumIdx P k r j i < selCount P k) := by omega
  simp only [enc, slot, if_neg hnot, Nat.add_sub_cancel_left, if_pos hv]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [dumIdx]
    rw [Nat.add_mul_div_left _ _ hmn, Nat.div_eq_of_lt (lt_mul j i), Nat.zero_add]
  · simp only [dumIdx]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lt_mul j i),
      Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  · rw [dumIdx_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

theorem slot_dumB (r : Fin (Theorem1.R (hs P) k)) (j : Fin P.m) (i : Fin P.n) :
    slot P k (enc P k (.inr (.inr (r, j, i)))) = (2, (r : ℕ), (j : ℕ), (i : ℕ)) := by
  have hn : 0 < P.n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hmn : 0 < P.m * P.n := Nat.lt_of_le_of_lt (Nat.zero_le _) (lt_mul j i)
  have hv := dumIdx_lt r j i
  have hnot : ¬ (selCount P k + dumCount P k + dumIdx P k r j i < selCount P k) := by omega
  have hsub : selCount P k + dumCount P k + dumIdx P k r j i - selCount P k
      = dumCount P k + dumIdx P k r j i := by omega
  have hnot2 : ¬ (dumCount P k + dumIdx P k r j i < dumCount P k) := by omega
  have hsub2 : dumCount P k + dumIdx P k r j i - dumCount P k = dumIdx P k r j i := by omega
  simp only [enc, slot, if_neg hnot, hsub, if_neg hnot2, hsub2]
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [dumIdx]
    rw [Nat.add_mul_div_left _ _ hmn, Nat.div_eq_of_lt (lt_mul j i), Nat.zero_add]
  · simp only [dumIdx]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (lt_mul j i),
      Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt i.isLt, Nat.zero_add]
  · rw [dumIdx_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]

/-! ## 4. The data of a job are the same under either name -/

theorem jp_enc (x : Theorem1.Jobs (hs P) k) :
    Lax496464.Construction.jp P k (enc P k x) = Theorem1.jp (hs P) k x := by
  rcases x with ⟨r, s⟩ | ⟨r, j, i⟩ | ⟨r, j, i⟩
  · have h := slot_sel r s
    simp [Lax496464.Construction.jp, family, h, Theorem1.jp]
  · have h := slot_dumA r j i
    simp [Lax496464.Construction.jp, family, seg, setIdx, h, Theorem1.jp,
      Lax496464.Construction.g, Theorem1.g]
  · have h := slot_dumB r j i
    simp [Lax496464.Construction.jp, family, seg, setIdx, h, Theorem1.jp,
      Lax496464.Construction.g, Theorem1.g]

theorem jq_enc (x : Theorem1.Jobs (hs P) k) :
    Lax496464.Construction.jq P k (enc P k x) = Theorem1.jq (hs P) k x := by
  rcases x with ⟨r, s⟩ | ⟨r, j, i⟩ | ⟨r, j, i⟩
  · obtain ⟨j, i⟩ := s
    have h := slot_sel r ⟨j, i⟩
    simp [Lax496464.Construction.jq, family, seg, setIdx, h, Theorem1.jq,
      Lax496464.Construction.g, Theorem1.g, Lax496464.Construction.Q, Theorem1.Q]
  · have h := slot_dumA r j i
    simp [Lax496464.Construction.jq, family, seg, setIdx, h, Theorem1.jq,
      Lax496464.Construction.g, Theorem1.g, Lax496464.Construction.Q, Theorem1.Q]
  · have h := slot_dumB r j i
    simp [Lax496464.Construction.jq, family, seg, setIdx, h, Theorem1.jq,
      Lax496464.Construction.g, Theorem1.g, Lax496464.Construction.Q, Theorem1.Q]

theorem jd_enc (x : Theorem1.Jobs (hs P) k) :
    Lax496464.Construction.jd P k (enc P k x) = Theorem1.jd (hs P) k x := by
  rcases x with ⟨r, s⟩ | ⟨r, j, i⟩ | ⟨r, j, i⟩
  · obtain ⟨j, i⟩ := s
    have h := slot_sel r ⟨j, i⟩
    simp [Lax496464.Construction.jd, family, seg, setIdx, elem, h, Theorem1.jd,
      Lax496464.Construction.g, Theorem1.g, Lax496464.Construction.Q, Theorem1.Q,
      Lax496464.Construction.G, Theorem1.G]
  · have h := slot_dumA r j i
    simp [Lax496464.Construction.jd, family, seg, setIdx, elem, h, Theorem1.jd,
      Lax496464.Construction.g, Theorem1.g, Lax496464.Construction.Q, Theorem1.Q,
      Lax496464.Construction.G, Theorem1.G]
  · have h := slot_dumB r j i
    simp [Lax496464.Construction.jd, family, seg, setIdx, elem, h, Theorem1.jd,
      Lax496464.Construction.g, Theorem1.g, Lax496464.Construction.Q, Theorem1.Q,
      Lax496464.Construction.G, Theorem1.G]

/-! ## 5. The numbering is a bijection -/

theorem enc_injective : Function.Injective (enc P k) := by
  intro x y h
  have hslot : slot P k (enc P k x) = slot P k (enc P k y) := by rw [h]
  rcases x with ⟨r, s⟩ | ⟨r, j, i⟩ | ⟨r, j, i⟩ <;>
    rcases y with ⟨r', s'⟩ | ⟨r', j', i'⟩ | ⟨r', j', i'⟩
  · rw [slot_sel, slot_sel] at hslot
    simp only [Prod.mk.injEq, true_and] at hslot
    obtain ⟨hr, -, -⟩ := hslot
    obtain rfl : r = r' := Fin.ext hr
    have h' : selPos s + L P * (r : ℕ) = selPos s' + L P * (r : ℕ) := h
    rw [selPos_injective (by omega : selPos s = selPos s')]
  · rw [slot_sel, slot_dumA] at hslot; simp at hslot
  · rw [slot_sel, slot_dumB] at hslot; simp at hslot
  · rw [slot_dumA, slot_sel] at hslot; simp at hslot
  · rw [slot_dumA, slot_dumA] at hslot
    simp only [Prod.mk.injEq, true_and] at hslot
    obtain ⟨hr, hj, hi⟩ := hslot
    obtain rfl : r = r' := Fin.ext hr
    obtain rfl : j = j' := Fin.ext hj
    obtain rfl : i = i' := Fin.ext hi
    rfl
  · rw [slot_dumA, slot_dumB] at hslot; simp at hslot
  · rw [slot_dumB, slot_sel] at hslot; simp at hslot
  · rw [slot_dumB, slot_dumA] at hslot; simp at hslot
  · rw [slot_dumB, slot_dumB] at hslot
    simp only [Prod.mk.injEq, true_and] at hslot
    obtain ⟨hr, hj, hi⟩ := hslot
    obtain rfl : r = r' := Fin.ext hr
    obtain rfl : j = j' := Fin.ext hj
    obtain rfl : i = i' := Fin.ext hi
    rfl

theorem card_jobs : Fintype.card (Theorem1.Jobs (hs P) k) = numJobs P k := by
  have h1 : Fintype.card (Theorem1.Jobs (hs P) k)
      = Theorem1.R (hs P) k * Fintype.card (hs P).SelIdx
        + (Theorem1.R (hs P) k * (P.m * P.n) + Theorem1.R (hs P) k * (P.m * P.n)) := by
    show Fintype.card ((Fin (Theorem1.R (hs P) k) × (hs P).SelIdx) ⊕
        (Fin (Theorem1.R (hs P) k) × Fin (hs P).m × Fin (hs P).n) ⊕
        (Fin (Theorem1.R (hs P) k) × Fin (hs P).m × Fin (hs P).n)) = _
    simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [h1, ← length_memberList, R_eq]
  simp only [numJobs, selCount, dumCount, L]
  ring

/-- The numbering, as a bijection. -/
noncomputable def jobEquiv : Theorem1.Jobs (hs P) k ≃ Fin (numJobs P k) :=
  Equiv.ofBijective (fun x => (⟨enc P k x, enc_lt x⟩ : Fin (numJobs P k)))
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y h => enc_injective (congrArg Fin.val h), by
        rw [card_jobs, Fintype.card_fin]⟩)

/-- The two namings describe the same shop. -/
noncomputable def iso :
    Iso (Theorem1.inst (hs P) k) (Bridge.model (Lax496464.Construction.construct P k)) where
  e := jobEquiv
  machines := rfl
  pre x := jp_enc x
  proc x := jq_enc x
  due x := jd_enc x
  wt _ := rfl

/-- **The two namings give the same answer.** -/
theorem hasWeight_iff (W : ℕ) :
    (Theorem1.inst (hs P) k).HasWeight W ↔
      Lax496464.FlowShop.Instance.HasWeight (Lax496464.Construction.construct P k) W :=
  (Iso.hasWeight_iff iso W).trans (Bridge.model_hasWeight W)

end Lax496464Proofs.Section8Bridge
