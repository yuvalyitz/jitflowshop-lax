import Lax496464Proofs.Ram.D2Valid
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Theorem 2, Pure Layer 4: How Many Sets of Thresholds There Are

The machine's scan of a set costs `O(|X|)`, and there is a set for every code, so the running time
is `O(Σ_X (|X|+1))` over the sets of at most `m` of the `n` indices.  That sum is at most
`2 (n+1)^m`, which is why no factor `m` appears in Theorem 2's bound.
-/

namespace Lax496464Proofs.Ram.D2Count

open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Scan Lax496464Proofs.Ram.D2Valid

/-- The sets of at most `m` of the indices `0 … n-1`. -/
def KS (n m : ℕ) : Finset (Finset ℕ) :=
  (Finset.range n).powerset.filter (fun X => X.card ≤ m)

theorem KS_zero_left (m : ℕ) : KS 0 m = {∅} := by
  ext X; simp [KS]; rintro rfl; simp

theorem KS_zero_right (n : ℕ) : KS n 0 = {∅} := by
  ext X; simp [KS]; rintro rfl; simp

theorem KS_succ_succ (n m : ℕ) : KS (n + 1) (m + 1) = KS n (m + 1) ∪ (KS n m).image (insert n) := by
  ext X
  simp only [KS, Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, Finset.mem_image,
    Finset.subset_iff, Finset.mem_range]
  constructor
  · rintro ⟨hsub, hcard⟩
    by_cases hn : n ∈ X
    · right
      refine ⟨X.erase n, ⟨?_, ?_⟩, Finset.insert_erase hn⟩
      · intro x hx
        have h1 := hsub (Finset.mem_of_mem_erase hx)
        have h2 := Finset.ne_of_mem_erase hx
        omega
      · rw [Finset.card_erase_of_mem hn]; omega
    · left
      refine ⟨fun x hx => ?_, hcard⟩
      have h1 := hsub hx
      have h2 : x ≠ n := fun h => hn (h ▸ hx)
      omega
  · rintro (⟨hsub, hcard⟩ | ⟨Y, ⟨hsub, hcard⟩, rfl⟩)
    · exact ⟨fun x hx => by have := hsub hx; omega, hcard⟩
    · have hnY : n ∉ Y := fun h => by have := hsub h; omega
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · omega
        · have := hsub hx; omega
      · rw [Finset.card_insert_of_notMem hnY]; omega

theorem KS_disjoint (n m m' : ℕ) : Disjoint (KS n m) ((KS n m').image (insert n)) := by
  rw [Finset.disjoint_left]
  intro X hX hX'
  obtain ⟨Y, -, rfl⟩ := Finset.mem_image.mp hX'
  simp only [KS, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_range] at hX
  have := hX.1 (Finset.mem_insert_self n Y)
  omega

theorem insert_injOn (n m : ℕ) : Set.InjOn (insert n) (↑(KS n m) : Set (Finset ℕ)) := by
  intro Y hY Y' hY' h
  simp only [KS, Finset.coe_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_range,
    Set.mem_ofPred_eq] at hY hY'
  have hnY : n ∉ Y := fun h => by have := hY.1 h; omega
  have hnY' : n ∉ Y' := fun h => by have := hY'.1 h; omega
  have := congrArg (fun Z => Z.erase n) h
  simpa [Finset.erase_insert hnY, Finset.erase_insert hnY'] using this

theorem card_KS_succ_succ (n m : ℕ) :
    (KS (n + 1) (m + 1)).card = (KS n (m + 1)).card + (KS n m).card := by
  rw [KS_succ_succ, Finset.card_union_of_disjoint (KS_disjoint n _ _),
    Finset.card_image_of_injOn (insert_injOn n m)]

theorem sum_KS_succ_succ (n m : ℕ) :
    ∑ X ∈ KS (n + 1) (m + 1), (X.card + 1) =
      ∑ X ∈ KS n (m + 1), (X.card + 1) + (∑ X ∈ KS n m, (X.card + 1) + (KS n m).card) := by
  rw [KS_succ_succ, Finset.sum_union (KS_disjoint n _ _),
    Finset.sum_image (insert_injOn n m)]
  congr 1
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro Y hY
  have hnY : n ∉ Y := by
    simp only [KS, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff,
      Finset.mem_range] at hY
    intro h; have := hY.1 h; omega
  rw [Finset.card_insert_of_notMem hnY]

theorem pow_succ_ge (a k : ℕ) : a ^ (k + 1) + (k + 1) * a ^ k ≤ (a + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : (a + 1) ^ (k + 1 + 1) = (a + 1) * (a + 1) ^ (k + 1) := by ring
    have h2 : a ^ (k + 1 + 1) = a * a ^ (k + 1) := by ring
    have h3 : a ^ (k + 1) = a * a ^ k := by ring
    rw [h1]
    nlinarith [Nat.zero_le (a ^ k), Nat.zero_le a, Nat.zero_le (k * a ^ k)]

theorem card_and_sum_le (n : ℕ) :
    ∀ m, (KS n m).card ≤ (n + 1) ^ m ∧ ∑ X ∈ KS n m, (X.card + 1) ≤ 2 * (n + 1) ^ m := by
  induction n with
  | zero => intro m; rw [KS_zero_left]; simp
  | succ n ih =>
    intro m
    cases m with
    | zero => rw [KS_zero_right]; simp
    | succ m =>
      obtain ⟨hS1, hT1⟩ := ih (m + 1)
      obtain ⟨hS0, hT0⟩ := ih m
      rw [card_KS_succ_succ, sum_KS_succ_succ]
      have hpg := pow_succ_ge (n + 1) m
      have hpos : 0 < (n + 1) ^ m := pow_pos (by omega) m
      have hp1 : (n + 1) ^ (m + 1) = (n + 1) * (n + 1) ^ m := by ring
      refine ⟨?_, ?_⟩
      · have : (n + 1 + 1) ^ (m + 1) ≥ (n + 1) ^ (m + 1) + (n + 1) ^ m := by
          have := Nat.mul_le_mul_right ((n + 1) ^ m) (show 1 ≤ m + 1 by omega)
          nlinarith
        omega
      · cases m with
        | zero =>
          rw [KS_zero_right] at hT0 hS0 ⊢
          simp only [Finset.card_singleton, Finset.sum_singleton, Finset.card_empty] at hT0 hS0 ⊢
          have : (n + 1 + 1) ^ (0 + 1) = n + 2 := by ring
          rw [this] at *
          simp only [pow_zero] at *
          omega
        | succ m' =>
          have hm : 2 ≤ m' + 1 + 1 := by omega
          have h2 : 2 * (n + 1) ^ (m' + 1) ≤ (m' + 1 + 1) * (n + 1) ^ (m' + 1) :=
            Nat.mul_le_mul_right _ hm
          omega

open Classical in
/-- The number of thresholds of the set whose code is `c` (`0` if `c` is not a code). -/
noncomputable def lenOf (n m c : ℕ) : ℕ :=
  if h : IsCode n m c then (Classical.choose h).length else 0

theorem lenOf_eq {n m c : ℕ} {Zs : List ℕ} (h : SL n m Zs) (hc : codeL n m Zs = c) :
    lenOf n m c = Zs.length := by
  have hic : IsCode n m c := ⟨Zs, h, hc⟩
  unfold lenOf
  rw [dif_pos hic]
  have hspec := Classical.choose_spec hic
  have := SL.codeL_inj hspec.1 h (hspec.2.trans hc.symm)
  rw [this]

/-- The sum of `|X| + 1 + R` over the codes of sets is at most `(2 + R) (n+1)^m`. -/
theorem sum_codes_le (n m R : ℕ) :
    ∑ c ∈ Finset.range ((n + 1) ^ m),
      (open Classical in if IsCode n m c then lenOf n m c + 1 + R else 0) ≤ (2 + R) * (n + 1) ^ m := by
  classical
  set N := (n + 1) ^ m with hN
  set Sc := (Finset.range N).filter (fun c => IsCode n m c) with hSc
  have h1 : ∑ c ∈ Finset.range N, (if IsCode n m c then lenOf n m c + 1 + R else 0) =
      ∑ c ∈ Sc, (lenOf n m c + 1 + R) := by
    rw [hSc, Finset.sum_filter]
  rw [h1]
  -- the map from a code to its set
  let φ : ℕ → Finset ℕ := fun c => if h : IsCode n m c then (Classical.choose h).toFinset else ∅
  have hφ : ∀ c ∈ Sc, ∃ Zs, SL n m Zs ∧ codeL n m Zs = c ∧ φ c = Zs.toFinset := by
    intro c hc
    have hic : IsCode n m c := (Finset.mem_filter.mp hc).2
    refine ⟨Classical.choose hic, (Classical.choose_spec hic).1, (Classical.choose_spec hic).2, ?_⟩
    simp only [φ, dif_pos hic]
  have hnd : ∀ Zs : List ℕ, SL n m Zs → Zs.Nodup := fun Zs hsl =>
    (List.sortedLT_iff_pairwise.mp hsl.sorted).imp (fun {a b} h => ne_of_lt h)
  have hcard : ∀ c ∈ Sc, lenOf n m c + 1 + R = (φ c).card + 1 + R := by
    intro c hc
    obtain ⟨Zs, hsl, hcode, hφc⟩ := hφ c hc
    rw [lenOf_eq hsl hcode, hφc, List.toFinset_card_of_nodup (hnd Zs hsl)]
  have hinj : Set.InjOn φ (↑Sc : Set ℕ) := by
    intro c hc c' hc' he
    obtain ⟨Zs, hsl, hcode, hφc⟩ := hφ c hc
    obtain ⟨Zs', hsl', hcode', hφc'⟩ := hφ c' hc'
    rw [hφc, hφc'] at he
    have hZ : Zs = Zs' := List.SortedLT.eq_of_mem_iff hsl.sorted hsl'.sorted (fun a => by
      have := Finset.ext_iff.mp he a
      simpa using this)
    rw [← hcode, ← hcode', hZ]
  have hsub : Sc.image φ ⊆ KS n m := by
    intro X hX
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hX
    obtain ⟨Zs, hsl, hcode, hφc⟩ := hφ c hc
    rw [hφc]
    simp only [KS, Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff, Finset.mem_range,
      List.mem_toFinset]
    refine ⟨fun x hx => hsl.lt x hx, ?_⟩
    exact le_trans (List.toFinset_card_le Zs) hsl.len
  rw [Finset.sum_congr rfl hcard, ← Finset.sum_image hinj (f := fun X : Finset ℕ => X.card + 1 + R)]
  refine le_trans (Finset.sum_le_sum_of_subset hsub) ?_
  have hb := card_and_sum_le n m
  have : ∑ X ∈ KS n m, (X.card + 1 + R) = ∑ X ∈ KS n m, (X.card + 1) + ∑ X ∈ KS n m, R := by
    rw [← Finset.sum_add_distrib]
  rw [this, Finset.sum_const, smul_eq_mul]
  have h2 : (KS n m).card * R ≤ (n + 1) ^ m * R := Nat.mul_le_mul_right _ hb.1
  nlinarith [hb.2]

end Lax496464Proofs.Ram.D2Count
