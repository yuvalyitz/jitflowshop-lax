import Lax496464.WH_C2_HittingSet
import Mathlib.Data.Nat.Size

/-! # The words of Hitting Set

A Hitting Set word (`WH_C2_HittingSet.word`) is the binary encoding `encodeInstance P k` written as
zeros and ones. This file gives it a closed form in terms of the self-delimiting code of a number
(`bitsNat`: `n.size` ones, a zero, the `n.size` binary digits least significant first), and proves
that the word determines the instance and the solution size (`word_inj`), so that the parameter of
a word is its `k` (`sizeParam_word`) and its answer is that of its instance (`yes_word_iff`).

The prefix-freeness argument is the one of the archive's just-in-time flow shop submission
(`lax-496464`, `HittingSet/Injective.lean`), repeated here. -/

namespace Lax496464Proofs.WHierarchy.HittingSet.Words

open Lax496464.HittingSet Lax434930.PolynomialTime Lax496464.WH_C2_HittingSet

/-! ## Numbers as zeros and ones -/

/-- A binary word as a list of zeros and ones. -/
def natBits (w : Word) : List ℕ := w.map fun b => if b then 1 else 0

/-- The `i`-th binary digit of `n`. -/
def digit (n i : ℕ) : ℕ := n / 2 ^ i % 2

/-- The self-delimiting code of a number, as zeros and ones. -/
def bitsNat (n : ℕ) : List ℕ :=
  List.replicate n.size 1 ++ [0] ++ (List.range n.size).map (digit n)

theorem word_eq_natBits (P : Instance) (k : ℕ) : word P k = natBits (encodeInstance P k) := rfl

theorem bits_eq_digits (n : ℕ) :
    n.bits.map (fun b => if b then 1 else 0) = (List.range n.size).map (digit n) := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
      by_cases hz : Nat.bit b n = 0
      · rw [hz]; simp
      · rw [Nat.bits_append_bit n b h, Nat.size_bit hz, List.range_succ_eq_map, List.map_cons,
          List.map_cons, List.map_map, ih]
        congr 1
        · cases b <;> simp [digit, Nat.bit_val]
        · refine List.map_congr_left fun i _ => ?_
          simp only [Function.comp, digit, pow_succ]
          rw [Nat.mul_comm, ← Nat.div_div_eq_div_mul]
          congr 2
          cases b <;> (simp [Nat.bit_val]; try omega)

theorem natBits_encodeNat (n : ℕ) : natBits (encodeNat n) = bitsNat n := by
  simp only [natBits, encodeNat, bitsNat, List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [bits_eq_digits, Nat.size_eq_bits_len]
  simp

@[simp] theorem length_bitsNat (n : ℕ) : (bitsNat n).length = 2 * n.size + 1 := by
  simp [bitsNat]; omega

theorem natBits_append (a b : Word) : natBits (a ++ b) = natBits a ++ natBits b := by
  simp [natBits]

theorem natBits_flatMap {α : Type} (l : List α) (f : α → Word) :
    natBits (l.flatMap f) = l.flatMap fun a => natBits (f a) := by
  simp [natBits, List.map_flatMap]

/-- The digits determine the number. -/
theorem sum_digit (n : ℕ) :
    ∑ i ∈ Finset.range n.size, digit n i * 2 ^ i = n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n' h ih =>
      by_cases hz : Nat.bit b n' = 0
      · simp [hz]
      · rw [Nat.size_bit hz, Finset.sum_range_succ']
        have hd0 : digit (Nat.bit b n') 0 = b.toNat := by
          rcases b <;> simp [digit, Nat.bit_val]
        have hdiv : Nat.bit b n' / 2 = n' := by
          rw [Nat.bit_val]; rcases b <;> (simp; try omega)
        have hdi : ∀ i, digit (Nat.bit b n') (i + 1) = digit n' i := by
          intro i
          unfold digit
          rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
        have hsum : ∑ i ∈ Finset.range n'.size, digit (Nat.bit b n') (i + 1) * 2 ^ (i + 1)
            = 2 * ∑ i ∈ Finset.range n'.size, digit n' i * 2 ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hdi]; ring
        rw [hsum, ih, hd0, pow_zero, mul_one, Nat.bit_val]

/-- A number's bit length never exceeds the number. -/
theorem size_le_self (v : ℕ) : v.size ≤ v := by
  induction v using Nat.binaryRec' with
  | zero => simp
  | bit b n h ih =>
      by_cases hz : Nat.bit b n = 0
      · simp [hz]
      · rw [Nat.size_bit hz]
        have hz' : 2 * n + b.toNat ≠ 0 := by rw [← Nat.bit_val]; exact hz
        have hbn : b.toNat ≤ 1 := by rcases b <;> simp
        rw [Nat.bit_val]
        omega

theorem digit_le_one (n i : ℕ) : digit n i ≤ 1 := by
  unfold digit; have := Nat.mod_lt (n / 2 ^ i) (show 0 < 2 by norm_num); omega

/-! ## Prefix-freeness -/

/-- Reading a binary word back as a number. -/
def ofBits : List Bool → ℕ := List.foldr (fun b n => Nat.bit b n) 0

theorem ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [ofBits]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [ofBits, List.foldr_cons] at ih ⊢
    rw [ih]

theorem bits_injective : Function.Injective Nat.bits := fun a b h => by
  rw [← ofBits_bits a, ← ofBits_bits b, h]

theorem replicate_true_inj (a b : ℕ) (u v : Word)
    (h : List.replicate a true ++ false :: u = List.replicate b true ++ false :: v) :
    a = b ∧ u = v := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa using h
    | succ b => simp [List.replicate_succ] at h
  | succ a ih =>
    cases b with
    | zero => simp [List.replicate_succ] at h
    | succ b =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih b h
      exact ⟨by omega, h2⟩

/-- **The number code is prefix-free.** -/
theorem peel {a b : ℕ} {x y : Word} (h : encodeNat a ++ x = encodeNat b ++ y) :
    a = b ∧ x = y := by
  simp only [encodeNat, List.append_assoc, List.singleton_append] at h
  obtain ⟨hl, hr⟩ := replicate_true_inj _ _ _ _ h
  obtain ⟨hb, hxy⟩ := List.append_inj hr hl
  exact ⟨bits_injective hb, hxy⟩

/-! ## Injectivity of the instance encoding -/

/-- A set as a word: its size then its members. -/
def setWord (c : ℕ) (l : List ℕ) : Word := encodeNat c ++ l.flatMap encodeNat

/-- A family as a word. -/
def famWord (cs : List (ℕ × List ℕ)) : Word := cs.flatMap fun s => setWord s.1 s.2

/-- The sets of an instance, as sizes and member lists. -/
def setsOf (P : Instance) : List (ℕ × List ℕ) :=
  (List.finRange P.m).map fun j => ((P.F j).card, (P.members j).map Fin.val)

theorem encodeInstance_eq (P : Instance) (k : ℕ) :
    encodeInstance P k =
      encodeNat P.n ++ (encodeNat P.m ++ (encodeNat k ++ famWord (setsOf P))) := by
  unfold encodeInstance famWord setsOf setWord
  simp only [List.append_assoc, List.flatMap_map, bind_pure_comp, List.map_eq_map]

theorem flatMap_peel : ∀ (l l' : List ℕ) (x y : Word), l.length = l'.length →
    l.flatMap encodeNat ++ x = l'.flatMap encodeNat ++ y → l = l' ∧ x = y
  | [], [], x, y, _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | a :: l, b :: l', x, y, hl, h => by
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := peel h
      obtain ⟨rfl, rfl⟩ := flatMap_peel l l' x y (by simpa using hl) h2
      exact ⟨rfl, rfl⟩

theorem famWord_peel : ∀ (cs cs' : List (ℕ × List ℕ)) (x y : Word), cs.length = cs'.length →
    (∀ s ∈ cs, s.1 = s.2.length) → (∀ s ∈ cs', s.1 = s.2.length) →
    famWord cs ++ x = famWord cs' ++ y → cs = cs' ∧ x = y
  | [], [], x, y, _, _, _, h => ⟨rfl, by simpa [famWord] using h⟩
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | s :: cs, s' :: cs', x, y, hl, h1, h2, h => by
      simp only [famWord, List.flatMap_cons, List.append_assoc, setWord] at h
      obtain ⟨hc, h3⟩ := peel h
      have e1 := h1 s (List.mem_cons_self ..)
      have e2 := h2 s' (List.mem_cons_self ..)
      obtain ⟨hm, h4⟩ := flatMap_peel s.2 s'.2 _ _ (by rw [← e1, ← e2, hc]) h3
      obtain ⟨rfl, rfl⟩ := famWord_peel cs cs' x y (by simpa using hl)
        (fun t ht => h1 t (List.mem_cons_of_mem _ ht))
        (fun t ht => h2 t (List.mem_cons_of_mem _ ht)) h4
      exact ⟨by rw [Prod.ext_iff.mpr ⟨hc, hm⟩], rfl⟩

theorem card_eq_length_members (P : Instance) (j : Fin P.m) :
    (P.F j).card = (P.members j).length := by
  rw [← Finset.univ_inter (P.F j), ← Finset.filter_mem_eq_inter, Finset.card_def,
    Finset.filter_val, Fin.univ_def]
  rfl

theorem setsOf_sizes (P : Instance) : ∀ s ∈ setsOf P, s.1 = s.2.length := by
  intro s hs
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hs
  simp only [List.length_map]
  exact card_eq_length_members P j

theorem mem_members_iff (P : Instance) (j : Fin P.m) (i : Fin P.n) :
    i ∈ P.members j ↔ i ∈ P.F j := by
  simp [Instance.members]

/-- Two instances of the same dimensions with the same member lists are equal. -/
theorem instance_ext {P P' : Instance} (hn : P.n = P'.n) (hm : P.m = P'.m)
    (hs : setsOf P = setsOf P') : P = P' := by
  obtain ⟨n, m, F⟩ := P
  obtain ⟨n', m', F'⟩ := P'
  simp only at hn hm
  subst hn hm
  congr
  funext j
  have hj : ((F j).card, (Instance.members ⟨n, m, F⟩ j).map Fin.val) =
      ((F' j).card, (Instance.members ⟨n, m, F'⟩ j).map Fin.val) := by
    have h1 := congrArg (fun l => l.getD (j : ℕ) (0, [])) hs
    simp only [setsOf] at h1
    rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getD_eq_getElem _ _ (by simp [j.isLt]),
      List.getElem_map, List.getElem_map, List.getElem_finRange] at h1
    exact h1
  have hm := (Prod.mk.inj hj).2
  ext i
  have h1 := mem_members_iff ⟨n, m, F⟩ j i
  have h2 := mem_members_iff ⟨n, m, F'⟩ j i
  simp only at h1 h2
  rw [← h1, ← h2]
  have : (i : ℕ) ∈ List.map Fin.val (Instance.members ⟨n, m, F⟩ j) ↔
      (i : ℕ) ∈ List.map Fin.val (Instance.members ⟨n, m, F'⟩ j) := by rw [hm]
  simpa [List.mem_map, Fin.val_inj] using this

/-- The binary encoding is injective. -/
theorem encodeInstance_inj {P P' : Instance} {k k' : ℕ}
    (h : encodeInstance P k = encodeInstance P' k') : P = P' ∧ k = k' := by
  rw [encodeInstance_eq, encodeInstance_eq] at h
  obtain ⟨hn, h⟩ := peel h
  obtain ⟨hm, h⟩ := peel h
  obtain ⟨hk, h⟩ := peel h
  have hlen : (setsOf P).length = (setsOf P').length := by simp [setsOf, hm]
  obtain ⟨hs, -⟩ := famWord_peel (setsOf P) (setsOf P') [] [] hlen (setsOf_sizes P)
    (setsOf_sizes P') (by simpa using h)
  exact ⟨instance_ext hn hm hs, hk⟩

theorem natBits_injective : Function.Injective natBits := by
  intro a b h
  unfold natBits at h
  refine List.map_injective_iff.mpr ?_ h
  intro u v huv
  cases u <;> cases v <;> simp_all

/-! ## The word determines the instance -/

/-- **A Hitting Set word determines its instance and its solution size.** -/
theorem word_inj {P P' : Instance} {k k' : ℕ} (h : word P k = word P' k') :
    P = P' ∧ k = k' :=
  encodeInstance_inj (natBits_injective h)

/-- Two equal words have the same answer. -/
theorem hasHittingSet_iff_of_word_eq {P P' : Instance} {k k' : ℕ} (h : word P k = word P' k') :
    P.HasHittingSet k ↔ P'.HasHittingSet k' := by
  obtain ⟨rfl, rfl⟩ := word_inj h
  exact Iff.rfl

theorem word_mem_domain (P : Instance) (k : ℕ) : word P k ∈ HittingSet.Domain := ⟨P, k, rfl⟩

/-- **The parameter of a word is its solution size.** -/
theorem sizeParam_word (P : Instance) (k : ℕ) : sizeParam (word P k) = k := by
  have h : ∃ p : Instance × ℕ, word P k = word p.1 p.2 := ⟨(P, k), rfl⟩
  unfold sizeParam
  rw [dif_pos h]
  exact ((word_inj (Classical.choose_spec h)).2).symm

theorem param_word (P : Instance) (k : ℕ) : HittingSet.param (word P k) = k :=
  sizeParam_word P k

/-- **The answer of a word is that of its instance.** -/
theorem yes_word_iff (P : Instance) (k : ℕ) : HittingSet.Yes (word P k) ↔ P.HasHittingSet k := by
  constructor
  · rintro ⟨P', k', h, hy⟩
    exact (hasHittingSet_iff_of_word_eq h).mpr hy
  · intro h
    exact ⟨P, k, rfl, h⟩

end Lax496464Proofs.WHierarchy.HittingSet.Words
