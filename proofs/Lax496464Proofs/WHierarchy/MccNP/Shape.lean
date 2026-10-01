import Mathlib.Tactic.Linarith
import Lax496464.WH_F1_IndependentSetMatrix
import Lax496464.WH_F2_MccConstruction

/-!
# The words of Independent Set instances

`Valid` states that a word has the form `1^n 0 · (n² entries) · 1^k 0` with a symmetric `0/1`
matrix of zero diagonal; `decode` recovers the instance. The word of an instance, its order,
threshold and adjacency agree with those read off the word.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Shape

open Lax496464.WH_F1_IndependentSetMatrix Lax762056.GraphEncoding
open Lax496464.WH_F2_MccConstruction (adjG)

/-- `n`: the run of ones at the start of the word. -/
def order (x : List ℕ) : ℕ := (x.takeWhile fun v => v == 1).length

/-- The matrix entry `(u, v)`. -/
def entry (x : List ℕ) (u v : ℕ) : ℕ := x.getD (order x + 1 + u * order x + v) 0

/-- `k`: the run of ones after the matrix. -/
def kOf (x : List ℕ) : ℕ :=
  ((x.drop (order x + 1 + order x * order x)).takeWhile fun v => v == 1).length

/-- The word has the shape of an encoding: a run of `n` ones and a zero, `n²` entries that are
0 or 1, symmetric with zero diagonal, a run of `k` ones, and a final zero, and nothing else. -/
def Valid (x : List ℕ) : Prop :=
  x.getD (order x) 0 = 0 ∧
  x.length = order x + 1 + order x * order x + kOf x + 1 ∧
  x.getD (order x + 1 + order x * order x + kOf x) 0 = 0 ∧
  (∀ u < order x, ∀ v < order x, entry x u v ≤ 1 ∧ entry x u v = entry x v u) ∧
  (∀ u < order x, entry x u u = 0)

open Classical in
/-- The instance a valid word presents (an arbitrary one for an invalid word). -/
noncomputable def decode (x : List ℕ) : Instance :=
  if h : x ∈ Instances then Classical.choose h else ⟨0, ⊥, 0⟩

open Classical

private lemma takeWhile_run (k : ℕ) (r : List ℕ) :
    ((List.replicate k 1 ++ 0 :: r).takeWhile fun v => v == 1).length = k := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ]

private lemma getD_flatMap_const {α β : Type _} (f : α → List β) (n : ℕ) (hf : ∀ a, (f a).length = n)
    (d : β) (l : List α) : ∀ (i j : ℕ) (hi : i < l.length) (_hj : j < n),
    (l.flatMap f).getD (i*n+j) d = (f l[i]).getD j d := by
  induction l with
  | nil => intro i j hi; simp at hi
  | cons a l ih =>
    intro i j hi hj
    cases i with
    | zero =>
      simp only [List.flatMap_cons, List.getD_eq_getElem?_getD, zero_mul, zero_add,
        List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [hf]; exact hj)]
    | succ i =>
      have hi' : i < l.length := by simpa using hi
      have : (i+1)*n+j = (f a).length + (i*n+j) := by rw [hf]; ring
      simp only [List.flatMap_cons, List.getD_eq_getElem?_getD, this, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      have := ih i j hi' hj
      simpa [List.getD_eq_getElem?_getD] using this

private lemma adjG_fin (I : Instance) (u v : Fin I.order) :
    adjG I u.val v.val = decide (I.graph.Adj u v) := by
  simp [adjG]

/-- the matrix part of the word -/
private noncomputable def mat (I : Instance) : List ℕ :=
  (List.finRange I.order).flatMap fun u => (List.finRange I.order).map fun v =>
    if adjG I u.val v.val then 1 else 0

private lemma word_eq (I : Instance) :
    word I = List.replicate I.order 1 ++ 0 :: (mat I ++ (List.replicate I.threshold 1 ++ [0])) := by
  simp only [word, encode, unary, mat, List.map_append, List.map_replicate, List.map_flatMap, List.map_map, List.map_cons, List.map_nil]
  simp only [bitNat, adjG_fin]
  simp
  simp [Function.comp_def, bitNat]


private lemma mat_length (I : Instance) : (mat I).length = I.order * I.order := by
  simp [mat, List.length_flatMap]

private lemma getD_mat (I : Instance) (u v : ℕ) (hu : u < I.order) (hv : v < I.order) :
    (mat I).getD (u * I.order + v) 0 = if adjG I u v then 1 else 0 := by
  unfold mat
  rw [getD_flatMap_const _ I.order (by simp) 0 _ u v (by simpa using hu) hv]
  simp [hv]

private lemma getD_rep (n i : ℕ) : (List.replicate n 1 ++ [0]).getD i 0 = if i < n then 1 else 0 := by
  by_cases h : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [h, List.getD_eq_getElem?_getD]
  · rw [if_neg h]
    by_cases h2 : i = n
    · subst h2
      rw [List.getD_append_right _ _ _ _ (by simp)]; simp
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; simp

private lemma word_getD (I : Instance) (i : ℕ) : (word I).getD i 0 =
    if i < I.order then 1
    else if i < I.order + 1 then 0
    else if i < I.order + 1 + I.order * I.order then
      (if adjG I ((i - (I.order + 1)) / I.order) ((i - (I.order + 1)) % I.order) then 1 else 0)
    else if i < I.order + 1 + I.order * I.order + I.threshold then 1 else 0 := by
  have hw : word I = (List.replicate I.order 1 ++ [0]) ++ (mat I ++ (List.replicate I.threshold 1 ++ [0])) := by
    rw [word_eq]; simp
  rw [hw]
  by_cases h1 : i < I.order + 1
  · rw [List.getD_append _ _ _ _ (by simpa using h1), getD_rep]
    by_cases h : i < I.order
    · simp [h]
    · simp [h, h1]
  · rw [List.getD_append_right _ _ _ _ (by simpa using h1)]
    simp only [List.length_append, List.length_replicate, List.length_singleton]
    have hn1 : ¬ i < I.order := by omega
    rw [if_neg hn1, if_neg h1]
    by_cases h2 : i - (I.order + 1) < I.order * I.order
    · rw [List.getD_append _ _ _ _ (by rw [mat_length]; exact h2)]
      have hn : 0 < I.order := by
        rcases Nat.eq_zero_or_pos I.order with h | h
        · rw [h] at h2; simp at h2
        · exact h
      have hu : (i - (I.order + 1)) / I.order < I.order := Nat.div_lt_of_lt_mul (by simpa [mul_comm] using h2)
      have hv := Nat.mod_lt (i - (I.order + 1)) hn
      have := getD_mat I _ _ hu hv
      rw [Nat.div_add_mod'] at this
      rw [this, if_pos (show i < I.order + 1 + I.order * I.order by omega)]
    · have h2' : ¬ i < I.order + 1 + I.order * I.order := by omega
      rw [if_neg h2', List.getD_append_right _ _ _ _ (by rw [mat_length]; omega), mat_length, getD_rep]
      have : i - (I.order + 1) - I.order * I.order = i - (I.order + 1 + I.order * I.order) := by omega
      rw [this]
      by_cases h3 : i < I.order + 1 + I.order * I.order + I.threshold
      · rw [if_pos h3, if_pos (by omega)]
      · rw [if_neg h3, if_neg (by omega)]

private lemma word_length (I : Instance) :
    (word I).length = I.order + 1 + I.order * I.order + I.threshold + 1 := by
  rw [word_eq]; simp [mat_length]; ring

private lemma order_word (I : Instance) : order (word I) = I.order := by
  rw [order, word_eq, takeWhile_run]

private lemma kOf_word (I : Instance) : kOf (word I) = I.threshold := by
  have hw : word I = (List.replicate I.order 1 ++ 0 :: mat I) ++ (List.replicate I.threshold 1 ++ [0]) := by
    rw [word_eq]; simp
  have hl : (List.replicate I.order 1 ++ 0 :: mat I).length = I.order + 1 + I.order * I.order := by
    simp [mat_length]; ring
  rw [kOf, order_word, hw, ← hl, List.drop_left]
  simp

private lemma entry_word (I : Instance) (u v : ℕ) (hu : u < I.order) (hv : v < I.order) :
    entry (word I) u v = if adjG I u v then 1 else 0 := by
  have hn : 0 < I.order := by omega
  rw [entry, order_word, word_getD]
  have h1 : I.order + 1 + u * I.order + v - (I.order + 1) = u * I.order + v := by omega
  have hdiv : (u * I.order + v) / I.order = u := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hv, zero_add]
  have hmod : (u * I.order + v) % I.order = v := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
  have hlt : u * I.order + v < I.order * I.order := by nlinarith
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), h1, hdiv, hmod]


private lemma adjG_iff (I : Instance) (u v : ℕ) (hu : u < I.order) (hv : v < I.order) :
    adjG I u v = true ↔ I.graph.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  simp [adjG, hu, hv]

private lemma adjG_comm (I : Instance) (u v : ℕ) : adjG I u v = adjG I v u := by
  unfold adjG
  simp only [decide_eq_decide]
  constructor <;> rintro ⟨hu, hv, h⟩
  · exact ⟨hv, hu, h.symm⟩
  · exact ⟨hv, hu, h.symm⟩

private lemma adjG_self (I : Instance) (u : ℕ) : adjG I u u = false := by
  simp [adjG]

private lemma tw_getD (x : List ℕ) (i : ℕ) (h : i < (x.takeWhile fun v => v == 1).length) :
    x.getD i 0 = 1 := by
  induction x generalizing i with
  | nil => simp at h
  | cons a t ih =>
    by_cases ha : a = 1
    · subst ha
      cases i with
      | zero => simp
      | succ i =>
        simp only [List.takeWhile_cons, beq_self_eq_true, if_true, List.length_cons] at h
        simpa using ih i (by omega)
    · simp [ha] at h

private lemma valid_word (I : Instance) : Valid (word I) := by
  unfold Valid
  rw [order_word, kOf_word]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [word_getD, if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _)]
  · exact word_length I
  · rw [word_getD, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · intro u hu v hv
    rw [entry_word I u v hu hv, entry_word I v u hv hu, adjG_comm I u v]
    refine ⟨?_, rfl⟩
    split_ifs <;> omega
  · intro u hu
    rw [entry_word I u u hu hu, adjG_self]; simp

/-- The instance read off a valid word. -/
@[reducible] private noncomputable def ofValid (x : List ℕ) : Instance :=
  ⟨order x, SimpleGraph.fromRel (fun u v : Fin (order x) => entry x u v = 1), kOf x⟩

private lemma ofValid_order (x : List ℕ) : (ofValid x).order = order x := rfl
private lemma ofValid_threshold (x : List ℕ) : (ofValid x).threshold = kOf x := rfl
private lemma ofValid_adj (x : List ℕ) (a b : Fin (order x)) :
    (ofValid x).graph.Adj a b ↔ a ≠ b ∧ (entry x a b = 1 ∨ entry x b a = 1) :=
  SimpleGraph.fromRel_adj _ _ _

private lemma adjG_ofValid {x : List ℕ} (h : Valid x) (u v : ℕ) :
    adjG (ofValid x) u v = decide (u < order x ∧ v < order x ∧ entry x u v = 1) := by
  unfold adjG
  simp only [decide_eq_decide]
  constructor
  · rintro ⟨hu, hv, hne, he⟩
    refine ⟨hu, hv, ?_⟩
    rcases he with he | he
    · exact he
    · exact (h.2.2.2.1 u hu v hv).2.trans he
  · rintro ⟨hu, hv, he⟩
    refine ⟨hu, hv, ?_⟩
    rw [ofValid_adj]
    refine ⟨?_, Or.inl he⟩
    intro heq
    have : u = v := by simpa using congrArg Fin.val heq
    subst this
    have := h.2.2.2.2 u hu
    omega

private lemma word_ofValid {x : List ℕ} (h : Valid x) : word (ofValid x) = x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hv : Valid x := ⟨h1, h2, h3, h4, h5⟩
  have hlen : (word (ofValid x)).length = x.length := by
    rw [word_length, ofValid_order, ofValid_threshold]; omega
  refine List.ext_getElem hlen fun i hi1 hi2 => ?_
  suffices hs : (word (ofValid x)).getD i 0 = x.getD i 0 by
    simpa [List.getD_eq_getElem?_getD, hi1, hi2] using hs
  rw [word_getD]
  change (if i < order x then 1
    else if i < order x + 1 then 0
    else if i < order x + 1 + order x * order x then
      (if adjG (ofValid x) ((i - (order x + 1)) / order x) ((i - (order x + 1)) % order x) then 1 else 0)
    else if i < order x + 1 + order x * order x + kOf x then 1 else 0) = x.getD i 0
  by_cases c1 : i < order x
  · rw [if_pos c1]; exact (tw_getD x i c1).symm
  rw [if_neg c1]
  by_cases c2 : i < order x + 1
  · rw [if_pos c2]
    have : i = order x := by omega
    subst this; exact h1.symm
  rw [if_neg c2]
  by_cases c3 : i < order x + 1 + order x * order x
  · rw [if_pos c3, adjG_ofValid hv]
    have hn : 0 < order x := by
      rcases Nat.eq_zero_or_pos (order x) with h | h
      · rw [h] at c3; omega
      · exact h
    have hu : (i - (order x + 1)) / order x < order x :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have hw := Nat.mod_lt (i - (order x + 1)) hn
    have he : entry x ((i - (order x + 1)) / order x) ((i - (order x + 1)) % order x) = x.getD i 0 := by
      unfold entry
      have := Nat.div_add_mod' (i - (order x + 1)) (order x)
      have e : order x + 1 + (i - (order x + 1)) / order x * order x + (i - (order x + 1)) % order x = i := by
        omega
      rw [e]
    have hle := (h4 _ hu _ hw).1
    rw [he] at hle ⊢
    generalize x.getD i 0 = a at hle ⊢
    have : a = 0 ∨ a = 1 := by omega
    rcases this with rfl | rfl <;> simp [hu, hw]
  rw [if_neg c3]
  by_cases c4 : i < order x + 1 + order x * order x + kOf x
  · rw [if_pos c4]
    have hd : x.getD i 0 = (x.drop (order x + 1 + order x * order x)).getD
        (i - (order x + 1 + order x * order x)) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2; omega
    rw [hd, tw_getD]
    show _ < kOf x
    omega
  · rw [if_neg c4]
    have : i = order x + 1 + order x * order x + kOf x := by omega
    subst this; exact h3.symm

private lemma exists_zero_head (I : Instance) :
    ∃ r, (mat I).reverse ++ 0 :: List.replicate I.order 1 = 0 :: r := by
  rcases Nat.eq_zero_or_pos I.order with h0 | hpos
  · have : mat I = [] := List.length_eq_zero_iff.mp (by rw [mat_length, h0])
    rw [this]; exact ⟨_, rfl⟩
  · have hlen : (mat I).reverse.length = I.order * I.order := by simp [mat_length]
    cases hm : (mat I).reverse with
    | nil =>
      exfalso
      rw [hm] at hlen
      simp at hlen
      omega
    | cons a r =>
      have h1 : (mat I).reverse[0]? = some a := by rw [hm]; rfl
      rw [List.getElem?_reverse (by rw [mat_length]; positivity)] at h1
      have h2 := getD_mat I (I.order - 1) (I.order - 1) (by omega) (by omega)
      rw [adjG_self] at h2
      have hidx : (mat I).length - 1 - 0 = (I.order - 1) * I.order + (I.order - 1) := by
        rw [mat_length]
        obtain ⟨m, hm'⟩ : ∃ m, I.order = m + 1 := ⟨I.order - 1, by omega⟩
        rw [hm']
        simp only [Nat.add_sub_cancel]
        have : (m + 1) * (m + 1) = m * (m + 1) + m + 1 := by ring
        omega
      rw [hidx] at h1
      rw [List.getD_eq_getElem?_getD, h1] at h2
      have ha : a = 0 := by simpa using h2
      exact ⟨r ++ 0 :: List.replicate I.order 1, by simp [ha]⟩

/-- The encoding is injective. -/
theorem word_injective : Function.Injective word := by
  intro I J h
  have hn : I.order = J.order := by rw [← order_word I, ← order_word J, h]
  have hk : I.threshold = J.threshold := by rw [← kOf_word I, ← kOf_word J, h]
  obtain ⟨n, G, k⟩ := I
  obtain ⟨n', G', k'⟩ := J
  simp only at hn hk
  subst hn hk
  have hG : G = G' := by
    ext u v
    have e := congrArg (fun w => entry w u.val v.val) h
    rw [entry_word ⟨n, G, k⟩ u v u.isLt v.isLt, entry_word ⟨n, G', k⟩ u v u.isLt v.isLt] at e
    have h1 := adjG_iff ⟨n, G, k⟩ u v u.isLt v.isLt
    have h2 := adjG_iff ⟨n, G', k⟩ u v u.isLt v.isLt
    simp only [Fin.eta] at h1 h2
    rw [← h1, ← h2]
    by_cases h3 : adjG ⟨n, G, k⟩ u v = true <;> by_cases h4 : adjG ⟨n, G', k⟩ u v = true <;>
      simp_all
  rw [hG]

/-- A word presents an instance exactly when it is valid. -/
theorem valid_iff_mem {x : List ℕ} : Valid x ↔ x ∈ Instances := by
  constructor
  · intro h; exact ⟨ofValid x, word_ofValid h⟩
  · rintro ⟨I, rfl⟩; exact valid_word I

theorem word_decode {x : List ℕ} (h : Valid x) : word (decode x) = x := by
  have hm := valid_iff_mem.mp h
  unfold decode
  rw [dif_pos hm]
  exact Classical.choose_spec hm

theorem order_decode {x : List ℕ} (h : Valid x) : (decode x).order = order x := by
  have := congrArg order (word_decode h)
  rwa [order_word] at this

theorem threshold_decode {x : List ℕ} (h : Valid x) : (decode x).threshold = kOf x := by
  have := congrArg kOf (word_decode h)
  rwa [kOf_word] at this

/-- The matrix of the decoded graph is the word's matrix. -/
theorem adjG_decode {x : List ℕ} (h : Valid x) (u v : ℕ) :
    Lax496464.WH_F2_MccConstruction.adjG (decode x) u v =
      decide (u < order x ∧ v < order x ∧ entry x u v = 1) := by
  have hw := word_decode h
  have ho := order_decode h
  by_cases hu : u < order x
  · by_cases hv : v < order x
    · have := entry_word (decode x) u v (by omega) (by omega)
      rw [hw] at this
      rw [this]
      by_cases hb : Lax496464.WH_F2_MccConstruction.adjG (decode x) u v = true <;> simp [hb, hu, hv]
    · have : Lax496464.WH_F2_MccConstruction.adjG (decode x) u v = false := by
        simp [Lax496464.WH_F2_MccConstruction.adjG]; intro _ hv'; omega
      simp [this, hv]
  · have : Lax496464.WH_F2_MccConstruction.adjG (decode x) u v = false := by
      simp [Lax496464.WH_F2_MccConstruction.adjG]; intro hu'; omega
    simp [this, hu]

/-- The parameter of the word of an instance is its threshold. -/
theorem threshold_word (I : Instance) : threshold (word I) = I.threshold := by
  have hw : word I = ((List.replicate I.order 1 ++ 0 :: mat I) ++ List.replicate I.threshold 1) ++ [0] := by
    rw [word_eq]; simp
  obtain ⟨r, hr⟩ := exists_zero_head I
  unfold threshold
  rw [hw, List.dropLast_concat, List.reverse_append, List.reverse_replicate]
  have hP : (List.replicate I.order 1 ++ 0 :: mat I).reverse = 0 :: r := by
    rw [← hr]; simp
  rw [hP, takeWhile_run]

theorem reduce_valid {x : List ℕ} (h : Valid x) :
    Lax496464.WH_F2_MccConstruction.reduce x = Lax496464.WH_F2_MccConstruction.word (decode x) := by
  have hm := valid_iff_mem.mp h
  unfold Lax496464.WH_F2_MccConstruction.reduce decode
  rw [dif_pos hm, dif_pos hm]

theorem reduce_invalid {x : List ℕ} (h : ¬ Valid x) : Lax496464.WH_F2_MccConstruction.reduce x = [] := by
  have hm : x ∉ Instances := fun hm => h (valid_iff_mem.mpr hm)
  unfold Lax496464.WH_F2_MccConstruction.reduce
  rw [dif_neg hm]

end Lax496464Proofs.WHierarchy.MccNP.Shape
