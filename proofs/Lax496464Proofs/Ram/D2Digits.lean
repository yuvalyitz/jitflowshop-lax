import Mathlib.Tactic
import Mathlib.Data.Finset.Sort

/-!
# Theorem 2, Pure Layer 1: Numbers as Digit Strings

A set of thresholds `X ⊆ {0,…,n-1}` with `|X| ≤ m` is written as its elements in increasing order,
padded on the right with the digit `n` to length `m`; read in base `b = n+1` (most significant digit
first) that string is a number `< b^m`.  This file is only the arithmetic of such numbers: `enc`,
the digit extraction the machine performs (`c / b^(m-1-i) % b`), the padding identity
`enc (replicate k n) = b^k - 1`, and the numbers that are codes of sets (`IsCode`).
-/

namespace Lax496464Proofs.Ram.D2Digits

/-- The value, most significant digit first, of a digit string in base `b`. -/
def enc (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: L => d * b ^ L.length + enc b L

@[simp] theorem enc_nil (b : ℕ) : enc b [] = 0 := by simp only [enc]
@[simp] theorem enc_cons (b d : ℕ) (L : List ℕ) : enc b (d :: L) = d * b ^ L.length + enc b L := rfl

theorem enc_append (b : ℕ) (A C : List ℕ) :
    enc b (A ++ C) = enc b A * b ^ C.length + enc b C := by
  induction A with
  | nil => simp
  | cons d A ih =>
    simp only [List.cons_append, enc_cons, List.length_append, ih, pow_add]
    ring

theorem enc_lt {b : ℕ} {L : List ℕ} (h : ∀ x ∈ L, x < b) : enc b L < b ^ L.length := by
  induction L with
  | nil => simp
  | cons d L ih =>
    have hd : d < b := h d (by simp)
    have hL := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp only [enc_cons, List.length_cons, pow_succ]
    nlinarith

theorem enc_replicate_succ {b : ℕ} (hb : 1 ≤ b) (k : ℕ) :
    enc b (List.replicate k (b - 1)) + 1 = b ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [List.replicate_succ, enc_cons, List.length_replicate, Nat.add_sub_cancel] at ih ⊢
    rw [pow_succ]
    nlinarith

theorem div_mod_pow (b d e k : ℕ) (hb : 0 < b) (he : e < b ^ k) :
    (d * b ^ k + e) / b ^ k = d ∧ (d * b ^ k + e) % b ^ k = e := by
  have hp : 0 < b ^ k := pow_pos hb k
  have h1 : d * b ^ k + e = e + b ^ k * d := by ring
  refine ⟨?_, ?_⟩
  · rw [h1, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt he]; simp
  · rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he]

/-- The `i`-th digit (from the top) of the `m`-digit number `c`, the extraction the machine does. -/
def dig (b m c i : ℕ) : ℕ := c / b ^ (m - 1 - i) % b

theorem dig_enc {b : ℕ} (hb : 0 < b) {L : List ℕ} (h : ∀ x ∈ L, x < b) :
    ∀ i, i < L.length → L.getD i 0 = dig b L.length (enc b L) i := by
  induction L with
  | nil => intro i hi; simp at hi
  | cons d L ih =>
    intro i hi
    have hd : d < b := h d (by simp)
    have hL : ∀ x ∈ L, x < b := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hlt := enc_lt hL
    cases i with
    | zero =>
      simp only [dig, List.length_cons, enc_cons, Nat.add_sub_cancel, Nat.sub_zero,
        List.getD_cons_zero]
      rw [(div_mod_pow b d _ _ hb hlt).1, Nat.mod_eq_of_lt hd]
    | succ i =>
      have hi' : i < L.length := by simpa using hi
      simp only [List.getD_cons_succ, List.length_cons, enc_cons]
      rw [ih hL i hi']
      unfold dig
      have ht : L.length - 1 - i < L.length := by omega
      have hk : L.length + 1 - 1 - (i + 1) = L.length - 1 - i := by omega
      rw [hk]
      set t := L.length - 1 - i with ht'
      have hkt : L.length = t + (L.length - t) := by omega
      have hpos : 0 < b ^ t := pow_pos hb t
      have hsplit : d * b ^ L.length + enc b L =
          enc b L + b ^ t * (d * b ^ (L.length - t)) := by
        conv_lhs => rw [hkt, pow_add]
        ring
      rw [hsplit, Nat.add_mul_div_left _ _ hpos]
      have hlt1 : 1 ≤ L.length - t := by omega
      obtain ⟨u, hu⟩ : ∃ u, L.length - t = u + 1 := ⟨L.length - t - 1, by omega⟩
      rw [hu, pow_succ, show d * (b ^ u * b) = (d * b ^ u) * b by ring]
      rw [Nat.add_mul_mod_self_right]

/-! ## Codes of sets -/

/-- The digit string of a strictly increasing list of thresholds: padded on the right with `n`. -/
def lstOf (n m : ℕ) (Zs : List ℕ) : List ℕ := Zs ++ List.replicate (m - Zs.length) n

/-- The number written by `lstOf`, in base `n + 1`. -/
def codeL (n m : ℕ) (Zs : List ℕ) : ℕ := enc (n + 1) (lstOf n m Zs)

/-- `Zs` is a strictly increasing list of thresholds below `n`, at most `m` of them. -/
structure SL (n m : ℕ) (Zs : List ℕ) : Prop where
  sorted : Zs.SortedLT
  lt : ∀ z ∈ Zs, z < n
  len : Zs.length ≤ m

theorem SL.lstOf_length {n m : ℕ} {Zs : List ℕ} (h : SL n m Zs) : (lstOf n m Zs).length = m := by
  have := h.len
  simp [lstOf]; omega

theorem SL.lstOf_lt {n m : ℕ} {Zs : List ℕ} (h : SL n m Zs) : ∀ x ∈ lstOf n m Zs, x < n + 1 := by
  intro x hx
  simp only [lstOf, List.mem_append, List.mem_replicate] at hx
  rcases hx with hx | ⟨-, rfl⟩
  · have := h.lt x hx; omega
  · omega

theorem SL.codeL_lt {n m : ℕ} {Zs : List ℕ} (h : SL n m Zs) : codeL n m Zs < (n + 1) ^ m := by
  have := enc_lt h.lstOf_lt
  rwa [h.lstOf_length] at this

/-- The code of the empty set: all padding. -/
theorem codeL_nil (n m : ℕ) : codeL n m [] = (n + 1) ^ m - 1 := by
  have := enc_replicate_succ (b := n + 1) (by omega) m
  simp only [Nat.add_sub_cancel] at this
  simp only [codeL, lstOf, List.length_nil, Nat.sub_zero, List.nil_append]
  omega

/-- `c` is the code of some set. -/
def IsCode (n m c : ℕ) : Prop := ∃ Zs, SL n m Zs ∧ codeL n m Zs = c

/-- Two sets with the same code are equal: the code determines the digit string. -/
theorem enc_inj {b : ℕ} (hb : 0 < b) :
    ∀ {L L' : List ℕ}, L.length = L'.length → (∀ x ∈ L, x < b) → (∀ x ∈ L', x < b) →
      enc b L = enc b L' → L = L' := by
  intro L
  induction L with
  | nil => intro L' hl _ _ _; cases L' with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons d L ih =>
    intro L' hl h1 h2 he
    cases L' with
    | nil => simp at hl
    | cons d' L' =>
      have hl' : L.length = L'.length := by simpa using hl
      have hL : ∀ x ∈ L, x < b := fun x hx => h1 x (List.mem_cons_of_mem _ hx)
      have hL' : ∀ x ∈ L', x < b := fun x hx => h2 x (List.mem_cons_of_mem _ hx)
      simp only [enc_cons, ← hl'] at he
      have a1 := div_mod_pow b d _ _ hb (enc_lt hL)
      have a2 := div_mod_pow b d' _ _ hb (hl' ▸ enc_lt hL' : enc b L' < b ^ L.length)
      have hdd : d = d' := by
        have this : (d * b ^ L.length + enc b L) / b ^ L.length =
            (d' * b ^ L.length + enc b L') / b ^ L.length := by rw [he]
        rw [a1.1] at this
        have h3 : (d' * b ^ L.length + enc b L') / b ^ L.length = d' := by
          have := div_mod_pow b d' (enc b L') L.length hb (by rw [hl']; exact enc_lt hL')
          exact this.1
        rw [h3] at this; exact this
      subst hdd
      have hee : enc b L = enc b L' := by omega
      rw [ih hl' hL hL' hee]

theorem SL.codeL_inj {n m : ℕ} {Zs Zs' : List ℕ} (h : SL n m Zs) (h' : SL n m Zs')
    (he : codeL n m Zs = codeL n m Zs') : Zs = Zs' := by
  have := enc_inj (b := n + 1) (by omega) (by rw [h.lstOf_length, h'.lstOf_length])
    h.lstOf_lt h'.lstOf_lt he
  -- the strings are `Zs ++ replicate p n` and `Zs' ++ replicate p' n`, all of `Zs` below `n`
  simp only [lstOf] at this
  have hcut : ∀ (A : List ℕ) (p : ℕ), (∀ z ∈ A, z < n) →
      (A ++ List.replicate p n).takeWhile (· < n) = A := by
    intro A p hA
    induction A with
    | nil =>
      cases p with
      | zero => simp
      | succ p => simp [List.replicate_succ]
    | cons a A ih =>
      simp only [List.cons_append, List.takeWhile_cons, hA a (by simp), decide_true, if_true]
      rw [ih (fun z hz => hA z (List.mem_cons_of_mem _ hz))]
  have h1 := hcut Zs (m - Zs.length) h.lt
  have h2 := hcut Zs' (m - Zs'.length) h'.lt
  rw [this] at h1
  rw [h1] at h2
  exact h2

end Lax496464Proofs.Ram.D2Digits
