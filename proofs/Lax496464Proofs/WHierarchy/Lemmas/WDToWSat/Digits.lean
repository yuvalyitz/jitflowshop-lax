import Mathlib.Tactic

/-! # Base-`n` digits

`digits n r z` is the list of the `r` lowest base-`n` digits of `z`, lowest first, and `codeOf n`
reads such a list back (Horner). On tuples of length `r` with entries below `n` the two are inverse
bijections with `[0, n^r)`. The tuples of positions of a structure are enumerated through them, and
the propositional variables are numbered by them. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits

/-- The `r` lowest base-`n` digits of `z`, lowest first. -/
def digits (n : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | r + 1, z => (z % n) :: digits n r (z / n)

/-- The number with the given base-`n` digits, lowest first. -/
def codeOf (n : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + n * codeOf n ds

@[simp] theorem length_digits (n r z : ℕ) : (digits n r z).length = r := by
  induction r generalizing z with
  | zero => rfl
  | succ r ih => simp [digits, ih]

theorem digits_lt {n : ℕ} (hn : 0 < n) : ∀ (r z : ℕ), ∀ d ∈ digits n r z, d < n
  | 0, _, d, hd => by simp [digits] at hd
  | r + 1, z, d, hd => by
    simp only [digits, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact Nat.mod_lt _ hn
    · exact digits_lt hn r (z / n) d hd

theorem codeOf_digits (n : ℕ) : ∀ (r z : ℕ), z < n ^ r → codeOf n (digits n r z) = z
  | 0, z, h => by simp at h; subst h; rfl
  | r + 1, z, h => by
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp at h
      · exact hn
    have h' : z / n < n ^ r := by
      rw [Nat.div_lt_iff_lt_mul hn]; rw [pow_succ] at h; exact h
    simp only [digits, codeOf, codeOf_digits n r (z / n) h']
    exact Nat.mod_add_div z n

theorem codeOf_lt {n : ℕ} : ∀ ds : List ℕ, (∀ d ∈ ds, d < n) → codeOf n ds < n ^ ds.length
  | [], _ => by simp [codeOf]
  | d :: ds, h => by
    have h1 := codeOf_lt ds fun e he => h e (by simp [he])
    have h2 := h d (by simp)
    simp only [codeOf, List.length_cons, pow_succ]
    have : n * codeOf n ds + n ≤ n * n ^ ds.length := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h1
    nlinarith

theorem digits_codeOf {n : ℕ} : ∀ ds : List ℕ, (∀ d ∈ ds, d < n) →
    digits n ds.length (codeOf n ds) = ds
  | [], _ => rfl
  | d :: ds, h => by
    have h2 := h d (by simp)
    have hn : 0 < n := by omega
    simp only [List.length_cons, digits, codeOf]
    have e1 : (d + n * codeOf n ds) % n = d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
    have e2 : (d + n * codeOf n ds) / n = codeOf n ds := by
      rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt h2, zero_add]
    rw [e1, e2, digits_codeOf ds fun e he => h e (by simp [he])]

/-- `codeOf` is injective on tuples of one length with entries below `n`. -/
theorem codeOf_inj {n : ℕ} {ds es : List ℕ} (hd : ∀ d ∈ ds, d < n) (he : ∀ e ∈ es, e < n)
    (hl : ds.length = es.length) (h : codeOf n ds = codeOf n es) : ds = es := by
  rw [← digits_codeOf ds hd, ← digits_codeOf es he, hl, h]

/-- `digits` is injective below `n ^ r`. -/
theorem digits_inj {n r z z' : ℕ} (hz : z < n ^ r) (hz' : z' < n ^ r)
    (h : digits n r z = digits n r z') : z = z' := by
  rw [← codeOf_digits n r z hz, ← codeOf_digits n r z' hz', h]

/-- The truncated form of `z % n` a program computes. -/
theorem mod_eq_sub (w n : ℕ) : w - w / n * n = w % n := by
  rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
