import Lax496464Proofs.WHierarchy.MccNP.Shape

/-!
# List facts for the validator

Runs of ones, and `Shape.Valid` in the form the validator checks.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Validate

/-- The run of ones of `y` starting at index `s`. -/
def tw (y : List ℕ) (s : ℕ) : ℕ := ((y.drop s).takeWhile fun v => v == 1).length

theorem takeWhile_facts (l : List ℕ) :
    (l.takeWhile fun v => v == 1).length ≤ l.length ∧
    (∀ j < (l.takeWhile fun v => v == 1).length, l.getD j 0 = 1) ∧
    ((l.takeWhile fun v => v == 1).length < l.length →
      l.getD (l.takeWhile fun v => v == 1).length 0 ≠ 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    by_cases ha : a = 1
    · subst ha
      simp only [List.takeWhile_cons, beq_self_eq_true, if_true, List.length_cons]
      refine ⟨by omega, ?_, ?_⟩
      · intro j hj
        rcases j with _ | j
        · simp
        · simp only [List.getD_cons_succ]; exact h2 j (by omega)
      · intro h
        simp only [List.getD_cons_succ]; exact h3 (by omega)
    · have : (a == 1) = false := by simpa using ha
      simp only [List.takeWhile_cons, this, Bool.false_eq_true, if_false, List.length_nil,
        List.length_cons]
      refine ⟨by omega, by simp, ?_⟩
      intro _
      simpa using ha

theorem getD_drop' (y : List ℕ) (s j : ℕ) : (y.drop s).getD j 0 = y.getD (s + j) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem tw_le (y : List ℕ) (s : ℕ) : s + tw y s ≤ y.length ∨ y.length < s := by
  have := (takeWhile_facts (y.drop s)).1
  simp only [List.length_drop] at this
  unfold tw; omega

theorem tw_le' {y : List ℕ} {s : ℕ} (hs : s ≤ y.length) : s + tw y s ≤ y.length := by
  rcases tw_le y s with h | h
  · exact h
  · omega

theorem tw_one {y : List ℕ} {s j : ℕ} (hj : j < tw y s) : y.getD (s + j) 0 = 1 := by
  have := (takeWhile_facts (y.drop s)).2.1 j hj
  rwa [getD_drop'] at this

theorem tw_stop {y : List ℕ} {s : ℕ} (h : s + tw y s < y.length) :
    y.getD (s + tw y s) 0 ≠ 1 := by
  have h' : tw y s < (y.drop s).length := by simp only [List.length_drop]; omega
  have := (takeWhile_facts (y.drop s)).2.2 h'
  rwa [getD_drop'] at this

open Shape in
theorem order_eq (x : List ℕ) : order x = tw x 0 := by
  simp [order, tw]

/-- The cell condition at flat index `t` of the matrix. -/
def Cell (x : List ℕ) (n t : ℕ) : Prop :=
  x.getD (n + 1 + t) 0 ≤ 1 ∧ x.getD (n + 1 + t) 0 = x.getD (n + 1 + (t % n * n + t / n)) 0 ∧
    (t / n = t % n → x.getD (n + 1 + t) 0 = 0)

theorem divmod_mul {n u v : ℕ} (hn : 0 < n) (hv : v < n) :
    (u * n + v) / n = u ∧ (u * n + v) % n = v := by
  rw [Nat.div_mod_unique hn]
  exact ⟨by rw [Nat.mul_comm]; omega, hv⟩

theorem lt_sq {n u v : ℕ} (hu : u < n) (hv : v < n) : u * n + v < n * n := by
  have : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right n hu
  have h2 : (u + 1) * n = u * n + n := by ring
  omega

open Shape in
/-- `Valid` in the form the machine checks it. -/
theorem valid_iff (x : List ℕ) :
    Valid x ↔ (order x + 1 + order x * order x < x.length ∧ x.getD (order x) 0 = 0 ∧
      (∀ t < order x * order x, Cell x (order x) t) ∧
      order x + 1 + order x * order x + tw x (order x + 1 + order x * order x) + 1 = x.length ∧
      x.getD (order x + 1 + order x * order x + tw x (order x + 1 + order x * order x)) 0 = 0) := by
  have hk : kOf x = tw x (order x + 1 + order x * order x) := rfl
  unfold Valid
  rw [hk]
  unfold entry
  generalize order x = n at *
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, h1, ?_, h2.symm, h3⟩
    intro t ht
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at ht
      · exact h
    have hu : t / n < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at ht; exact ht)
    have hv : t % n < n := Nat.mod_lt _ hn
    have ht' : t / n * n + t % n = t := Nat.div_add_mod' t n
    obtain ⟨e1, e2⟩ := h4 _ hu _ hv
    have i1 : n + 1 + t / n * n + t % n = n + 1 + t := by omega
    have i2 : n + 1 + t % n * n + t / n = n + 1 + (t % n * n + t / n) := by omega
    rw [i1] at e1 e2
    rw [i2] at e2
    refine ⟨e1, e2, fun hd => ?_⟩
    have := h5 _ hu
    have i3 : n + 1 + t / n * n + t / n = n + 1 + t := by omega
    rw [i3] at this
    exact this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h2, h4.symm, h5, ?_, ?_⟩
    · intro u hu v hv
      have hn : 0 < n := by omega
      have ht := lt_sq hu hv
      obtain ⟨d1, d2⟩ := divmod_mul (u := u) hn hv
      obtain ⟨c1, c2, c3⟩ := h3 _ ht
      rw [d1, d2] at c2 c3
      have i1 : n + 1 + u * n + v = n + 1 + (u * n + v) := by omega
      have i2 : n + 1 + v * n + u = n + 1 + (v * n + u) := by omega
      rw [i1, i2]
      exact ⟨c1, c2⟩
    · intro u hu
      have hn : 0 < n := by omega
      have ht := lt_sq hu hu
      obtain ⟨d1, d2⟩ := divmod_mul (u := u) hn hu
      obtain ⟨c1, c2, c3⟩ := h3 _ ht
      rw [d1, d2] at c3
      have i1 : n + 1 + u * n + u = n + 1 + (u * n + u) := by omega
      rw [i1]
      exact c3 rfl

end Lax496464Proofs.WHierarchy.MccNP.Validate
