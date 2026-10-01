import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs

/-! # Basic facts: numbers in base `M`, digits, decoding, occurrences

Numbers in base `M` and their digits (`num`, `digit_num`, `num_inj`), the decoding of the input word
into clauses and weight (`encode_unique`), the offsets of the clauses, and the first occurrences of
the variables (`fst`, `rep`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic

open Lax496464.WH_C3_WeightedSat
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs
open Lax496464Proofs.WHierarchy.HittingSet.Compress (idxOf_eq_of_least getD_idxOf getD_mem)

/-! ### Numbers in base `M` -/

@[simp] theorem num_nil (M : ℕ) : num M [] = 0 := rfl

@[simp] theorem num_cons (M a : ℕ) (l : List ℕ) : num M (a :: l) = a + M * num M l := rfl

theorem num_append (M : ℕ) : ∀ l1 l2 : List ℕ,
    num M (l1 ++ l2) = num M l1 + M ^ l1.length * num M l2
  | [], l2 => by simp
  | a :: l1, l2 => by
    simp only [List.cons_append, num_cons, num_append M l1 l2, List.length_cons, pow_succ]
    ring

theorem num_lt {M : ℕ} (hM : 0 < M) : ∀ {l : List ℕ}, (∀ a ∈ l, a < M) → num M l < M ^ l.length
  | [], _ => by simp
  | a :: l, h => by
    have ha := h a (by simp)
    have ih := num_lt hM (l := l) fun b hb => h b (by simp [hb])
    simp only [num_cons, List.length_cons, pow_succ]
    have : M * num M l + M ≤ M * M ^ l.length := by
      have := Nat.mul_le_mul_left M (show num M l + 1 ≤ M ^ l.length by omega)
      linarith
    nlinarith

theorem num_cons_mod {M a : ℕ} (l : List ℕ) (ha : a < M) : num M (a :: l) % M = a := by
  simp only [num_cons]
  rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt ha

theorem num_cons_div {M a : ℕ} (l : List ℕ) (ha : a < M) : num M (a :: l) / M = num M l := by
  simp only [num_cons]
  have hM : 0 < M := by omega
  rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt ha, zero_add]

/-- Digit `p` of a number is entry `p` of its list of digits. -/
theorem digit_num {M : ℕ} : ∀ {l : List ℕ}, (∀ a ∈ l, a < M) → ∀ p,
    num M l / M ^ p % M = l.getD p 0
  | [], _, p => by simp
  | a :: l, h, p => by
    have ha := h a (by simp)
    rcases p with _ | p
    · simp only [pow_zero, Nat.div_one, List.getD_cons_zero]; exact num_cons_mod l ha
    · rw [pow_succ', ← Nat.div_div_eq_div_mul, num_cons_div l ha, List.getD_cons_succ]
      exact digit_num (fun b hb => h b (by simp [hb])) p

/-- The digits of a number are its list of digits. -/
theorem digitsOf_num {M : ℕ} {l : List ℕ} (h : ∀ a ∈ l, a < M) :
    digitsOf M l.length (num M l) = l := by
  refine List.ext_getElem (by simp [digitsOf]) fun p h1 h2 => ?_
  simp only [digitsOf, List.getElem_map, List.getElem_range]
  rw [digit_num h p, List.getD_eq_getElem _ _ h2]

theorem num_inj {M : ℕ} {l l' : List ℕ} (h : ∀ a ∈ l, a < M) (h' : ∀ a ∈ l', a < M)
    (hl : l.length = l'.length) (he : num M l = num M l') : l = l' := by
  rw [← digitsOf_num h, ← digitsOf_num h', he, hl]

theorem length_digitsOf (M a e : ℕ) : (digitsOf M a e).length = a := by simp [digitsOf]

theorem tag_div {M g : ℕ} (hg : g < M) (l : List ℕ) : (g + M * num M l) / M = num M l := by
  have hM : 0 < M := by omega
  rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hg, zero_add]

/-! ### Choosing digits -/

/-- **Every digit function below `n` is the digit function of a number below `n ^ r`.** -/
theorem exists_digits (n : ℕ) : ∀ (r : ℕ) (δ : ℕ → ℕ), (∀ p < r, δ p < n) →
    ∃ t < n ^ r, ∀ p < r, t / n ^ p % n = δ p
  | 0, _, _ => ⟨0, by simp, fun p hp => absurd hp (Nat.not_lt_zero _)⟩
  | r + 1, δ, h => by
    obtain ⟨t', ht', hd⟩ := exists_digits n r (fun p => δ (p + 1)) fun p hp => h (p + 1) (by omega)
    have h0 := h 0 (by omega)
    have hn : 0 < n := by omega
    refine ⟨δ 0 + n * t', ?_, fun p hp => ?_⟩
    · have : n * t' + n ≤ n * n ^ r := by
        have := Nat.mul_le_mul_left n (show t' + 1 ≤ n ^ r by omega); linarith
      rw [pow_succ]; nlinarith
    · rcases p with _ | p
      · simp only [pow_zero, Nat.div_one]
        rw [Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt h0
      · rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hn,
          Nat.div_eq_of_lt h0, zero_add]
        exact hd p (by omega)

/-! ### Decoding -/

theorem parseCl_append : ∀ (cl : List (List ℕ)) (r : List ℕ),
    parseCl cl.length ((cl.flatMap fun c => c.length :: c) ++ r) = cl
  | [], _ => rfl
  | c :: cl, r => by
    simp only [List.length_cons, List.flatMap_cons, List.cons_append, List.append_assoc, parseCl,
      List.drop_one, List.tail_cons, List.getD_cons_zero]
    rw [List.take_left' rfl, List.drop_left' rfl, parseCl_append cl r]

theorem clOf_wordOf' (cl : List (List ℕ)) (k : ℕ) : clOf (wordOf' cl k) = cl := by
  simp only [clOf, wordOf', List.drop_one]
  exact parseCl_append cl [k]

theorem kOf_wordOf' (cl : List (List ℕ)) (k : ℕ) : kOf (wordOf' cl k) = k := by
  have h : ∀ l : List ℕ, (l ++ [k]).getLast? = some k := fun l => by simp
  exact (congrArg (fun o => Option.getD o 0) (h _)).trans rfl

/-- The clauses as lists of codes. -/
def codesOf (α : Lax429075.CNF.Formula) : List (List ℕ) := α.map fun C => C.map litCode

theorem encode_eq (α : Lax429075.CNF.Formula) (k : ℕ) :
    encode α ++ [k] = wordOf' (codesOf α) k := by
  simp only [encode, wordOf', codesOf, List.length_map, List.flatMap_map, List.cons_append]

theorem litCode_inj {l l' : Lax429075.CNF.Literal} (h : litCode l = litCode l') : l = l' := by
  obtain ⟨i, b⟩ := l
  obtain ⟨i', b'⟩ := l'
  simp only [litCode] at h
  cases b <;> cases b' <;> simp at h <;> first | (subst h; rfl) | omega

theorem codesOf_inj {α α' : Lax429075.CNF.Formula} (h : codesOf α = codesOf α') : α = α' := by
  unfold codesOf at h
  refine List.map_injective_iff.mpr (fun C C' hC => ?_) h
  exact List.map_injective_iff.mpr (fun _ _ => litCode_inj) hC

/-- **The input word determines the formula and the weight.** -/
theorem encode_unique {α α' : Lax429075.CNF.Formula} {k k' : ℕ}
    (h : encode α ++ [k] = encode α' ++ [k']) : α = α' ∧ k = k' := by
  rw [encode_eq, encode_eq] at h
  have h1 := clOf_wordOf' (codesOf α) k
  have h2 := kOf_wordOf' (codesOf α) k
  rw [h] at h1 h2
  rw [clOf_wordOf'] at h1
  rw [kOf_wordOf'] at h2
  exact ⟨codesOf_inj h1.symm, h2.symm⟩

/-! ### Occurrences -/

section Occ

variable (cl : List (List ℕ))

theorem off_zero : off cl 0 = 0 := by simp [off]

theorem off_succ {c : ℕ} (hc : c < cl.length) : off cl (c + 1) = off cl c + len cl c := by
  simp only [off, len, List.take_add_one, List.map_append, List.sum_append]
  rw [List.getElem?_eq_getElem hc, List.getD_eq_getElem _ _ hc]
  simp

theorem off_len_le {c : ℕ} (hc : c < cl.length) : off cl c + len cl c ≤ nL cl := by
  rw [← off_succ cl hc]
  simp only [off, nL, List.length_flatten]
  exact List.Sublist.sum_le_sum ((List.take_sublist _ _).map _) (fun _ _ => Nat.zero_le _)

theorem off_cons_succ (C : List ℕ) (c : ℕ) : off (C :: cl) (c + 1) = C.length + off cl c := by
  simp [off, List.take_succ_cons]

theorem len_cons_succ (C : List ℕ) (c : ℕ) : len (C :: cl) (c + 1) = len cl c := by
  simp [len]

theorem code_cons_add (C : List ℕ) (j : ℕ) : code (C :: cl) (C.length + j) = code cl j := by
  unfold code
  rw [List.flatten_cons, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

theorem code_cons_lt (C : List ℕ) {j : ℕ} (hj : j < C.length) :
    code (C :: cl) j = C.getD j 0 := by
  unfold code
  rw [List.flatten_cons, List.getD_append _ _ _ _ hj]

/-- The code of literal `p` of clause `c`. -/
theorem code_off {c p : ℕ} (hc : c < cl.length) (hp : p < len cl c) :
    code cl (off cl c + p) = (cl.getD c []).getD p 0 := by
  induction cl generalizing c with
  | nil => simp at hc
  | cons C cl ih =>
    rcases c with _ | c
    · simp only [off_zero, zero_add, List.getD_cons_zero]
      exact code_cons_lt cl C (by simpa [len] using hp)
    · rw [off_cons_succ, Nat.add_assoc, code_cons_add, List.getD_cons_succ]
      exact ih (by simp at hc; omega) (by rw [len_cons_succ] at hp; exact hp)

theorem off_lt {c p : ℕ} (hc : c < cl.length) (hp : p < len cl c) : off cl c + p < nL cl := by
  have := off_len_le cl hc; omega

theorem len_le_of_dcnf {d : ℕ} (h : ∀ C ∈ cl, C.length ≤ d) (c : ℕ) : len cl c ≤ d := by
  unfold len
  by_cases hc : c < cl.length
  · rw [List.getD_eq_getElem _ _ hc]; exact h _ (List.getElem_mem hc)
  · rw [List.getD_eq_default _ _ (by omega)]; simp

/-- Every occurrence lies in some clause. -/
theorem exists_clause_of_lt {j : ℕ} (hj : j < nL cl) :
    ∃ c < cl.length, ∃ p < len cl c, j = off cl c + p := by
  induction cl generalizing j with
  | nil => simp [nL] at hj
  | cons C cl ih =>
    by_cases hj' : j < C.length
    · exact ⟨0, by simp, j, by simpa [len] using hj', by simp [off]⟩
    · have : j - C.length < nL cl := by simp [nL] at hj ⊢; omega
      obtain ⟨c, hc, p, hp, he⟩ := ih this
      refine ⟨c + 1, by simp; omega, p, by rw [len_cons_succ]; exact hp, ?_⟩
      rw [off_cons_succ]; omega

end Occ

/-! ### First occurrences -/

section Fst

variable (cl : List (List ℕ))

theorem length_varList : (varList cl).length = nL cl := by
  unfold varList nL; exact List.length_map _

theorem varList_getD {j : ℕ} (hj : j < nL cl) : (varList cl).getD j 0 = code cl j / 2 := by
  have hj' : j < cl.flatten.length := hj
  unfold varList code
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj'), List.getElem_map,
    List.getD_eq_getElem _ _ hj']

theorem mem_varList {j : ℕ} (hj : j < nL cl) : code cl j / 2 ∈ varList cl := by
  rw [← varList_getD cl hj]; exact getD_mem (by rw [length_varList]; exact hj)

theorem fst_lt {j : ℕ} (hj : j < nL cl) : fst cl j < nL cl := by
  have := List.idxOf_lt_length_of_mem (mem_varList cl hj)
  rwa [length_varList] at this

theorem code_fst {j : ℕ} (hj : j < nL cl) : code cl (fst cl j) / 2 = code cl j / 2 := by
  rw [← varList_getD cl (fst_lt cl hj)]
  exact getD_idxOf (mem_varList cl hj)

theorem fst_fst {j : ℕ} (hj : j < nL cl) : fst cl (fst cl j) = fst cl j := by
  show (varList cl).idxOf (code cl (fst cl j) / 2) = fst cl j
  rw [code_fst cl hj]; rfl

theorem fst_eq_iff {j j' : ℕ} (hj : j < nL cl) (hj' : j' < nL cl) :
    fst cl j = fst cl j' ↔ code cl j / 2 = code cl j' / 2 := by
  constructor
  · intro h; rw [← code_fst cl hj, ← code_fst cl hj', h]
  · intro h; unfold fst; rw [h]

/-- The representative of a variable: its first occurrence. -/
def rep (v : ℕ) : ℕ := (varList cl).idxOf v

theorem fst_eq_rep (j : ℕ) : fst cl j = rep cl (code cl j / 2) := rfl

theorem rep_inj {v v' : ℕ} (hv : v ∈ varList cl) (h : rep cl v = rep cl v') : v = v' := by
  have hv' : v' ∈ varList cl := by
    by_contra hn
    have h1 := List.idxOf_lt_length_of_mem hv
    unfold rep at h
    rw [h, List.idxOf_eq_length hn] at h1
    omega
  rw [← getD_idxOf hv, ← getD_idxOf hv']; unfold rep at h; rw [h]

end Fst

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
