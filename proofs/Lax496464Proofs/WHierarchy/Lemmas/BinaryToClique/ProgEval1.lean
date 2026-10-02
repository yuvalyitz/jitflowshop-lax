import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgElb

/-!
# Σ₁[2] Model Checking to Clique: the Stack Operations

The stack `l` (top first) is held in the array `st` as its first `zsp` entries, bottom first:
`st.take zsp = l.reverse`. Each operation of a node moves `l` to `evStep c (g, m) l`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval1

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics

/-! ### Stacks in arrays -/

/-- The array `arr` holds the stack `l` (top first) in its first `l.length` entries. -/
def Holds (arr l : List ℕ) : Prop := arr.take l.length = l.reverse ∧ l.length ≤ arr.length

theorem holds_nil (arr : List ℕ) : Holds arr [] := by simp [Holds]

theorem holds_push {arr l : List ℕ} (h : Holds arr l) (hr : l.length < arr.length) (v : ℕ) :
    Holds (arr.set l.length v) (v :: l) := by
  obtain ⟨h1, -⟩ := h
  refine ⟨?_, by simp; omega⟩
  rw [List.length_cons, List.take_add_one, List.take_set_of_le (le_refl _), h1,
    List.getElem?_set_self hr]
  simp

theorem getD_of_holds {arr l : List ℕ} (h : Holds arr l) {i : ℕ} (hi : i < l.length) :
    arr.getD i 0 = l.reverse.getD i 0 := by
  obtain ⟨h1, h2⟩ := h
  rw [← h1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

theorem holds_top {arr : List ℕ} {v : ℕ} {t : List ℕ} (h : Holds arr (v :: t)) :
    arr.getD t.length 0 = v := by
  rw [getD_of_holds h (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem holds_second {arr : List ℕ} {v w : ℕ} {t : List ℕ} (h : Holds arr (v :: w :: t)) :
    arr.getD t.length 0 = w := by
  rw [getD_of_holds h (by simp)]
  simp [List.getD_eq_getElem?_getD]

theorem holds_set_top {arr : List ℕ} {v : ℕ} {t : List ℕ} (h : Holds arr (v :: t)) (u : ℕ) :
    Holds (arr.set t.length u) (u :: t) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, by simp at h2 ⊢; omega⟩
  simp only [List.length_cons] at h1 ⊢
  rw [List.take_set, h1]
  simp [List.set_append_right]

theorem holds_pop2 {arr : List ℕ} {v w : ℕ} {t : List ℕ} (h : Holds arr (v :: w :: t)) (u : ℕ) :
    Holds (arr.set t.length u) (u :: t) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, by simp at h2 ⊢; omega⟩
  simp only [List.length_cons] at h1 h2 ⊢
  have e : arr.take (t.length + 1) = t.reverse ++ [w] := by
    have := congrArg (List.take (t.length + 1)) h1
    rw [List.take_take, Nat.min_eq_left (by omega)] at this
    rw [this]
    rw [show t.length + 1 = t.reverse.length + 1 by simp]
    simp [List.take_append]
  rw [List.take_set, e]
  simp [List.set_append_right]

/-- Values of a stack are bits. -/
def Bits (l : List ℕ) : Prop := ∀ v ∈ l, v ≤ 1

theorem evStep_bits (c : ℕ) (nd : ℕ × ℕ) {l : List ℕ} (h : Bits l) : Bits (evStep c nd l) := by
  have hb := bitv_le_one c nd.2
  unfold Bits at h ⊢
  have hd : ∀ l : List ℕ, (∀ v ∈ l, v ≤ 1) → l.headD 0 ≤ 1 := by
    intro l hl; cases l <;> simp_all
  have ht : ∀ v ∈ l.tail, v ≤ 1 := fun v hv => h v (List.mem_of_mem_tail hv)
  have htt : ∀ v ∈ l.tail.tail, v ≤ 1 := fun v hv => ht v (List.mem_of_mem_tail hv)
  have h1 := hd l h
  have h2 := hd l.tail ht
  unfold evStep
  split_ifs
  all_goals first
    | exact h
    | (intro v hv; rcases List.mem_cons.1 hv with rfl | hv
       · omega
       · first | exact h v hv | exact ht v hv | exact htt v hv)

theorem length_evStep (c : ℕ) (nd : ℕ × ℕ) (l : List ℕ) :
    (evStep c nd l).length ≤ l.length + 1 := by
  unfold evStep; split_ifs <;> simp <;> omega

/-! ### The operations -/

/-- The stack invariant: `zsp` is the height, `st` (of length `S`) holds the stack of bits. -/
def SI (S : ℕ) (l : List ℕ) (σ : Env) : Prop :=
  σ.vars "zsp" = l.length ∧ Holds (σ.arrs "st") l ∧ (σ.arrs "st").length = S ∧ Bits l

theorem bitv_eq (c m : ℕ) : bitv c m = c / 2 ^ m - c / 2 ^ m / 2 * 2 := by
  unfold bitv; omega

theorem bits_cons {v : ℕ} {l : List ℕ} (hv : v ≤ 1) (h : Bits l) : Bits (v :: l) := by
  intro u hu; rcases List.mem_cons.1 hu with rfl | hu
  · exact hv
  · exact h u hu

set_option maxHeartbeats 1000000 in
theorem pushBit_spec {B S : ℕ} (l : List ℕ) :
    Spec B (fun σ => SI S l σ ∧ l.length < S ∧ S < B ∧ 2 < B ∧ σ.vars "zc" < B ∧
        σ.vars "zm" < B ∧ σ.vars "zc" / 2 ^ σ.vars "zm" < B)
      pushBit (fun σ σ' => SI S (bitv (σ.vars "zc") (σ.vars "zm") :: l) σ') 20 := by
  unfold pushBit
  run_vcg
  all_goals (obtain ⟨h1, h2, h3, h4⟩ := ‹SI S l σ›)
  all_goals first
    | omega
    | (simp [h1, h3]; omega)
    | exact lt_of_le_of_lt (Nat.div_le_self _ _) ‹_›
    | exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) ‹_›
    | exact lt_of_le_of_lt (Nat.sub_le _ _) ‹_›
    | (simp only [SI]
       refine ⟨by simp [h1], ?_, by simp [h3], bits_cons (bitv_le_one _ _) h4⟩
       simpa [h1, bitv_eq] using holds_push h2 (by omega) (bitv (σ.vars "zc") (σ.vars "zm")))


theorem holds_pop {arr : List ℕ} {v w : ℕ} {t : List ℕ} (h : Holds arr (v :: w :: t)) :
    Holds arr (w :: t) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, by simp at h2 ⊢; omega⟩
  simp only [List.length_cons] at h1 h2 ⊢
  have := congrArg (List.take (t.length + 1)) h1
  rw [List.take_take, Nat.min_eq_left (by omega)] at this
  rw [this, show t.length + 1 = t.reverse.length + 1 by simp]
  simp [List.take_append]

theorem neg_SI {S v : ℕ} {t : List ℕ} {σ : Env} (h : SI S (v :: t) σ) :
    SI S ((1 - v) :: t)
      (σ.setArr "st" (σ.vars "zsp" - 1) (1 - (σ.arrs "st").getD (σ.vars "zsp" - 1) 0)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have idx : σ.vars "zsp" - 1 = t.length := by rw [h1]; simp
  rw [idx, holds_top h2]
  refine ⟨by simp [h1], by simpa using holds_set_top h2 (1 - v), by simp [h3],
    bits_cons (by omega) fun u hu => h4 u (List.mem_cons_of_mem _ hu)⟩

theorem pop_SI {S v w u : ℕ} {t : List ℕ} {σ : Env} (h : SI S (v :: w :: t) σ) (hu : u ≤ 1) :
    SI S (u :: t) ((σ.setArr "st" (σ.vars "zsp" - 2) u).setVar "zsp"
      ((σ.setArr "st" (σ.vars "zsp" - 2) u).vars "zsp" - 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have idx : σ.vars "zsp" - 2 = t.length := by rw [h1]; simp
  refine ⟨by simp [h1], ?_, by simp [h3],
    bits_cons hu fun u hu => h4 u (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu))⟩
  simp only [arrs_setVar, arrs_setArr, ↓reduceIte]
  rw [idx]
  exact holds_pop2 h2 u

theorem keep_SI {S v w : ℕ} {t : List ℕ} {σ : Env} (h : SI S (v :: w :: t) σ) :
    SI S (w :: t) (σ.setVar "zsp" (σ.vars "zsp" - 1)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by simp [h1], by simpa using holds_pop h2, by simp [h3],
    fun u hu => h4 u (List.mem_cons_of_mem _ hu)⟩

theorem top_val {S v : ℕ} {t : List ℕ} {σ : Env} (h : SI S (v :: t) σ) :
    (σ.arrs "st").getD (σ.vars "zsp" - 1) 0 = v := by
  obtain ⟨h1, h2, -, -⟩ := h
  rw [h1]; simpa using holds_top h2

theorem second_val {S v w : ℕ} {t : List ℕ} {σ : Env} (h : SI S (v :: w :: t) σ) :
    (σ.arrs "st").getD (σ.vars "zsp" - 2) 0 = w := by
  obtain ⟨h1, h2, -, -⟩ := h
  rw [h1]; simpa using holds_second h2

theorem SI.le {S : ℕ} {l : List ℕ} {σ : Env} (h : SI S l σ) : σ.vars "zsp" ≤ S := by
  obtain ⟨h1, h2, h3, -⟩ := h; rw [h1, ← h3]; exact h2.2

theorem SI.head_le {S v : ℕ} {t : List ℕ} {σ : Env} (h : SI S (v :: t) σ) : v ≤ 1 :=
  h.2.2.2 v List.mem_cons_self

theorem SI.second_le {S v w : ℕ} {t : List ℕ} {σ : Env} (h : SI S (v :: w :: t) σ) : w ≤ 1 :=
  h.2.2.2 w (List.mem_cons_of_mem _ List.mem_cons_self)

set_option maxHeartbeats 1000000 in
theorem negC_spec {B S : ℕ} (l : List ℕ) :
    Spec B (fun σ => SI S l σ ∧ S < B ∧ 2 < B) negC
      (fun _ σ' => SI S (if l.length = 0 then l else (1 - l.headD 0) :: l.tail) σ') 20 := by
  unfold negC
  rcases l with _ | ⟨v, t⟩
  · intro σ ⟨h, hS, h2⟩
    have hle := h.le
    have h3 : (σ.arrs "st").length = S := h.2.2.1
    have h0 : σ.vars "zsp" = 0 := h.1
    run_vcg
    all_goals first
      | exact h
      | (simp at *; omega)
  · intro σ ⟨h, hS, h2⟩
    have hle := h.le
    have h3 : (σ.arrs "st").length = S := h.2.2.1
    have h0 : σ.vars "zsp" = t.length + 1 := h.1
    have htop := top_val h
    have hv := h.head_le
    run_vcg
    all_goals first
      | (simp at *; omega)
      | (rw [htop]; omega)
      | (rw [if_neg (by simp)]; exact neg_SI h)

set_option maxHeartbeats 1000000 in
theorem andC_spec {B S : ℕ} (l : List ℕ) :
    Spec B (fun σ => SI S l σ ∧ S < B ∧ 2 < B) andC
      (fun _ σ' => SI S (if l.length < 2 then l
        else (if l.headD 0 = 0 then 0 else l.tail.headD 0) :: l.tail.tail) σ') 30 := by
  unfold andC
  rcases l with _ | ⟨v, _ | ⟨w, t⟩⟩
  · intro σ ⟨h, hS, h2⟩
    have hle := h.le
    have h3 : (σ.arrs "st").length = S := h.2.2.1
    have h0 : σ.vars "zsp" = 0 := h.1
    run_vcg
    all_goals first
      | exact h
      | (simp at *; omega)
  · intro σ ⟨h, hS, h2⟩
    have hle := h.le
    have h3 : (σ.arrs "st").length = S := h.2.2.1
    have h0 : σ.vars "zsp" = 1 := h.1
    run_vcg
    all_goals first
      | exact h
      | (simp at *; omega)
  · intro σ ⟨h, hS, h2⟩
    have hle := h.le
    have h3 : (σ.arrs "st").length = S := h.2.2.1
    have h0 : σ.vars "zsp" = t.length + 2 := h.1
    have htop := top_val h
    have hsec := second_val h
    have hv := h.head_le
    have hw := h.second_le
    run_vcg
    all_goals first
      | (simp at *; omega)
      | ((try rw [if_neg (show ¬ ((v :: w :: t).length < 2) by simp)])
         (try simp only [List.headD_cons, List.tail_cons])
         split_ifs with hc <;> first
           | (simp only [hc, ↓reduceIte]; exact pop_SI h (by omega))
           | (simp only [hc, ↓reduceIte]; exact keep_SI h)
           | (exfalso; simp only [htop, hsec] at *; omega))

set_option maxHeartbeats 1000000 in
theorem orC_spec {B S : ℕ} (l : List ℕ) :
    Spec B (fun σ => SI S l σ ∧ S < B ∧ 2 < B) orC
      (fun _ σ' => SI S (if l.length < 2 then l
        else (if l.tail.headD 0 + l.headD 0 = 0 then 0 else 1) :: l.tail.tail) σ') 40 := by
  unfold orC
  rcases l with _ | ⟨v, _ | ⟨w, t⟩⟩
  · intro σ ⟨h, hS, h2⟩
    have hle := h.le
    have h3 : (σ.arrs "st").length = S := h.2.2.1
    have h0 : σ.vars "zsp" = 0 := h.1
    run_vcg
    all_goals first
      | exact h
      | (simp at *; omega)
  · intro σ ⟨h, hS, h2⟩
    have hle := h.le
    have h3 : (σ.arrs "st").length = S := h.2.2.1
    have h0 : σ.vars "zsp" = 1 := h.1
    run_vcg
    all_goals first
      | exact h
      | (simp at *; omega)
  · intro σ ⟨h, hS, h2⟩
    have hle := h.le
    have h3 : (σ.arrs "st").length = S := h.2.2.1
    have h0 : σ.vars "zsp" = t.length + 2 := h.1
    have htop := top_val h
    have hsec := second_val h
    have hv := h.head_le
    have hw := h.second_le
    run_vcg
    all_goals first
      | (simp at *; omega)
      | ((try rw [if_neg (show ¬ ((v :: w :: t).length < 2) by simp)])
         (try simp only [List.headD_cons, List.tail_cons])
         split_ifs with hc <;> first
           | (simp only [hc, ↓reduceIte]; exact pop_SI h (by omega))
           | (exfalso; simp only [htop, hsec] at *; omega))

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgEval1
