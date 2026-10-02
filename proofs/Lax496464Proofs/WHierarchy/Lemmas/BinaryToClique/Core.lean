import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# Σ₁[2] Model Checking to Clique: the Graph, Abstractly

The graph of the reduction, described by a handful of functions on numbers (`Params`): the number
`k = 2q` of rows, the number `ne` of candidate values and the value `E e` of candidate `e`, the
variable `vs r` of row `r`, the flag `ok c` of the truth valuation `c < 2^q` of the `q` atoms, and
the truth `atm m v w` of atom `m` when its two variables take the values `v` and `w`.

A vertex `u` is a triple: its valuation `c`, its candidate `e`, its row `r`
(`u = (c · ne + e) · k + r`). Two vertices are adjacent when they have the same valuation `c`, the
valuation satisfies the formula (`ok c = 1`), their rows differ, rows of the same variable carry the
same value, and when the two rows are the two rows `2m, 2m + 1` of atom `m`, the atom has the truth
value `c` gives it.

**`clique_iff`**: under the hypotheses that relate the functions to a formula — abstracted here to
a predicate `Φ` on assignments, atom predicates `Aτ m` and a set `F` of variables — the graph has a
clique of `k` vertices exactly when some assignment of candidate values to the variables of `F`
satisfies `Φ`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core

/-- Bit `m` of `c`. -/
def bitv (c m : ℕ) : ℕ := c / 2 ^ m % 2

theorem bitv_le_one (c m : ℕ) : bitv c m ≤ 1 := by
  unfold bitv; have := Nat.mod_lt (c / 2 ^ m) (show 0 < 2 by norm_num); omega

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The data of the graph. -/
structure Params where
  /-- The number of rows, twice the number of atoms. -/
  k : ℕ
  /-- The number of candidate values. -/
  ne : ℕ
  /-- The value of each candidate. -/
  E : ℕ → ℕ
  /-- The variable of each row. -/
  vs : ℕ → ℕ
  /-- `ok c = 1` when the valuation `c` of the atoms satisfies the formula. -/
  ok : ℕ → ℕ
  /-- The truth (`0` or `1`) of atom `m` at the values `v, w` of its two variables. -/
  atm : ℕ → ℕ → ℕ → ℕ

variable (P : Params)

/-- The row of a vertex. -/
def rowOf (u : ℕ) : ℕ := u % P.k

/-- The candidate of a vertex. -/
def eltOf (u : ℕ) : ℕ := u / P.k % P.ne

/-- The valuation of a vertex. -/
def compOf (u : ℕ) : ℕ := u / P.k / P.ne

/-- The value of a vertex. -/
def valOf (u : ℕ) : ℕ := P.E (eltOf P u)

/-- The atom test between rows `r1 ≠ r2` of the same atom `r1 / 2`: the value of the lower row
first. -/
def atomOK (c r1 r2 v1 v2 : ℕ) : Bool :=
  decide (P.atm (r1 / 2) (if r1 < r2 then v1 else v2) (if r1 < r2 then v2 else v1) =
    bitv c (r1 / 2))

/-- **The adjacency.** -/
def adjP (u w : ℕ) : Bool :=
  if compOf P u = compOf P w then
    if P.ok (compOf P u) = 1 then
      if rowOf P u = rowOf P w then false
      else if P.vs (rowOf P u) = P.vs (rowOf P w) ∧ valOf P u ≠ valOf P w then false
      else if rowOf P u / 2 = rowOf P w / 2 then
        atomOK P (compOf P u) (rowOf P u) (rowOf P w) (valOf P u) (valOf P w)
      else true
    else false
  else false

theorem adjP_true_iff (u w : ℕ) :
    adjP P u w = true ↔ compOf P u = compOf P w ∧ P.ok (compOf P u) = 1 ∧
      rowOf P u ≠ rowOf P w ∧ ¬ (P.vs (rowOf P u) = P.vs (rowOf P w) ∧ valOf P u ≠ valOf P w) ∧
      (rowOf P u / 2 = rowOf P w / 2 →
        atomOK P (compOf P u) (rowOf P u) (rowOf P w) (valOf P u) (valOf P w) = true) := by
  unfold adjP
  split_ifs <;> simp_all

theorem adjP_irrefl (u : ℕ) : adjP P u u = false := by
  unfold adjP; simp

theorem atomOK_symm {c c' r1 r2 v1 v2 : ℕ} (hc : c = c') (hr : r1 ≠ r2) (hm : r1 / 2 = r2 / 2) :
    atomOK P c r1 r2 v1 v2 = atomOK P c' r2 r1 v2 v1 := by
  subst hc
  unfold atomOK
  rw [hm]
  rcases Nat.lt_or_gt_of_ne hr with h | h
  · rw [if_pos h, if_pos h, if_neg (by omega), if_neg (by omega)]
  · rw [if_neg (by omega), if_neg (by omega), if_pos h, if_pos h]

theorem adjP_symm (u w : ℕ) : adjP P u w = adjP P w u := by
  by_cases h : adjP P u w = true
  · rw [h]; symm
    obtain ⟨h1, h2, h3, h4, h5⟩ := (adjP_true_iff P u w).1 h
    refine (adjP_true_iff P w u).2 ⟨h1.symm, h1 ▸ h2, Ne.symm h3, fun ⟨a, b⟩ => h4 ⟨a.symm,
      Ne.symm b⟩, fun hm => ?_⟩
    rw [← atomOK_symm P h1 h3 hm.symm]
    exact h5 hm.symm
  · have h' : adjP P w u ≠ true := by
      intro h'
      obtain ⟨h1, h2, h3, h4, h5⟩ := (adjP_true_iff P w u).1 h'
      refine h ((adjP_true_iff P u w).2 ⟨h1.symm, h1 ▸ h2, Ne.symm h3, fun ⟨a, b⟩ => h4 ⟨a.symm,
        Ne.symm b⟩, fun hm => ?_⟩)
      rw [← atomOK_symm P h1 h3 hm.symm]
      exact h5 hm.symm
    simp only [Bool.not_eq_true] at h h'
    rw [h, h']

/-- **The graph** on `n` vertices. -/
def graph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u w := adjP P u w = true
  symm := ⟨fun u w h => by rw [adjP_symm]; exact h⟩
  loopless := ⟨fun u h => by rw [adjP_irrefl] at h; exact Bool.false_ne_true h⟩

/-! ### Vertices as triples -/

/-- The vertex of valuation `c`, candidate `e`, row `r`. -/
def enc (c e r : ℕ) : ℕ := (c * P.ne + e) * P.k + r

theorem rowOf_enc {c e r : ℕ} (hr : r < P.k) : rowOf P (enc P c e r) = r := by
  unfold rowOf enc
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem div_enc {c e r : ℕ} (hr : r < P.k) : enc P c e r / P.k = c * P.ne + e := by
  unfold enc
  have hk : 0 < P.k := by omega
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hk, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem eltOf_enc {c e r : ℕ} (he : e < P.ne) (hr : r < P.k) : eltOf P (enc P c e r) = e := by
  unfold eltOf
  rw [div_enc P hr, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt he]

theorem compOf_enc {c e r : ℕ} (he : e < P.ne) (hr : r < P.k) : compOf P (enc P c e r) = c := by
  unfold compOf
  have hn : 0 < P.ne := by omega
  rw [div_enc P hr, Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt he,
    Nat.zero_add]

theorem enc_lt {C c e r : ℕ} (hc : c < C) (he : e < P.ne) (hr : r < P.k) :
    enc P c e r < C * (P.ne * P.k) := by
  unfold enc
  have h1 : c * P.ne + e + 1 ≤ C * P.ne := by
    have : (c + 1) * P.ne ≤ C * P.ne := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have h2 : (c * P.ne + e + 1) * P.k ≤ C * P.ne * P.k := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, Nat.one_mul] at h2
  rw [← Nat.mul_assoc]; omega

theorem compOf_lt {C u : ℕ} (hu : u < C * (P.ne * P.k)) : compOf P u < C := by
  unfold compOf
  rw [Nat.div_div_eq_div_mul]
  apply Nat.div_lt_of_lt_mul
  rw [Nat.mul_comm P.k P.ne, Nat.mul_comm]; exact hu

theorem eltOf_lt {C u : ℕ} (hu : u < C * (P.ne * P.k)) : eltOf P u < P.ne := by
  unfold eltOf
  apply Nat.mod_lt
  rcases Nat.eq_zero_or_pos P.ne with h | h
  · rw [h] at hu; simp at hu
  · exact h

theorem rowOf_lt {C u : ℕ} (hu : u < C * (P.ne * P.k)) : rowOf P u < P.k := by
  unfold rowOf
  apply Nat.mod_lt
  rcases Nat.eq_zero_or_pos P.k with h | h
  · rw [h] at hu; simp at hu
  · exact h

/-! ### Numbers from bits -/

/-- The number whose first `q` bits are `β`. -/
def cOf (β : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | q + 1 => cOf β q + if β q then 2 ^ q else 0

theorem cOf_lt (β : ℕ → Bool) : ∀ q, cOf β q < 2 ^ q
  | 0 => by simp [cOf]
  | q + 1 => by
    have := cOf_lt β q
    rw [cOf, pow_succ]
    split_ifs <;> omega

theorem bitv_cOf (β : ℕ → Bool) : ∀ q m, m < q → bitv (cOf β q) m = if β m then 1 else 0
  | 0, m, h => absurd h (Nat.not_lt_zero _)
  | q + 1, m, h => by
    have hlt := cOf_lt β q
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
    rcases Nat.lt_or_ge m q with hm | hm
    · rw [← bitv_cOf β q m hm]
      unfold bitv
      rw [cOf]
      have e : 2 ^ q = 2 ^ (q - m) * 2 ^ m := by rw [← pow_add]; congr 1; omega
      have e2 : 2 ^ (q - m) = 2 * 2 ^ (q - m - 1) := by
        rw [← pow_succ']; congr 1; omega
      split_ifs
      · rw [e, Nat.add_mul_div_right _ _ hpos, e2, Nat.add_mul_mod_self_left]
      · rw [Nat.add_zero]
    · have hm' : m = q := by omega
      subst hm'
      unfold bitv
      rw [cOf]
      split_ifs with hb
      · rw [show cOf β m + 2 ^ m = cOf β m + 1 * 2 ^ m by ring, Nat.add_mul_div_right _ _ hpos,
          Nat.div_eq_of_lt hlt]
      · rw [Nat.add_zero, Nat.div_eq_of_lt hlt]

/-! ### The clique theorem -/

section Clique

open Classical

variable {q : ℕ} {Φ : (ℕ → ℕ) → Prop} {Aτ : ℕ → (ℕ → ℕ) → Prop} {F : Set ℕ}

/-- The hypotheses relating the data to a formula `Φ` with atoms `Aτ m`, `m < q`, and variables
`F`. -/
structure Hyp (P : Params) (q : ℕ) (Φ : (ℕ → ℕ) → Prop) (Aτ : ℕ → (ℕ → ℕ) → Prop)
    (F : Set ℕ) : Prop where
  /-- Two rows per atom, at least one atom. -/
  k_eq : P.k = 2 * q
  q_pos : 1 ≤ q
  /-- The atom test computes the atom, which depends only on its two rows' variables. -/
  atm_eq : ∀ m < q, ∀ ρ : ℕ → ℕ,
    P.atm m (ρ (P.vs (2 * m))) (ρ (P.vs (2 * m + 1))) = if Aτ m ρ then 1 else 0
  /-- A valuation that is the pattern of an assignment satisfies the formula iff the assignment
  does. -/
  ok_iff : ∀ c < 2 ^ q, ∀ ρ : ℕ → ℕ, (∀ m < q, bitv c m = 1 ↔ Aτ m ρ) → (P.ok c = 1 ↔ Φ ρ)
  /-- The variables of the rows are the variables `F`. -/
  vs_mem : ∀ r < P.k, P.vs r ∈ F
  mem_vs : ∀ v ∈ F, ∃ r < P.k, P.vs r = v

variable {P}

theorem atm_eq_bitv {c m : ℕ} {ρ : ℕ → ℕ} (h : Hyp P q Φ Aτ F) (hm : m < q)
    (hb : P.atm m (ρ (P.vs (2 * m))) (ρ (P.vs (2 * m + 1))) = bitv c m) :
    (bitv c m = 1 ↔ Aτ m ρ) := by
  rw [← hb, h.atm_eq m hm ρ]
  split_ifs with ha <;> simp [ha]

open Classical in
/-- From a clique, an assignment. -/
theorem sat_of_clique (h : Hyp P q Φ Aτ F) {s : Finset (Fin (2 ^ q * (P.ne * P.k)))}
    (hs : (graph P _).IsNClique P.k s) :
    ∃ ρ : ℕ → ℕ, (∀ v ∈ F, ∃ e < P.ne, P.E e = ρ v) ∧ Φ ρ := by
  have hk2 : 2 ≤ P.k := by have := h.q_pos; rw [h.k_eq]; omega
  have hcard : s.card = P.k := hs.card_eq
  have hadj : ∀ u ∈ s, ∀ w ∈ s, u ≠ w → adjP P u w = true := fun u hu w hw hne =>
    hs.1 hu hw hne
  -- some vertex
  obtain ⟨u0, hu0⟩ : s.Nonempty := Finset.card_pos.1 (by omega)
  -- rows are injective on `s`
  have hrowinj : ∀ u ∈ s, ∀ w ∈ s, rowOf P u = rowOf P w → u = w := by
    intro u hu w hw hr
    by_contra hne
    exact ((adjP_true_iff P u w).1 (hadj u hu w hw hne)).2.2.1 hr
  have himg : s.image (fun u : Fin (2 ^ q * (P.ne * P.k)) => rowOf P u) = Finset.range P.k := by
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hr
      exact Finset.mem_range.2 (rowOf_lt P u.2)
    · rw [Finset.card_image_of_injOn (fun u hu w hw hr => hrowinj u hu w hw hr), hcard]
      simp
  have hex : ∀ r < P.k, ∃ u ∈ s, rowOf P u = r := by
    intro r hr
    have : r ∈ s.image (fun u : Fin (2 ^ q * (P.ne * P.k)) => rowOf P u) := by rw [himg]; exact Finset.mem_range.2 hr
    obtain ⟨u, hu, hur⟩ := Finset.mem_image.1 this
    exact ⟨u, hu, hur⟩
  let pick : ℕ → Fin (2 ^ q * (P.ne * P.k)) := fun r => if hr : ∃ u ∈ s, rowOf P u = r then Classical.choose hr else u0
  have hpick : ∀ r < P.k, pick r ∈ s ∧ rowOf P (pick r) = r := by
    intro r hr
    have he := hex r hr
    simp only [pick, dif_pos he]
    exact Classical.choose_spec he
  -- the common valuation
  set c := compOf P u0 with hc
  have hcomp : ∀ u ∈ s, compOf P u = c := by
    intro u hu
    by_cases hne : u = u0
    · rw [hne]
    · exact ((adjP_true_iff P u u0).1 (hadj u hu u0 hu0 hne)).1
  have hclt : c < 2 ^ q := compOf_lt P u0.2
  have hpickne : ∀ r < P.k, ∀ r' < P.k, r ≠ r' → pick r ≠ pick r' := by
    intro r hr r' hr' hne heq
    apply hne
    rw [← (hpick r hr).2, ← (hpick r' hr').2, heq]
  have hadjpick : ∀ r < P.k, ∀ r' < P.k, r ≠ r' → adjP P (pick r) (pick r') = true :=
    fun r hr r' hr' hne => hadj _ (hpick r hr).1 _ (hpick r' hr').1 (hpickne r hr r' hr' hne)
  -- the value of each row
  let val : ℕ → ℕ := fun r => valOf P (pick r)
  let ρ : ℕ → ℕ := fun v => if hv : ∃ r, r < P.k ∧ P.vs r = v then val (Nat.find hv) else 0
  have hρ : ∀ r < P.k, ρ (P.vs r) = val r := by
    intro r hr
    have hv : ∃ r', r' < P.k ∧ P.vs r' = P.vs r := ⟨r, hr, rfl⟩
    simp only [ρ, dif_pos hv]
    obtain ⟨h1, h2⟩ := Nat.find_spec hv
    by_cases heq : Nat.find hv = r
    · rw [heq]
    · have ha := (adjP_true_iff P _ _).1 (hadjpick _ h1 r hr heq)
      rw [(hpick _ h1).2, (hpick r hr).2] at ha
      by_contra hne
      exact ha.2.2.2.1 ⟨h2, hne⟩
  -- the valuation is the pattern of `ρ`
  have hpat : ∀ m < q, (bitv c m = 1 ↔ Aτ m ρ) := by
    intro m hm
    have h2m : 2 * m + 1 < P.k := by rw [h.k_eq]; omega
    have ha := (adjP_true_iff P _ _).1 (hadjpick (2 * m) (by omega) (2 * m + 1) h2m (by omega))
    rw [(hpick _ (by omega)).2, (hpick _ h2m).2, hcomp _ (hpick _ (by omega)).1] at ha
    have hat := ha.2.2.2.2 (by omega)
    simp only [atomOK, decide_eq_true_eq, if_pos (show 2 * m < 2 * m + 1 by omega)] at hat
    rw [show 2 * m / 2 = m by omega] at hat
    refine atm_eq_bitv h hm ?_
    rw [hρ _ (by omega), hρ _ h2m]
    exact hat
  have hok : P.ok c = 1 := by
    have ha := (adjP_true_iff P _ _).1 (hadjpick 0 (by omega) 1 (by omega) (by omega))
    rw [hcomp _ (hpick 0 (by omega)).1] at ha
    exact ha.2.1
  refine ⟨ρ, fun v hv => ?_, (h.ok_iff c hclt ρ hpat).1 hok⟩
  obtain ⟨r, hr, rfl⟩ := h.mem_vs v hv
  exact ⟨eltOf P (pick r), eltOf_lt P (pick r).2, by rw [hρ r hr]; rfl⟩

open Classical in
/-- From an assignment, a clique. -/
theorem clique_of_sat (h : Hyp P q Φ Aτ F) {ρ : ℕ → ℕ}
    (hF : ∀ v ∈ F, ∃ e < P.ne, P.E e = ρ v) (hΦ : Φ ρ) :
    ∃ s : Finset (Fin (2 ^ q * (P.ne * P.k))), (graph P _).IsNClique P.k s := by
  set β : ℕ → Bool := fun m => decide (Aτ m ρ) with hβ
  set c := cOf β q with hc
  have hclt : c < 2 ^ q := cOf_lt β q
  have hbit : ∀ m < q, bitv c m = if Aτ m ρ then 1 else 0 := by
    intro m hm
    rw [hc, bitv_cOf β q m hm]
    simp [hβ]
  have hok : P.ok c = 1 :=
    (h.ok_iff c hclt ρ fun m hm => by rw [hbit m hm]; split_ifs with ha <;> simp [ha]).2 hΦ
  have hE : ∀ r < P.k, ∃ e < P.ne, P.E e = ρ (P.vs r) := fun r hr => hF _ (h.vs_mem r hr)
  let e : ℕ → ℕ := fun r => if hr : r < P.k then Classical.choose (hE r hr) else 0
  have he : ∀ r < P.k, e r < P.ne ∧ P.E (e r) = ρ (P.vs r) := by
    intro r hr
    simp only [e, dif_pos hr]
    exact Classical.choose_spec (hE r hr)
  let vtx : Fin P.k → Fin (2 ^ q * (P.ne * P.k)) := fun r =>
    ⟨enc P c (e r) r, enc_lt P hclt (he r r.2).1 r.2⟩
  have hrow : ∀ r : Fin P.k, rowOf P (vtx r) = r := fun r => rowOf_enc P r.2
  have hcomp : ∀ r : Fin P.k, compOf P (vtx r) = c := fun r => compOf_enc P (he r r.2).1 r.2
  have hval : ∀ r : Fin P.k, valOf P (vtx r) = ρ (P.vs r) := fun r => by
    unfold valOf; rw [eltOf_enc P (he r r.2).1 r.2]; exact (he r r.2).2
  have hinj : Function.Injective vtx := by
    intro r r' hrr
    apply Fin.ext
    rw [← hrow r, ← hrow r', hrr]
  refine ⟨Finset.univ.image vtx, ?_⟩
  rw [SimpleGraph.isNClique_iff]
  refine ⟨?_, by rw [Finset.card_image_of_injective _ hinj]; simp⟩
  intro a ha b hb hab
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
  obtain ⟨r, rfl⟩ := ha
  obtain ⟨r', rfl⟩ := hb
  have hrr : (r : ℕ) ≠ r' := fun h' => hab (by rw [Fin.ext h'])
  show adjP P (vtx r) (vtx r') = true
  refine (adjP_true_iff P _ _).2 ⟨by rw [hcomp, hcomp], by rw [hcomp]; exact hok, ?_, ?_, ?_⟩
  · rw [hrow, hrow]; exact hrr
  · rintro ⟨h1, h2⟩
    rw [hrow, hrow] at h1
    rw [hval, hval, h1] at h2
    exact h2 rfl
  · intro hm
    rw [hrow, hrow] at hm ⊢
    rw [hcomp, hval, hval]
    set m := (r : ℕ) / 2 with hmdef
    have hmq : m < q := by have := r.2; have := h.k_eq; omega
    have hat := h.atm_eq m hmq ρ
    rw [← hbit m hmq] at hat
    unfold atomOK
    rw [decide_eq_true_eq]
    rcases Nat.lt_or_gt_of_ne hrr with hlt | hgt
    · rw [if_pos hlt, if_pos hlt, ← hmdef]
      have h1 : (r : ℕ) = 2 * m := by omega
      have h2 : (r' : ℕ) = 2 * m + 1 := by omega
      rw [h1, h2]; exact hat
    · rw [if_neg (by omega), if_neg (by omega), ← hmdef]
      have h1 : (r : ℕ) = 2 * m + 1 := by omega
      have h2 : (r' : ℕ) = 2 * m := by omega
      rw [h1, h2]; exact hat

/-- **The clique theorem.** -/
theorem clique_iff (h : Hyp P q Φ Aτ F) :
    (∃ s : Finset (Fin (2 ^ q * (P.ne * P.k))), (graph P _).IsNClique P.k s) ↔
      ∃ ρ : ℕ → ℕ, (∀ v ∈ F, ∃ e < P.ne, P.E e = ρ v) ∧ Φ ρ :=
  ⟨fun ⟨_, hs⟩ => sat_of_clique h hs, fun ⟨_, hF, hΦ⟩ => clique_of_sat h hF hΦ⟩

end Clique

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core
