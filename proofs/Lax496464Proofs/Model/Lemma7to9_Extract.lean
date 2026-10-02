import Lax496464Proofs.Model.Lemma6_Schedule
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Lax496464Proofs

/-!
# Section 8, Lemmas 7–9: Extracting a Hitting Set from a Schedule

The converse of `Lemma6_Schedule.lean`, and the longest file of the development. It runs
from the arithmetic core of Lemma 7 — the paper's inequality (9), in the form that makes
it a statement about prefix counts rather than about schedules — through Lemma 8 and the
stable-segment argument to `Setup.lemma9`, which hands the hitting set back.

## What Inequality (9) Actually Says

Lemma 7 bounds how many dummy jobs a feasible set can contain: at most `2(k−1)` per epoch
on average, over every prefix of the epochs. The proof is by minimal counterexample. Fix
the first epoch position `ℓ` where the bound fails, so that

* every *shorter* prefix obeys it — at most `2(k−1)·t` dummies in the first `t` epochs, and
* the prefix of length `ℓ` does not: it holds at least `2(k−1)·ℓ + 1` dummies.

Since a dummy of the epoch at position `g` costs `g·(n+1)` to preprocess, the cheapest way
to hold that many dummies inside the first `ℓ` epochs is to saturate every earlier prefix —
`2(k−1)` in each of the first `ℓ−1` epochs and `2(k−1)+1` in the `ℓ`-th. That is exactly
what the paper writes down, and `weighted_lower_bound` below is that step, stated for an
arbitrary count sequence `c` and an arbitrary per-epoch allowance `d`:

> if every prefix of length `t ≤ L` has `∑_{g<t} c g ≤ d·t`, and the prefix of length
> `L+1` has at least `d·(L+1) + 1`, then `∑_{g<L+1} c g · (g+1) ≥ (d/2)·(L+1)(L+2) + (L+1)`.

(Stated doubled, `2 · ∑ … ≥ d·(L+1)(L+2) + 2(L+1)`, so that no division appears.)

Multiplying by `(n+1)` and using `Q = (k−1)(n+1)` with `d = 2(k−1)` turns the right-hand
side into `Q·ℓ(ℓ+1) + ℓ(n+1)`, which strictly exceeds `Q·ℓ(ℓ+1) + n` — the *largest start
time of any dummy in the first `ℓ` epochs*, since `s(B) = g(g+1)Q + o` with `o ≤ n`. So
`FFJ.Preprocessable` fails at that job, and the counterexample cannot have been feasible.

## The Route Through Abel Summation

`abel_prefix` is the only non-obvious step: writing `F t = ∑_{g<t} c g` for the prefix
counts,

```
∑_{g<ℓ} c g · (g+1)  +  ∑_{t<ℓ} F t  =  ℓ · F ℓ
```

which converts a statement about the *weighted* sum (what preprocessing time costs) into
one about *prefix* sums (what the induction hypothesis controls). It is proved by a
three-line induction, and it is stated additively so that no natural-number subtraction
ever appears.
-/


namespace FlexFlowJIT

namespace Theorem1

/-! ## 1. Abel summation -/

/-- **Abel summation, in the additive form.** The weighted sum `∑ c g · (g+1)` and the sum
of all prefix counts together make up `ℓ · F ℓ`. Stated as an equation between naturals
with no subtraction, so it can be used in either direction. -/
lemma abel_prefix (c : ℕ → ℕ) (ℓ : ℕ) :
    (∑ g ∈ Finset.range ℓ, c g * (g + 1))
        + (∑ t ∈ Finset.range ℓ, ∑ g ∈ Finset.range t, c g)
      = ℓ * ∑ g ∈ Finset.range ℓ, c g := by
  induction ℓ with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ (fun g => c g * (g + 1)),
        Finset.sum_range_succ (fun t => ∑ g ∈ Finset.range t, c g),
        Finset.sum_range_succ c]
      calc (∑ g ∈ Finset.range L, c g * (g + 1)) + c L * (L + 1)
              + ((∑ t ∈ Finset.range L, ∑ g ∈ Finset.range t, c g)
                + ∑ g ∈ Finset.range L, c g)
          = ((∑ g ∈ Finset.range L, c g * (g + 1))
              + ∑ t ∈ Finset.range L, ∑ g ∈ Finset.range t, c g)
            + (c L * (L + 1) + ∑ g ∈ Finset.range L, c g) := by ring
        _ = L * (∑ g ∈ Finset.range L, c g)
            + (c L * (L + 1) + ∑ g ∈ Finset.range L, c g) := by rw [ih]
        _ = (L + 1) * ((∑ g ∈ Finset.range L, c g) + c L) := by ring

/-! ## 2. Inequality (9) -/

/-- **The paper's inequality (9).** A count sequence whose every proper prefix respects the
allowance `d`, but whose prefix of length `L+1` exceeds it, has a large weighted sum — the
excess has to be paid for in the expensive late epochs.

Doubled to keep everything in `ℕ`: the real statement divides the right-hand side by two.
-/
lemma weighted_lower_bound (c : ℕ → ℕ) (d L : ℕ)
    (hpre : ∀ t, t ≤ L → (∑ g ∈ Finset.range t, c g) ≤ d * t)
    (hbig : d * (L + 1) + 1 ≤ ∑ g ∈ Finset.range (L + 1), c g) :
    d * (L + 1) * (L + 2) + 2 * (L + 1)
      ≤ 2 * ∑ g ∈ Finset.range (L + 1), c g * (g + 1) := by
  have habel := abel_prefix c (L + 1)
  have h1 : (∑ t ∈ Finset.range (L + 1), ∑ g ∈ Finset.range t, c g)
      ≤ ∑ t ∈ Finset.range (L + 1), d * t :=
    Finset.sum_le_sum fun t ht => hpre t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))
  have h2 : (∑ t ∈ Finset.range (L + 1), d * t) * 2 = d * ((L + 1) * L) := by
    rw [← Finset.mul_sum, mul_assoc, Finset.sum_range_id_mul_two (L + 1)]
    simp
  have hmul : (L + 1) * (d * (L + 1) + 1) ≤ (L + 1) * ∑ g ∈ Finset.range (L + 1), c g :=
    Nat.mul_le_mul_left _ hbig
  have hring : 2 * ((L + 1) * (d * (L + 1) + 1))
      = d * (L + 1) * (L + 2) + 2 * (L + 1) + d * ((L + 1) * L) := by ring
  omega

/-! ## 3. Minimal counterexample, packaged

`weighted_lower_bound` is what refutes a *first* violation. This is the induction that
turns "no first violation" into "no violation": the shape Lemma 7 will be proved in, once
the scheduling side supplies the single step from `FFJ.Preprocessable`. -/

/-- If a prefix count can never be the *first* to exceed its allowance, it never exceeds
it. -/
lemma prefix_count_le (c : ℕ → ℕ) (d : ℕ)
    (hstep : ∀ L, (∀ t, t ≤ L → (∑ g ∈ Finset.range t, c g) ≤ d * t) →
      (∑ g ∈ Finset.range (L + 1), c g) ≤ d * (L + 1)) :
    ∀ ℓ, (∑ g ∈ Finset.range ℓ, c g) ≤ d * ℓ := by
  have key : ∀ ℓ, ∀ t, t ≤ ℓ → (∑ g ∈ Finset.range t, c g) ≤ d * t := by
    intro ℓ
    induction ℓ with
    | zero =>
        intro t ht
        have : t = 0 := by omega
        subst this
        simp
    | succ L ih =>
        intro t ht
        rcases Nat.lt_or_ge t (L + 1) with h | h
        · exact ih t (by omega)
        · have hteq : t = L + 1 := by omega
          subst hteq
          exact hstep L ih
  exact fun ℓ => key ℓ ℓ le_rfl

variable (P : HSInstance) (k : ℕ)

/-! ## 4. Counting dummy jobs by epoch

The bridge from §2–§3's arithmetic to the shop. `dumCount Z a` is how many dummy jobs of
`Z` sit in the epoch at position `a`, and `sum_jp_dumsBelow` is the only fact about it that
matters: the total preprocessing time of the dummies of `Z` in the first `ℓ` epochs is
`(n+1) · ∑_{a<ℓ} (dumCount Z a) · (a+1)` — exactly the weighted sum
`weighted_lower_bound` bounds from below, since a dummy of the epoch at position `a` costs
`g·(n+1) = (a+1)(n+1)` to preprocess. -/

/-- Whether a job is one of the two dummies (rather than a selection job). -/
def isDummy : Jobs P k → Bool := fun x =>
  match x with
  | .inl _ => false
  | .inr _ => true

lemma jp_of_isDummy {x : Jobs P k} (h : isDummy P k x = true) :
    jp P k x = (epochIdx P k x + 1) * (P.n + 1) := by
  match x with
  | .inl _ => simp [isDummy] at h
  | .inr (.inl (r, j, i)) => rfl
  | .inr (.inr (r, j, i)) => rfl

/-- How many dummy jobs of `Z` live in the epoch at position `a`. -/
def dumCount (Z : Finset (Jobs P k)) (a : ℕ) : ℕ :=
  (Z.filter (fun x => isDummy P k x = true ∧ epochIdx P k x = a)).card

/-- The dummy jobs of `Z` in the first `ℓ` epochs. -/
def dumsBelow (Z : Finset (Jobs P k)) (ℓ : ℕ) : Finset (Jobs P k) :=
  Z.filter (fun x => isDummy P k x = true ∧ epochIdx P k x < ℓ)

/-- **The preprocessing time of a prefix of dummies, by epoch.** -/
lemma sum_jp_dumsBelow (Z : Finset (Jobs P k)) (ℓ : ℕ) :
    ∑ x ∈ dumsBelow P k Z ℓ, jp P k x
      = (P.n + 1) * ∑ a ∈ Finset.range ℓ, dumCount P k Z a * (a + 1) := by
  have hmaps : ∀ x ∈ dumsBelow P k Z ℓ, epochIdx P k x ∈ Finset.range ℓ := by
    intro x hx
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (jp P k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hfib : (dumsBelow P k Z ℓ).filter (fun x => epochIdx P k x = a)
      = Z.filter (fun x => isDummy P k x = true ∧ epochIdx P k x = a) := by
    ext x
    simp only [dumsBelow, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hz, hd, -⟩, he⟩
      exact ⟨hz, hd, he⟩
    · rintro ⟨hz, hd, he⟩
      exact ⟨⟨hz, hd, he ▸ Finset.mem_range.mp ha⟩, he⟩
  rw [hfib]
  have hconst : ∀ x ∈ Z.filter (fun x => isDummy P k x = true ∧ epochIdx P k x = a),
      jp P k x = (a + 1) * (P.n + 1) := by
    intro x hx
    obtain ⟨-, hd, he⟩ := Finset.mem_filter.mp hx
    rw [jp_of_isDummy P k hd, he]
  rw [Finset.sum_congr rfl hconst]
  simp only [Finset.sum_const, dumCount]
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-! ## 5. Lemma 7

Condition 1, in naturals, then the minimal-counterexample argument itself. -/

/-- **Condition 1, applied to a prefix.** If every job of `D ⊆ Z` starts no later than
`j` does, then `D`'s total preprocessing time fits before `j`'s own start.

Stated in `ℕ`, which is where the rest of the argument lives; the cast is done once here
rather than at every use. -/
lemma sum_jp_le_of_max {Z : Finset (Jobs P k)} (h : (inst P k).Preprocessable Z)
    {D : Finset (Jobs P k)} (hDZ : D ⊆ Z) {j : Jobs P k} (hj : j ∈ Z)
    (hmax : ∀ x ∈ D, sN P k x ≤ sN P k j) :
    ∑ x ∈ D, jp P k x ≤ sN P k j := by
  have hmax' : ∀ x ∈ D, (inst P k).s x ≤ (inst P k).s j := by
    intro x hx
    rw [s_eq_sN, s_eq_sN]
    exact_mod_cast hmax x hx
  have hfin := FFJ.Preprocessable.sum_le (inst P k) h hDZ hj hmax'
  rw [s_eq_sN] at hfin
  refine (Nat.cast_le (α := ℤ)).mp ?_
  calc ((∑ x ∈ D, jp P k x : ℕ) : ℤ) = ∑ x ∈ D, ((inst P k).p x : ℤ) := by push_cast; rfl
    _ ≤ ((sN P k j : ℕ) : ℤ) := hfin

/-- A dummy in one of the first `ℓ` epochs starts no later than `ℓ(ℓ+1)Q + n` — the latest
start time available in that range, attained by a `B` job of the last of them. -/
lemma sN_le_of_dummy {ℓ : ℕ} {x : Jobs P k} (hd : isDummy P k x = true)
    (ha : epochIdx P k x < ℓ) : sN P k x ≤ ℓ * (ℓ + 1) * Q P k + P.n := by
  rcases x with y | y | y
  · simp [isDummy] at hd
  · obtain ⟨r, j, i⟩ := y
    have hlt : gp P r.val j < ℓ := ha
    have hi : i.val + 1 ≤ P.n := i.isLt
    have hmul : (gp P r.val j + 1) ^ 2 * Q P k ≤ ℓ * (ℓ + 1) * Q P k := by
      refine Nat.mul_le_mul_right _ ?_
      have hsq : (gp P r.val j + 1) ^ 2 = (gp P r.val j + 1) * (gp P r.val j + 1) := by ring
      rw [hsq]
      exact Nat.mul_le_mul (by omega) (by omega)
    simp only [sN, G, g_eq_gp_succ]
    omega
  · obtain ⟨r, j, i⟩ := y
    have hlt : gp P r.val j < ℓ := ha
    have hi : i.val + 1 ≤ P.n := i.isLt
    have hid : (gp P r.val j + 1) ^ 2 * Q P k + (gp P r.val j + 1) * Q P k
        = (gp P r.val j + 1) * (gp P r.val j + 2) * Q P k := by ring
    have hmul : (gp P r.val j + 1) * (gp P r.val j + 2) * Q P k ≤ ℓ * (ℓ + 1) * Q P k :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
    simp only [sN, G, g_eq_gp_succ]
    omega

/-- **The preprocessing budget of a prefix of epochs.** Whatever a feasible set holds in
the first `ℓ` epochs must be preprocessed before the last of those jobs starts, and that is
at most `ℓ(ℓ+1)Q + n`.

This is Condition 1 in the shape both halves of Lemma 7 consume: the left-hand side is the
weighted count `weighted_lower_bound` bounds from below. -/
lemma dums_weighted_le {Z : Finset (Jobs P k)} (hfeas : (inst P k).Feasible Z) (ℓ : ℕ)
    (hne : (dumsBelow P k Z ℓ).Nonempty) :
    (P.n + 1) * (∑ a ∈ Finset.range ℓ, dumCount P k Z a * (a + 1))
      ≤ ℓ * (ℓ + 1) * Q P k + P.n := by
  obtain ⟨hpp, -⟩ := ((inst P k).feasible_iff Z).mp hfeas
  obtain ⟨j, hjmem, hjmax⟩ := (dumsBelow P k Z ℓ).exists_max_image (sN P k) hne
  obtain ⟨hjZ, hjd, hja⟩ := Finset.mem_filter.mp hjmem
  have hle : ∑ x ∈ dumsBelow P k Z ℓ, jp P k x ≤ sN P k j :=
    sum_jp_le_of_max P k hpp (D := dumsBelow P k Z ℓ) (Finset.filter_subset _ _) hjZ hjmax
  have hsum := sum_jp_dumsBelow P k Z ℓ
  have hs := sN_le_of_dummy P k hjd hja
  omega

/-- If a prefix of epochs holds any dummies at all, the corresponding job set is
nonempty. -/
lemma dumsBelow_nonempty {Z : Finset (Jobs P k)} {ℓ : ℕ}
    (h : 0 < ∑ a ∈ Finset.range ℓ, dumCount P k Z a) : (dumsBelow P k Z ℓ).Nonempty := by
  rcases Finset.eq_empty_or_nonempty (dumsBelow P k Z ℓ) with he | hn
  · exfalso
    have hzero : ∀ a ∈ Finset.range ℓ, dumCount P k Z a = 0 := by
      intro a ha
      rw [dumCount, Finset.card_eq_zero]
      ext x
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro hz hd he'
      have hmem : x ∈ dumsBelow P k Z ℓ :=
        Finset.mem_filter.mpr ⟨hz, hd, he' ▸ Finset.mem_range.mp ha⟩
      rw [he] at hmem
      exact absurd hmem (Finset.notMem_empty x)
    rw [Finset.sum_congr rfl hzero] at h
    simp at h
  · exact hn

/-- **Lemma 7.** A feasible set holds at most `2(k−1)` dummy jobs per epoch, over every
prefix of the epochs.

The proof is the paper's: a *first* violation at epoch `ℓ` would force the dummies of the
first `ℓ` epochs to need more preprocessing time than the latest of them has available,
contradicting Condition 1. `weighted_lower_bound` is the arithmetic and `prefix_count_le`
the induction; everything here is the translation between them. -/
theorem lemma7 {Z : Finset (Jobs P k)} (hfeas : (inst P k).Feasible Z) (ℓ : ℕ) :
    ∑ a ∈ Finset.range ℓ, dumCount P k Z a ≤ 2 * (k - 1) * ℓ := by
  refine prefix_count_le (dumCount P k Z) (2 * (k - 1)) ?_ ℓ
  intro L hpre
  by_contra hcon
  have hbig : 2 * (k - 1) * (L + 1) + 1 ≤ ∑ a ∈ Finset.range (L + 1), dumCount P k Z a := by
    omega
  have hbound := weighted_lower_bound (dumCount P k Z) (2 * (k - 1)) L hpre hbig
  have hbudget := dums_weighted_le P k hfeas (L + 1) (dumsBelow_nonempty P k (by omega))
  have hid3 : (L + 1) * (L + 1 + 1) * Q P k = (L + 1) * (L + 2) * Q P k := by ring
  rw [hid3] at hbudget
  -- the prefix needs strictly more preprocessing time than it has
  have hQ : (P.n + 1) * (k - 1) = Q P k := by simp only [Q]; ring
  have hW := Nat.mul_le_mul_left (P.n + 1) hbound
  have hid1 : (P.n + 1) * (2 * (k - 1) * (L + 1) * (L + 2) + 2 * (L + 1))
      = 2 * ((L + 1) * (L + 2) * Q P k) + 2 * ((P.n + 1) * (L + 1)) := by
    rw [← hQ]; ring
  have hid2 : (P.n + 1) * (2 * ∑ a ∈ Finset.range (L + 1), dumCount P k Z a * (a + 1))
      = 2 * ((P.n + 1) * ∑ a ∈ Finset.range (L + 1), dumCount P k Z a * (a + 1)) := by ring
  have hpos : P.n + 1 ≤ (P.n + 1) * (L + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-! ## 6. Lemma 7's second clause: attaining the bound forces exactness

Lemma 7 also claims that a set attaining `2(k−1)·R·m` dummies has exactly `2(k−1)` in
*each* epoch. That does **not** follow from the prefix bounds and the total alone — the
counts `(2(k−2), 2k, …)` satisfy both — so it needs its own argument, and the paper gives
one: a shortfall in an early epoch has to be made up later, where dummies cost strictly
more to preprocess, pushing the total past the budget.

`weighted_lower_bound_strict` is that step. Its hypothesis is a *strict* deficit in some
proper prefix; its conclusion beats the exact-fit value `d·ℓ(ℓ+1)/2` by one whole unit,
which is all the slack `dums_weighted_le` leaves. -/

/-- With the total attained and some proper prefix strictly short of its allowance, the
weighted sum strictly exceeds the exact-fit value. Doubled, to stay in `ℕ`. -/
lemma weighted_lower_bound_strict (c : ℕ → ℕ) (d ℓ t₀ : ℕ)
    (hpre : ∀ t, t ≤ ℓ → (∑ g ∈ Finset.range t, c g) ≤ d * t)
    (htot : (∑ g ∈ Finset.range ℓ, c g) = d * ℓ)
    (ht₀ : t₀ < ℓ) (hdef : (∑ g ∈ Finset.range t₀, c g) + 1 ≤ d * t₀) :
    d * ℓ * (ℓ + 1) + 2 ≤ 2 * ∑ g ∈ Finset.range ℓ, c g * (g + 1) := by
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  have habel := abel_prefix c (L + 1)
  rw [htot] at habel
  -- the prefix sums fall strictly short in total
  have hlt : (∑ t ∈ Finset.range (L + 1), ∑ g ∈ Finset.range t, c g)
      < ∑ t ∈ Finset.range (L + 1), d * t := by
    exact Finset.sum_lt_sum (fun t ht => hpre t (le_of_lt (Finset.mem_range.mp ht)))
      ⟨t₀, Finset.mem_range.mpr ht₀, by omega⟩
  have hD : (∑ t ∈ Finset.range (L + 1), d * t) * 2 = d * ((L + 1) * L) := by
    rw [← Finset.mul_sum, mul_assoc, Finset.sum_range_id_mul_two (L + 1)]
    simp
  have hring : 2 * ((L + 1) * (d * (L + 1)))
      = d * (L + 1) * (L + 1 + 1) + d * ((L + 1) * L) := by ring
  omega

/-- **Lemma 7, second clause.** A feasible set attaining the dummy bound over the first `ℓ`
epochs holds exactly `2(k−1)` dummies in each one of them.

`k ≤ 1` is a real special case rather than a formality: there the allowance is `0`, the
construction has no dummy jobs at all, and `dums_weighted_le`'s nonemptiness hypothesis
genuinely fails. It is dispatched first. -/
theorem lemma7_exact {Z : Finset (Jobs P k)} (hfeas : (inst P k).Feasible Z) {ℓ : ℕ}
    (htot : (∑ a ∈ Finset.range ℓ, dumCount P k Z a) = 2 * (k - 1) * ℓ)
    {a : ℕ} (ha : a < ℓ) : dumCount P k Z a = 2 * (k - 1) := by
  rcases Nat.eq_zero_or_pos (2 * (k - 1)) with hd0 | hdpos
  · -- the allowance is zero, so there are no dummies to distribute
    rw [hd0] at htot ⊢
    rw [zero_mul] at htot
    exact Finset.sum_eq_zero_iff.mp htot a (Finset.mem_range.mpr ha)
  have hposum : 0 < ∑ a ∈ Finset.range ℓ, dumCount P k Z a := by
    rw [htot]
    exact Nat.mul_pos hdpos (by omega)
  -- every prefix is exactly at its allowance ...
  have hall : ∀ t, t ≤ ℓ → (∑ g ∈ Finset.range t, dumCount P k Z g) = 2 * (k - 1) * t := by
    intro t ht
    by_contra hne'
    have hdef : (∑ g ∈ Finset.range t, dumCount P k Z g) + 1 ≤ 2 * (k - 1) * t := by
      have := lemma7 P k hfeas t
      omega
    have htlt : t < ℓ := by
      rcases Nat.lt_or_ge t ℓ with h | h
      · exact h
      · exfalso
        have hteq : t = ℓ := by omega
        subst hteq
        exact hne' htot
    have hstrict := weighted_lower_bound_strict (dumCount P k Z) (2 * (k - 1)) ℓ t
      (fun s _ => lemma7 P k hfeas s) htot htlt hdef
    have hbudget := dums_weighted_le P k hfeas ℓ (dumsBelow_nonempty P k hposum)
    have hQ : (P.n + 1) * (k - 1) = Q P k := by simp only [Q]; ring
    have hW := Nat.mul_le_mul_left (P.n + 1) hstrict
    have hid1 : (P.n + 1) * (2 * (k - 1) * ℓ * (ℓ + 1) + 2)
        = 2 * (ℓ * (ℓ + 1) * Q P k) + 2 * (P.n + 1) := by rw [← hQ]; ring
    have hid2 : (P.n + 1) * (2 * ∑ g ∈ Finset.range ℓ, dumCount P k Z g * (g + 1))
        = 2 * ((P.n + 1) * ∑ g ∈ Finset.range ℓ, dumCount P k Z g * (g + 1)) := by ring
    omega
  -- ... so each epoch's count is the difference of two consecutive allowances
  have h1 := hall a (by omega)
  have h2 := hall (a + 1) (by omega)
  rw [Finset.sum_range_succ] at h2
  have hring : 2 * (k - 1) * (a + 1) = 2 * (k - 1) * a + 2 * (k - 1) := by ring
  omega

/-! ## 7. Toward Lemma 8: what shares a machine inside one epoch

Lemma 8 needs the per-epoch machine capacity `2·selₐ + cₐ ≤ 2k`, and that is where
Condition 2 finally enters: a machine running a selection job in an epoch can run nothing
else in it, and a machine without one runs at most an `A` and a `B`.

All of it follows from one inequality. Writing `off x` for the element offset `i + 1`
(at most `n`) and `a` for the epoch position, every job of the epoch starts at
`(a+1)²Q + off` — except a `B`, which starts `(a+1)Q` later — and is due at
`(a+1)²Q + (2(a+1)+1)Q + off`, except an `A`, which is due `(a+1)Q` after the start of the
epoch. So `s` and `d` are the same expression with different multiples of `Q`, and since
`off ≤ n < Q` (this is where `k ≥ 2` is needed: `Q = (k−1)(n+1) ≥ n+1`), the offsets can
never bridge a gap of a whole `Q`. Hence `s x < d y` for any two jobs of one epoch **except**
when `x` is a `B` and `y` is its epoch's `A` — the one pair that genuinely may not overlap,
and exactly the pair the schedule of Lemma 6 puts together on one machine. -/

/-- The element offset `i + 1` a job carries in its due date. -/
def off : Jobs P k → ℕ
  | .inl (_, ⟨_, i⟩) => i.val.val + 1
  | .inr (.inl (_, _, i)) => i.val + 1
  | .inr (.inr (_, _, i)) => i.val + 1

lemma off_le (x : Jobs P k) : off P k x ≤ P.n := by
  rcases x with u | u | u
  · obtain ⟨r, j, i⟩ := u; exact i.val.isLt
  · obtain ⟨r, j, i⟩ := u; exact i.isLt
  · obtain ⟨r, j, i⟩ := u; exact i.isLt

/-- Which family a job belongs to: `0` selection, `1` the `A` dummy, `2` the `B` dummy. -/
def kind : Jobs P k → ℕ
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- `Q` exceeds every element offset — the one place `k ≥ 2` is used. -/
lemma off_lt_Q (hk : 2 ≤ k) (x : Jobs P k) : off P k x < Q P k := by
  have h1 := off_le P k x
  have h2 : 1 * (P.n + 1) ≤ (k - 1) * (P.n + 1) := Nat.mul_le_mul_right _ (by omega)
  simp only [Q]
  omega

lemma sN_eq (x : Jobs P k) :
    sN P k x = (epochIdx P k x + 1) ^ 2 * Q P k
      + (if kind P k x = 2 then (epochIdx P k x + 1) * Q P k else 0) + off P k x := by
  rcases x with u | u | u
  · obtain ⟨r, j, i⟩ := u; simp [sN, kind, epochIdx, off, G, g_eq_gp_succ]
  · obtain ⟨r, j, i⟩ := u; simp [sN, kind, epochIdx, off, G, g_eq_gp_succ]
  · obtain ⟨r, j, i⟩ := u; simp [sN, kind, epochIdx, off, G, g_eq_gp_succ]

lemma jd_eq (x : Jobs P k) :
    jd P k x = (epochIdx P k x + 1) ^ 2 * Q P k
      + (if kind P k x = 1 then (epochIdx P k x + 1) * Q P k
         else (2 * (epochIdx P k x + 1) + 1) * Q P k) + off P k x := by
  rcases x with u | u | u
  · obtain ⟨r, j, i⟩ := u; simp [jd, kind, epochIdx, off, G, g_eq_gp_succ]
  · obtain ⟨r, j, i⟩ := u; simp [jd, kind, epochIdx, off, G, g_eq_gp_succ]
  · obtain ⟨r, j, i⟩ := u; simp [jd, kind, epochIdx, off, G, g_eq_gp_succ]

/-- **The one inequality.** Inside one epoch, every job starts before every other is due,
with the single exception of a `B` against its epoch's `A`. -/
lemma sN_lt_jd (hk : 2 ≤ k) {x y : Jobs P k} (he : epochIdx P k x = epochIdx P k y)
    (hne : ¬ (kind P k x = 2 ∧ kind P k y = 1)) : sN P k x < jd P k y := by
  have hox := off_lt_Q P k hk x
  rw [sN_eq, jd_eq, he]
  set a := epochIdx P k y
  set Qv := Q P k
  have hmul : Qv ≤ (a + 1) * Qv := Nat.le_mul_of_pos_left _ (by omega)
  have hmul2 : (a + 1) * Qv ≤ (2 * (a + 1) + 1) * Qv := Nat.mul_le_mul_right _ (by omega)
  by_cases h1 : kind P k x = 2 <;> by_cases h2 : kind P k y = 1
  · exact absurd ⟨h1, h2⟩ hne
  · rw [if_pos h1, if_neg h2]
    have hstep : (a + 1) * Qv + Qv ≤ (2 * (a + 1) + 1) * Qv := by
      have hEq : (a + 1) * Qv + Qv = (a + 1 + 1) * Qv := by ring
      rw [hEq]
      exact Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [if_neg h1, if_pos h2]
    omega
  · rw [if_neg h1, if_neg h2]
    omega

/-- **What cannot share a machine.** Two distinct jobs of one epoch conflict whenever they
are not an `A`/`B` pair — in particular whenever one of them is a selection job. -/
lemma conflict_of_same_epoch (hk : 2 ≤ k) {x y : Jobs P k}
    (he : epochIdx P k x = epochIdx P k y)
    (hx : ¬ (kind P k x = 2 ∧ kind P k y = 1))
    (hy : ¬ (kind P k y = 2 ∧ kind P k x = 1)) : (inst P k).Conflict x y := by
  constructor
  · rw [s_eq_sN]
    exact_mod_cast sN_lt_jd P k hk he hx
  · rw [s_eq_sN]
    exact_mod_cast sN_lt_jd P k hk he.symm hy

/-! ## 8. The per-epoch machine capacity

`2·selₐ + cₐ ≤ 2k`, by an injection into `machines × {0,1}`: send each job of the epoch to
its machine tagged `1` if it is a `B` and `0` otherwise, and send each *selection* job a
second time to its machine tagged `1`. Two jobs colliding under that map would have to
share a machine while conflicting — the only pair `conflict_of_same_epoch` allows to share
is an `A` with a `B`, and those two get tags `0` and `1`. The doubling of the selection
jobs is what expresses "a machine running a selection job runs nothing else". -/

/-- The jobs of `Z` in the epoch at position `a`. -/
def epochOf (Z : Finset (Jobs P k)) (a : ℕ) : Finset (Jobs P k) :=
  Z.filter (fun x => epochIdx P k x = a)

/-- How many selection jobs of `Z` live in the epoch at position `a`. -/
def selCount (Z : Finset (Jobs P k)) (a : ℕ) : ℕ :=
  ((epochOf P k Z a).filter (fun x => kind P k x = 0)).card

lemma isDummy_iff_kind (x : Jobs P k) : isDummy P k x = true ↔ ¬ kind P k x = 0 := by
  rcases x with u | u | u <;> simp [isDummy, kind]

/-- The epoch splits into its selection jobs and its dummies. -/
lemma selCount_add_dumCount (Z : Finset (Jobs P k)) (a : ℕ) :
    selCount P k Z a + dumCount P k Z a = (epochOf P k Z a).card := by
  have hd : dumCount P k Z a
      = ((epochOf P k Z a).filter (fun x => ¬ kind P k x = 0)).card := by
    rw [dumCount, epochOf, Finset.filter_filter]
    congr 1
    apply Finset.filter_congr
    intro x _
    rw [isDummy_iff_kind]
    exact and_comm
  rw [selCount, hd]
  exact Finset.card_filter_add_card_filter_not _

/-- **The capacity of one epoch.** -/
theorem epoch_capacity (hk : 2 ≤ k) {Z : Finset (Jobs P k)}
    (hfeas : (inst P k).Feasible Z) (a : ℕ) :
    (epochOf P k Z a).card + selCount P k Z a ≤ 2 * k := by
  classical
  obtain ⟨-, c, hlt, hindep⟩ := ((inst P k).feasible_iff Z).mp hfeas
  set S : Finset (Jobs P k) := (epochOf P k Z a).filter (fun x => kind P k x = 0) with hS
  set D : Finset (Jobs P k ⊕ Jobs P k) := (epochOf P k Z a).disjSum S with hD
  set f : Jobs P k ⊕ Jobs P k → ℕ × ℕ :=
    fun z => Sum.elim (fun x => (c x, if kind P k x = 2 then 1 else 0))
      (fun x => (c x, 1)) z with hf
  have hfl : ∀ x : Jobs P k, f (Sum.inl x) = (c x, if kind P k x = 2 then 1 else 0) :=
    fun _ => rfl
  have hfr : ∀ x : Jobs P k, f (Sum.inr x) = (c x, 1) := fun _ => rfl
  -- both parts land in `machines × {0,1}`
  have hmem : ∀ z ∈ D, z.elim id id ∈ epochOf P k Z a := by
    intro z hz
    rcases Finset.mem_disjSum.mp hz with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact hx
    · exact (Finset.mem_filter.mp hx).1
  have hmaps : ∀ z ∈ D, f z ∈ Finset.range k ×ˢ Finset.range 2 := by
    intro z hz
    have hx := hmem z hz
    have hZ : z.elim id id ∈ Z := (Finset.mem_filter.mp hx).1
    have hc : c (z.elim id id) < k := hlt _ hZ
    rcases z with x | x
    · rw [hfl]
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hc,
        Finset.mem_range.mpr (by split <;> omega)⟩
    · rw [hfr]
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hc, Finset.mem_range.mpr one_lt_two⟩
  -- and the map is injective, because a collision would be two conflicting jobs sharing
  -- a machine
  have hclash : ∀ x ∈ epochOf P k Z a, ∀ y ∈ epochOf P k Z a, x ≠ y → c x = c y →
      (kind P k x = 2 ∧ kind P k y = 1) ∨ (kind P k y = 2 ∧ kind P k x = 1) := by
    intro x hx y hy hxy hc
    by_contra hcon
    obtain ⟨hxZ, hxe⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyZ, hye⟩ := Finset.mem_filter.mp hy
    refine hindep x hxZ y hyZ hxy hc
      (conflict_of_same_epoch P k hk (hxe.trans hye.symm) ?_ ?_)
    · exact fun h => hcon (Or.inl h)
    · exact fun h => hcon (Or.inr h)
  have hSmem : ∀ y : Jobs P k, Sum.inr y ∈ D → kind P k y = 0 := by
    intro y hy
    rcases Finset.mem_disjSum.mp hy with ⟨u, -, hcon⟩ | ⟨u, hu, hcon⟩
    · exact absurd hcon (by simp)
    · rw [Sum.inr.injEq] at hcon
      subst hcon
      exact (Finset.mem_filter.mp hu).2
  have hinj : Set.InjOn f (D : Set (Jobs P k ⊕ Jobs P k)) := by
    intro z hz z' hz' heq
    simp only [Finset.mem_coe] at hz hz'
    have hze := hmem z hz
    have hz'e := hmem z' hz'
    rcases z with x | x <;> rcases z' with y | y <;>
      simp only [hfl, hfr, Prod.mk.injEq] at heq
    · -- both from the epoch
      by_cases hxy : x = y
      · rw [hxy]
      · exfalso
        rcases hclash x hze y hz'e hxy heq.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          · rw [h1, h2] at heq
            simp at heq
    · -- an epoch job against a duplicated selection job
      exfalso
      have hy0 : kind P k y = 0 := hSmem y hz'
      have hx2 : kind P k x = 2 := by
        by_contra hx2
        rw [if_neg hx2] at heq
        exact absurd heq.2 (by omega)
      have hxy : x ≠ y := fun h => by rw [h, hy0] at hx2; omega
      rcases hclash x hze y hz'e hxy heq.1 with ⟨-, h2⟩ | ⟨h1, -⟩ <;> omega
    · exfalso
      have hx0 : kind P k x = 0 := hSmem x hz
      have hy2 : kind P k y = 2 := by
        by_contra hy2
        rw [if_neg hy2] at heq
        exact absurd heq.2.symm (by omega)
      have hxy : x ≠ y := fun h => by rw [← h, hx0] at hy2; omega
      rcases hclash x hze y hz'e hxy heq.1 with ⟨h1, -⟩ | ⟨-, h2⟩ <;> omega
    · -- two duplicated selection jobs
      by_cases hxy : x = y
      · rw [hxy]
      · exfalso
        have hx0 : kind P k x = 0 := hSmem x hz
        have hy0 : kind P k y = 0 := hSmem y hz'
        rcases hclash x hze y hz'e hxy heq.1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [hD, Finset.card_disjSum] at hcard
  simpa [Finset.card_product, selCount, hS, Nat.mul_comm] using hcard

/-! ## 9. Lemma 8

Summing `epoch_capacity` over the `R·m` epochs and feeding in Lemma 7 pins everything
down. Writing `S` and `D` for the total numbers of selection jobs and dummies, and
`N = R·m`:

* the capacity gives `(S + D) + S ≤ 2kN`,
* the hypothesis gives `N(2k−1) ≤ S + D`,
* Lemma 7 gives `D ≤ 2(k−1)N`,

and those three force `S = N` and `D = 2(k−1)N` exactly. `lemma7_exact` then makes each
epoch's dummy count exactly `2(k−1)`, the capacity makes each epoch's selection count at
most `1`, and `S = N` over `N` epochs makes it exactly `1`. -/

/-- Every job lives in one of the `R·m` epochs. -/
lemma epochIdx_lt (x : Jobs P k) : epochIdx P k x < R P k * P.m := by
  rcases x with u | u | u <;>
    · obtain ⟨r, j, i⟩ := u
      have h1 : r.val + 1 ≤ R P k := r.isLt
      have h2 : j.val < P.m := j.isLt
      have h3 : (r.val + 1) * P.m ≤ R P k * P.m := Nat.mul_le_mul_right _ h1
      simp only [Nat.add_mul, one_mul] at h3
      simp only [epochIdx, gp]
      omega

/-- **Lemma 8.** A feasible set of the target size holds exactly one selection job and
exactly `2(k−1)` dummy jobs in every epoch. -/
theorem lemma8 (hk : 2 ≤ k) {Z : Finset (Jobs P k)} (hfeas : (inst P k).Feasible Z)
    (hcard : targetSize P k ≤ Z.card) {a : ℕ} (ha : a < R P k * P.m) :
    selCount P k Z a = 1 ∧ dumCount P k Z a = 2 * (k - 1) := by
  set N := R P k * P.m with hN
  set S := ∑ b ∈ Finset.range N, selCount P k Z b with hS
  set D := ∑ b ∈ Finset.range N, dumCount P k Z b with hD
  have hZ : Z.card = ∑ b ∈ Finset.range N, (epochOf P k Z b).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => Finset.mem_range.mpr (epochIdx_lt P k x)
  have hsplit : ∑ b ∈ Finset.range N, (epochOf P k Z b).card = S + D := by
    rw [hS, hD, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => (selCount_add_dumCount P k Z b).symm
  have hcap : (S + D) + S ≤ N * (2 * k) := by
    have hsum : ∑ b ∈ Finset.range N, ((epochOf P k Z b).card + selCount P k Z b)
        ≤ N * (2 * k) := by
      calc ∑ b ∈ Finset.range N, ((epochOf P k Z b).card + selCount P k Z b)
          ≤ ∑ _b ∈ Finset.range N, 2 * k :=
            Finset.sum_le_sum fun b _ => epoch_capacity P k hk hfeas b
        _ = N * (2 * k) := by
            rw [Finset.sum_const_nat (m := 2 * k) fun _ _ => rfl, Finset.card_range]
    rw [Finset.sum_add_distrib, hsplit] at hsum
    exact hsum
  have hL7 : D ≤ 2 * (k - 1) * N := lemma7 P k hfeas N
  -- the three inequalities pin `S` and `D` exactly
  have b1 : N * (2 * k) = N * (2 * k - 1) + N := by
    have h : 2 * k - 1 + 1 = 2 * k := by omega
    calc N * (2 * k) = N * (2 * k - 1 + 1) := by rw [h]
      _ = N * (2 * k - 1) + N := by ring
  have b2 : 2 * (k - 1) * N + N = N * (2 * k - 1) := by
    have h : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
    calc 2 * (k - 1) * N + N = (2 * (k - 1) + 1) * N := by ring
      _ = (2 * k - 1) * N := by rw [h]
      _ = N * (2 * k - 1) := by ring
  have htarget : targetSize P k = N * (2 * k - 1) := rfl
  rw [htarget, hZ, hsplit] at hcard
  have hDeq : D = 2 * (k - 1) * N := by omega
  have hSeq : S = N := by omega
  -- each epoch's dummy count, then each epoch's selection count
  have hdum : ∀ b, b < N → dumCount P k Z b = 2 * (k - 1) := fun b hb =>
    lemma7_exact P k hfeas hDeq hb
  have hsel_le : ∀ b, b < N → selCount P k Z b ≤ 1 := by
    intro b hb
    have h1 := epoch_capacity P k hk hfeas b
    have h2 := selCount_add_dumCount P k Z b
    have h3 := hdum b hb
    have h4 : 2 * (k - 1) + 2 = 2 * k := by omega
    omega
  have hsel : ∀ b, b < N → selCount P k Z b = 1 := by
    intro b hb
    by_contra hcon
    have h0 : selCount P k Z b = 0 := by have := hsel_le b hb; omega
    have hlt : S < N := by
      rw [hS]
      calc ∑ c ∈ Finset.range N, selCount P k Z c
          < ∑ _c ∈ Finset.range N, 1 :=
            Finset.sum_lt_sum (fun c hc => hsel_le c (Finset.mem_range.mp hc))
              ⟨b, Finset.mem_range.mpr hb, by omega⟩
        _ = N := by
            rw [Finset.sum_const_nat (m := 1) fun _ _ => rfl, Finset.card_range, Nat.mul_one]
    omega
  exact ⟨hsel a ha, hdum a ha⟩

/-! ## 10. Toward Lemma 9: the load of a segment

Lemma 9 extracts the hitting set. Its engine is a *load* computation: whichever way an
epoch's machine is filled — one selection job, or an `A` and a `B` — that machine is busy
for exactly `(2g+1)·Q` during the epoch (`jq_sel_eq`, `jq_dum_add_eq`). Summing over the
`m` epochs of a segment telescopes to the difference of two squares
(`segment_load`), which is exactly the distance from `G(r,1)` to `G(r+1,1)`.

That is what forbids a machine from ever moving *backwards*: a machine that starts segment
`r`'s work at offset `i` finishes it no earlier than `G(r+1,1) + i`, so its offset in
segment `r+1` is at least `i`. With offsets confined to `{1, …, n}` a machine can therefore
change its choice at most `n − 1` times, and with `R = k(n−1)+1` segments and `k` machines
some segment must repeat every machine's choice — the pigeonhole that produces the hitting
set.

**Only the load identities below are formalized.** The monotonicity argument, the
pigeonhole, and the extraction are not. -/

/-! ## 11. The pigeonhole, and why the paper's `R` is one too small

With `k` machines whose offsets are non-decreasing and confined to `{1, …, n}`, each
machine changes its choice at most `n − 1` times, so at most `k(n−1)` of the gaps between
consecutive segments see any change at all. A *stable* gap therefore exists as soon as
there are **more** than `k(n−1)` gaps, i.e. as soon as `R − 1 > k(n−1)`.

The paper sets `R = k(n−1) + 1`, giving exactly `R − 1 = k(n−1)` gaps — one too few, and
the pigeonhole does not close. It is not a slack bound either: with machine `1` increasing
across gaps `0 … n−2`, machine `2` across gaps `n−1 … 2n−3`, and so on, all `k(n−1)` gaps
are used up and no segment repeats. `Theorem1.R` is therefore defined as `k(n−1) + 2` here.
Nothing else changes — every result about the construction is generic in `R`.

`exists_stable_gap` is the pigeonhole itself, stated for an arbitrary offset function so
that the counting is separated from the scheduling. It is proved by tracking the sum of
the `k` offsets: that sum starts at `≥ k`, ends at `≤ kn`, and would have to strictly
increase at every one of the `R − 1` gaps. -/

/-- **The pigeonhole.** Non-decreasing offsets in `{1, …, n}` on `k` machines over
`R ≥ k(n−1) + 2` segments leave some gap at which no machine changes. -/
lemma exists_stable_gap {n k R : ℕ} (f : ℕ → ℕ → ℕ) (hR : k * (n - 1) + 2 ≤ R)
    (hmono : ∀ r c, r + 1 < R → c < k → f r c ≤ f (r + 1) c)
    (hlo : ∀ r c, r < R → c < k → 1 ≤ f r c)
    (hhi : ∀ r c, r < R → c < k → f r c ≤ n) :
    ∃ r, r + 1 < R ∧ ∀ c, c < k → f r c = f (r + 1) c := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, by omega, fun c hc => absurd hc (by omega)⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (hlo 0 0 (by omega) hk) (by have := hhi 0 0 (by omega) hk; omega)
  by_contra hcon
  have hbad : ∀ r, r + 1 < R → ∃ c, c < k ∧ f r c ≠ f (r + 1) c := by
    intro r hr
    by_contra h2
    exact hcon ⟨r, hr, fun c hc => by
      by_contra h3
      exact h2 ⟨c, hc, h3⟩⟩
  set T : ℕ → ℕ := fun r => ∑ c ∈ Finset.range k, f r c with hT
  have hstep : ∀ r, r + 1 < R → T r + 1 ≤ T (r + 1) := by
    intro r hr
    obtain ⟨c, hc, hne⟩ := hbad r hr
    have hlt : T r < T (r + 1) :=
      Finset.sum_lt_sum (fun c' hc' => hmono r c' hr (Finset.mem_range.mp hc'))
        ⟨c, Finset.mem_range.mpr hc, lt_of_le_of_ne (hmono r c hr hc) hne⟩
    omega
  have hgrow : ∀ j, j + 1 ≤ R → T 0 + j ≤ T j := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ J ih =>
        intro hJ
        have h1 := ih (by omega)
        have h2 := hstep J (by omega)
        omega
  have hT0 : k ≤ T 0 := by
    calc k = ∑ _c ∈ Finset.range k, 1 := by
          rw [Finset.sum_const_nat (m := 1) fun _ _ => rfl, Finset.card_range, Nat.mul_one]
      _ ≤ T 0 := Finset.sum_le_sum fun c hc => hlo 0 c (by omega) (Finset.mem_range.mp hc)
  have hTR : T (R - 1) ≤ k * n := by
    calc T (R - 1) ≤ ∑ _c ∈ Finset.range k, n :=
          Finset.sum_le_sum fun c hc => hhi (R - 1) c (by omega) (Finset.mem_range.mp hc)
      _ = k * n := by rw [Finset.sum_const_nat (m := n) fun _ _ => rfl, Finset.card_range]
  have hfin := hgrow (R - 1) (by omega)
  have hbridge : k * (n - 1) + k = k * n := by
    have h : n - 1 + 1 = n := by omega
    calc k * (n - 1) + k = k * (n - 1 + 1) := by ring
      _ = k * n := by rw [h]
  omega

/-! ## 12. Offsets never decrease along a machine

The paper derives this from the segment-load computation of §10: a machine that begins
segment `r`'s work at offset `i` is busy for exactly `G(r+1,1) − G(r,1)` and so cannot
finish before `G(r+1,1) + i`. The same conclusion follows *directly* from the windows, one
epoch at a time, and that is what is proved here.

A job that is not an `A` — a selection job or a `B` — is due at `(a+2)²Q + off`, the very
end of its epoch. A job that is not a `B` — a selection job or an `A` — starts at
`(a+1)²Q + off`, the very beginning. So if such a pair sits on one machine in consecutive
epochs, the earlier one is due at `(a+2)²Q + off x` and the later starts at `(a+2)²Q + off y`,
and not conflicting forces `off x ≤ off y` outright. Every other pairing is impossible: an
epoch-`a` job always starts before an epoch-`(a+1)` job is due, because the gap between the
two epochs' midpoints is `2(a+2)Q`, far more than any offset. -/

lemma sN_le_epoch_mid (x : Jobs P k) :
    sN P k x ≤ (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k + off P k x := by
  rw [sN_eq]
  have hid : (epochIdx P k x + 1) ^ 2 * Q P k + (epochIdx P k x + 1) * Q P k
      = (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k := by ring
  have hle : (epochIdx P k x + 1) ^ 2 * Q P k
      ≤ (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k := by
    refine Nat.mul_le_mul_right _ ?_
    have h : (epochIdx P k x + 1) ^ 2 = (epochIdx P k x + 1) * (epochIdx P k x + 1) := by ring
    rw [h]
    exact Nat.mul_le_mul_left _ (by omega)
  split <;> omega

lemma jd_ge_epoch_mid (x : Jobs P k) :
    (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k + off P k x ≤ jd P k x := by
  rw [jd_eq]
  have hid : (epochIdx P k x + 1) ^ 2 * Q P k + (epochIdx P k x + 1) * Q P k
      = (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k := by ring
  have hle : (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k
      ≤ (epochIdx P k x + 1) ^ 2 * Q P k + (2 * (epochIdx P k x + 1) + 1) * Q P k := by
    have h : (epochIdx P k x + 1) ^ 2 * Q P k + (2 * (epochIdx P k x + 1) + 1) * Q P k
        = (epochIdx P k x + 2) * (epochIdx P k x + 2) * Q P k := by ring
    rw [h]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  split <;> omega

/-- A selection job or a `B` is due at the very end of its epoch. -/
lemma jd_eq_end {x : Jobs P k} (h : kind P k x ≠ 1) :
    jd P k x = (epochIdx P k x + 2) ^ 2 * Q P k + off P k x := by
  rw [jd_eq, if_neg h]
  have hid : (epochIdx P k x + 1) ^ 2 * Q P k + (2 * (epochIdx P k x + 1) + 1) * Q P k
      = (epochIdx P k x + 2) ^ 2 * Q P k := by ring
  omega

/-- A selection job or an `A` starts at the very beginning of its epoch. -/
lemma sN_eq_start {x : Jobs P k} (h : kind P k x ≠ 2) :
    sN P k x = (epochIdx P k x + 1) ^ 2 * Q P k + off P k x := by
  rw [sN_eq, if_neg h, Nat.add_zero]

/-- **Offsets never decrease along a machine.** -/
lemma off_le_of_succ_epoch (hk : 2 ≤ k) {Z : Finset (Jobs P k)} {c : Jobs P k → ℕ}
    (hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j)
    {x y : Jobs P k} (hx : x ∈ Z) (hy : y ∈ Z)
    (hxk : kind P k x ≠ 1) (hyk : kind P k y ≠ 2)
    (hsucc : epochIdx P k y = epochIdx P k x + 1) (hmach : c x = c y) :
    off P k x ≤ off P k y := by
  have hxy : x ≠ y := fun h => by rw [h] at hsucc; omega
  have hnc := hindep x hx y hy hxy hmach
  -- the earlier job always starts before the later one is due
  have h1 : sN P k x < jd P k y := by
    have ha := sN_le_epoch_mid P k x
    have hb := jd_ge_epoch_mid P k y
    have hoff := off_lt_Q P k hk x
    rw [hsucc] at hb
    have hid : (epochIdx P k x + 1 + 1) * (epochIdx P k x + 1 + 2) * Q P k
        = (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k
          + 2 * (epochIdx P k x + 2) * Q P k := by ring
    have hQle : Q P k ≤ 2 * (epochIdx P k x + 2) * Q P k :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- so not conflicting forces the earlier to be due before the later starts
  have h2 : jd P k x ≤ sN P k y := by
    by_contra h3
    have h3' : sN P k y < jd P k x := by omega
    refine hnc ⟨?_, ?_⟩
    · rw [s_eq_sN]; exact_mod_cast h1
    · rw [s_eq_sN]; exact_mod_cast h3'
  rw [jd_eq_end P k hxk, sN_eq_start P k hyk, hsucc] at h2
  have hb2 : (epochIdx P k x + 1 + 1) ^ 2 * Q P k
      = (epochIdx P k x + 2) ^ 2 * Q P k := by ring
  omega

/-! ## 13. Inside one epoch, the opener comes before the closer

`off_le_of_succ_epoch` chains a machine's *last* job in an epoch to its *first* in the
next. To turn that into monotonicity of a single quantity, one more step is needed: on a
machine, within one epoch, the job that opens (a selection job or an `A`) has offset at
most the job that closes (a selection job or a `B`).

There are only three ways that can happen, and two of them are degenerate: if the two jobs
are the same job it is trivial, and if they are a selection job paired with a dummy they
conflict, so they cannot be on one machine at all. The real case is an `A` with a `B`, and
there the two are due and start at the same epoch midpoint `(a+1)(a+2)Q`, shifted by their
offsets — so not conflicting is precisely `off A ≤ off B`. -/

/-- An `A` is due at its epoch's midpoint. -/
lemma jd_eq_mid {x : Jobs P k} (h : kind P k x = 1) :
    jd P k x = (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k + off P k x := by
  rw [jd_eq, if_pos h]
  have hid : (epochIdx P k x + 1) ^ 2 * Q P k + (epochIdx P k x + 1) * Q P k
      = (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k := by ring
  omega

/-- A `B` starts at its epoch's midpoint. -/
lemma sN_eq_mid {x : Jobs P k} (h : kind P k x = 2) :
    sN P k x = (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k + off P k x := by
  rw [sN_eq, if_pos h]
  have hid : (epochIdx P k x + 1) ^ 2 * Q P k + (epochIdx P k x + 1) * Q P k
      = (epochIdx P k x + 1) * (epochIdx P k x + 2) * Q P k := by ring
  omega

/-- **Within one epoch, a machine's opener has the smaller offset.** -/
lemma off_le_within_epoch (hk : 2 ≤ k) {Z : Finset (Jobs P k)} {c : Jobs P k → ℕ}
    (hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j)
    {x y : Jobs P k} (hx : x ∈ Z) (hy : y ∈ Z) (hxk : kind P k x ≠ 2)
    (he : epochIdx P k x = epochIdx P k y) (hmach : c x = c y) :
    off P k x ≤ off P k y := by
  by_cases hxy : x = y
  · rw [hxy]
  have hnc := hindep x hx y hy hxy hmach
  -- the only pair that can share a machine is an `A` with a `B`
  have hcase : kind P k y = 2 ∧ kind P k x = 1 := by
    by_contra hcon
    exact hnc (conflict_of_same_epoch P k hk he (fun h => hxk h.1) fun h => hcon ⟨h.1, h.2⟩)
  obtain ⟨hy2, hx1⟩ := hcase
  -- and there, not conflicting is exactly `off x ≤ off y`
  have h1 : sN P k x < jd P k y :=
    sN_lt_jd P k hk he (fun h => absurd h.1 (by omega))
  have h2 : jd P k x ≤ sN P k y := by
    by_contra h3
    have h3' : sN P k y < jd P k x := by omega
    refine hnc ⟨?_, ?_⟩
    · rw [s_eq_sN]; exact_mod_cast h1
    · rw [s_eq_sN]; exact_mod_cast h3'
  rw [jd_eq_mid P k hx1, sN_eq_mid P k hy2, he] at h2
  omega

/-! ## 14. Every machine opens and closes every epoch

The last structural fact Lemma 9 needs: in each epoch, *each* machine carries a job that
starts at the epoch's beginning (an "opener": a selection job or an `A`) and one that is
due at its end (a "closer": a selection job or a `B`). Lemma 8 counts jobs per epoch; this
refines the count to per machine.

The route avoids re-deriving the distribution job by job. Openers pairwise conflict, so
they sit on distinct machines and there are at most `k` of them; likewise closers. And
`|openers| + |closers| = |epoch| + selCount` — because openers and closers cover the epoch
and meet exactly in its selection jobs — which Lemma 8 evaluates to `(2k−1) + 1 = 2k`. Two
numbers each at most `k` summing to `2k` are both exactly `k`, so each family already
covers every machine. -/

/-- The jobs of an epoch that start at its beginning: selection jobs and `A`s. -/
def openers (Z : Finset (Jobs P k)) (a : ℕ) : Finset (Jobs P k) :=
  (epochOf P k Z a).filter (fun x => kind P k x ≠ 2)

/-- The jobs of an epoch that are due at its end: selection jobs and `B`s. -/
def closers (Z : Finset (Jobs P k)) (a : ℕ) : Finset (Jobs P k) :=
  (epochOf P k Z a).filter (fun x => kind P k x ≠ 1)

lemma kind_lt_three (x : Jobs P k) : kind P k x < 3 := by
  rcases x with u | u | u <;> simp [kind]

/-- Openers and closers cover the epoch and meet in its selection jobs. -/
lemma card_openers_add_card_closers (Z : Finset (Jobs P k)) (a : ℕ) :
    (openers P k Z a).card + (closers P k Z a).card
      = (epochOf P k Z a).card + selCount P k Z a := by
  classical
  have hunion : openers P k Z a ∪ closers P k Z a = epochOf P k Z a := by
    ext x
    simp only [openers, closers, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      have := kind_lt_three P k x
      by_cases h2 : kind P k x = 2
      · exact Or.inr ⟨h, by omega⟩
      · exact Or.inl ⟨h, h2⟩
  have hinter : openers P k Z a ∩ closers P k Z a
      = (epochOf P k Z a).filter (fun x => kind P k x = 0) := by
    ext x
    simp only [openers, closers, Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, h2⟩, ⟨-, h1⟩⟩
      have := kind_lt_three P k x
      exact ⟨h, by omega⟩
    · rintro ⟨h, h0⟩
      exact ⟨⟨h, by omega⟩, ⟨h, by omega⟩⟩
  have h := Finset.card_union_add_card_inter (openers P k Z a) (closers P k Z a)
  rw [hunion, hinter] at h
  rw [selCount]
  omega

/-- Openers sit on distinct machines. -/
lemma openers_injOn {Z : Finset (Jobs P k)} {c : Jobs P k → ℕ} (hk : 2 ≤ k)
    (hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j)
    (a : ℕ) : Set.InjOn c (openers P k Z a : Set (Jobs P k)) := by
  intro x hx y hy heq
  simp only [Finset.mem_coe, openers, epochOf, Finset.mem_filter] at hx hy
  obtain ⟨⟨hxZ, hxe⟩, hxk⟩ := hx
  obtain ⟨⟨hyZ, hye⟩, hyk⟩ := hy
  by_contra hxy
  exact hindep x hxZ y hyZ hxy heq
    (conflict_of_same_epoch P k hk (hxe.trans hye.symm) (fun h => hxk h.1) fun h => hyk h.1)

/-- Closers likewise. -/
lemma closers_injOn {Z : Finset (Jobs P k)} {c : Jobs P k → ℕ} (hk : 2 ≤ k)
    (hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j)
    (a : ℕ) : Set.InjOn c (closers P k Z a : Set (Jobs P k)) := by
  intro x hx y hy heq
  simp only [Finset.mem_coe, closers, epochOf, Finset.mem_filter] at hx hy
  obtain ⟨⟨hxZ, hxe⟩, hxk⟩ := hx
  obtain ⟨⟨hyZ, hye⟩, hyk⟩ := hy
  by_contra hxy
  exact hindep x hxZ y hyZ hxy heq
    (conflict_of_same_epoch P k hk (hxe.trans hye.symm) (fun h => hyk h.2) fun h => hxk h.2)

private lemma mem_openers_mem_Z {Z : Finset (Jobs P k)} {a : ℕ} {x : Jobs P k}
    (hx : x ∈ openers P k Z a) : x ∈ Z :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1

private lemma mem_closers_mem_Z {Z : Finset (Jobs P k)} {a : ℕ} {x : Jobs P k}
    (hx : x ∈ closers P k Z a) : x ∈ Z :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1

lemma card_openers_le {Z : Finset (Jobs P k)} {c : Jobs P k → ℕ} (hk : 2 ≤ k)
    (hlt : ∀ j ∈ Z, c j < k)
    (hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j)
    (a : ℕ) : (openers P k Z a).card ≤ k := by
  have hmain : (openers P k Z a).card ≤ (Finset.range k).card :=
    Finset.card_le_card_of_injOn c
      (fun x hx => Finset.mem_range.mpr (hlt x (mem_openers_mem_Z P k hx)))
      (openers_injOn P k hk hindep a)
  simpa using hmain

lemma card_closers_le {Z : Finset (Jobs P k)} {c : Jobs P k → ℕ} (hk : 2 ≤ k)
    (hlt : ∀ j ∈ Z, c j < k)
    (hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j)
    (a : ℕ) : (closers P k Z a).card ≤ k := by
  have hmain : (closers P k Z a).card ≤ (Finset.range k).card :=
    Finset.card_le_card_of_injOn c
      (fun x hx => Finset.mem_range.mpr (hlt x (mem_closers_mem_Z P k hx)))
      (closers_injOn P k hk hindep a)
  simpa using hmain

/-- **Every machine opens every epoch, and closes it.** The two families each have exactly
`k` members on `k` distinct machines, so each covers all of them. -/
theorem exists_opener_closer (hk : 2 ≤ k) {Z : Finset (Jobs P k)}
    (hfeas : (inst P k).Feasible Z) (hcard : targetSize P k ≤ Z.card)
    {c : Jobs P k → ℕ} (hlt : ∀ j ∈ Z, c j < k)
    (hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j)
    {a : ℕ} (ha : a < R P k * P.m) {μ : ℕ} (hμ : μ < k) :
    (∃ x ∈ openers P k Z a, c x = μ) ∧ (∃ y ∈ closers P k Z a, c y = μ) := by
  obtain ⟨hsel, hdum⟩ := lemma8 P k hk hfeas hcard ha
  have hsize : (epochOf P k Z a).card = 2 * k - 1 := by
    have h := selCount_add_dumCount P k Z a
    omega
  have hsum := card_openers_add_card_closers P k Z a
  have hop := card_openers_le P k hk hlt hindep a
  have hcl := card_closers_le P k hk hlt hindep a
  -- two numbers at most `k` summing to `2k` are both `k`
  have hopk : (openers P k Z a).card = k := by omega
  have hclk : (closers P k Z a).card = k := by omega
  constructor
  · have himg : (openers P k Z a).image c = Finset.range k := by
      refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_range.mpr (hlt x (mem_openers_mem_Z P k hx))
      · rw [Finset.card_range,
          Finset.card_image_of_injOn (openers_injOn P k hk hindep a), hopk]
    obtain ⟨x, hx, hcx⟩ := Finset.mem_image.mp
      (himg ▸ Finset.mem_range.mpr hμ : μ ∈ (openers P k Z a).image c)
    exact ⟨x, hx, hcx⟩
  · have himg : (closers P k Z a).image c = Finset.range k := by
      refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_range.mpr (hlt x (mem_closers_mem_Z P k hx))
      · rw [Finset.card_range,
          Finset.card_image_of_injOn (closers_injOn P k hk hindep a), hclk]
    obtain ⟨y, hy, hcy⟩ := Finset.mem_image.mp
      (himg ▸ Finset.mem_range.mpr hμ : μ ∈ (closers P k Z a).image c)
    exact ⟨y, hy, hcy⟩

/-! ## 15. The offset of a machine in an epoch

`exists_opener_closer` gives each machine an opener and a closer in every epoch, and
`openers_injOn` says the opener is unique. `openerOff` names its offset — as a `Finset.sup`
over the (singleton) fibre rather than by choice, so it is a total function with no
proof arguments. `openerOff_eq` is the only thing ever used about it: it *is* the offset of
any opener on that machine.

Chaining `off_le_within_epoch` (opener before closer, same epoch) with
`off_le_of_succ_epoch` (closer before next opener) makes `openerOff` non-decreasing in the
epoch — which is the hypothesis `exists_stable_gap` wants. -/

/-- The offset of the job on machine `μ` that opens epoch `a`. -/
def openerOff (Z : Finset (Jobs P k)) (c : Jobs P k → ℕ) (a μ : ℕ) : ℕ :=
  ((openers P k Z a).filter (fun x => c x = μ)).sup (off P k)

/-- The offset of the job on machine `μ` that closes epoch `a`. -/
def closerOff (Z : Finset (Jobs P k)) (c : Jobs P k → ℕ) (a μ : ℕ) : ℕ :=
  ((closers P k Z a).filter (fun x => c x = μ)).sup (off P k)

lemma mem_openers_epoch {Z : Finset (Jobs P k)} {a : ℕ} {x : Jobs P k}
    (hx : x ∈ openers P k Z a) : epochIdx P k x = a :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2

lemma mem_closers_epoch {Z : Finset (Jobs P k)} {a : ℕ} {x : Jobs P k}
    (hx : x ∈ closers P k Z a) : epochIdx P k x = a :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2

lemma openerOff_eq {Z : Finset (Jobs P k)} {c : Jobs P k → ℕ} (hk : 2 ≤ k)
    (hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j)
    {a μ : ℕ} {x : Jobs P k} (hx : x ∈ openers P k Z a) (hcx : c x = μ) :
    openerOff P k Z c a μ = off P k x := by
  refine le_antisymm (Finset.sup_le fun y hy => ?_) (Finset.le_sup ?_)
  · obtain ⟨hy1, hy2⟩ := Finset.mem_filter.mp hy
    have : y = x := openers_injOn P k hk hindep a (by simpa using hy1) (by simpa using hx)
      (by rw [hy2, hcx])
    rw [this]
  · exact Finset.mem_filter.mpr ⟨hx, hcx⟩

lemma closerOff_eq {Z : Finset (Jobs P k)} {c : Jobs P k → ℕ} (hk : 2 ≤ k)
    (hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j)
    {a μ : ℕ} {y : Jobs P k} (hy : y ∈ closers P k Z a) (hcy : c y = μ) :
    closerOff P k Z c a μ = off P k y := by
  refine le_antisymm (Finset.sup_le fun z hz => ?_) (Finset.le_sup ?_)
  · obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
    have : z = y := closers_injOn P k hk hindep a (by simpa using hz1) (by simpa using hy)
      (by rw [hz2, hcy])
    rw [this]
  · exact Finset.mem_filter.mpr ⟨hy, hcy⟩

variable {P k}

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- Bundling what the scheduling side supplies, so the long argument below reads. -/
structure Setup (Z : Finset (Jobs P k)) where
  /-- At least two machines — the construction is wrong below that. -/
  hk : 2 ≤ k
  /-- The set is feasible. -/
  hfeas : (inst P k).Feasible Z
  /-- ... and of the target size. -/
  hcard : targetSize P k ≤ Z.card
  /-- The machine assignment. -/
  c : Jobs P k → ℕ
  /-- It uses only the `k` machines available. -/
  hlt : ∀ j ∈ Z, c j < k
  /-- ... and never puts conflicting jobs together. -/
  hindep : ∀ i ∈ Z, ∀ j ∈ Z, i ≠ j → c i = c j → ¬ (inst P k).Conflict i j

namespace Setup

variable {Z : Finset (Jobs P k)} (S : Setup Z)

/-- Within an epoch, the opener's offset is at most the closer's. -/
lemma openerOff_le_closerOff {a : ℕ} (ha : a < R P k * P.m) {μ : ℕ} (hμ : μ < k) :
    openerOff P k Z S.c a μ ≤ closerOff P k Z S.c a μ := by
  obtain ⟨⟨x, hx, hcx⟩, ⟨y, hy, hcy⟩⟩ :=
    exists_opener_closer P k S.hk S.hfeas S.hcard S.hlt S.hindep ha hμ
  rw [openerOff_eq P k S.hk S.hindep hx hcx, closerOff_eq P k S.hk S.hindep hy hcy]
  exact off_le_within_epoch P k S.hk S.hindep (mem_openers_mem_Z P k hx)
    (mem_closers_mem_Z P k hy) (Finset.mem_filter.mp hx).2
    ((mem_openers_epoch P k hx).trans (mem_closers_epoch P k hy).symm) (by rw [hcx, hcy])

/-- Across an epoch boundary, the closer's offset is at most the next opener's. -/
lemma closerOff_le_openerOff_succ {a : ℕ} (ha : a + 1 < R P k * P.m) {μ : ℕ} (hμ : μ < k) :
    closerOff P k Z S.c a μ ≤ openerOff P k Z S.c (a + 1) μ := by
  obtain ⟨-, ⟨y, hy, hcy⟩⟩ :=
    exists_opener_closer P k S.hk S.hfeas S.hcard S.hlt S.hindep (by omega : a < R P k * P.m) hμ
  obtain ⟨⟨x, hx, hcx⟩, -⟩ :=
    exists_opener_closer P k S.hk S.hfeas S.hcard S.hlt S.hindep ha hμ
  rw [closerOff_eq P k S.hk S.hindep hy hcy, openerOff_eq P k S.hk S.hindep hx hcx]
  refine off_le_of_succ_epoch P k S.hk S.hindep (mem_closers_mem_Z P k hy)
    (mem_openers_mem_Z P k hx) (Finset.mem_filter.mp hy).2 (Finset.mem_filter.mp hx).2 ?_
    (by rw [hcy, hcx])
  rw [mem_openers_epoch P k hx, mem_closers_epoch P k hy]

/-- So the opener's offset never decreases from one epoch to the next. -/
lemma openerOff_mono_step {a : ℕ} (ha : a + 1 < R P k * P.m) {μ : ℕ} (hμ : μ < k) :
    openerOff P k Z S.c a μ ≤ openerOff P k Z S.c (a + 1) μ :=
  le_trans (S.openerOff_le_closerOff (by omega) hμ) (S.closerOff_le_openerOff_succ ha hμ)

end Setup

variable (P k)

/-! ## 16. A stable segment exists

Lifting `openerOff_mono_step` from one epoch to many makes the offset non-decreasing
across a whole segment, so `f r μ := openerOff (r·m) μ` is exactly the input
`exists_stable_gap` wants: non-decreasing in `r`, and confined to `{1, …, n}` because it is
the offset of an actual job. The gap it returns is a pair of consecutive segments across
which no machine changes — and monotonicity then squeezes every epoch in between, so the
offsets are constant throughout that segment. -/

lemma one_le_off (x : Jobs P k) : 1 ≤ off P k x := by
  rcases x with u | u | u <;> · obtain ⟨r, j, i⟩ := u; simp [off]

variable {P k}

namespace Setup

variable {Z : Finset (Jobs P k)} (S : Setup Z)

/-- The offset never decreases, however many epochs apart. -/
lemma openerOff_mono {μ : ℕ} (hμ : μ < k) :
    ∀ d a : ℕ, a + d < R P k * P.m →
      openerOff P k Z S.c a μ ≤ openerOff P k Z S.c (a + d) μ := by
  intro d
  induction d with
  | zero => intro a _; simp
  | succ D ih =>
      intro a ha
      have h1 : openerOff P k Z S.c a μ ≤ openerOff P k Z S.c (a + D) μ := ih a (by omega)
      have h2 := S.openerOff_mono_step (a := a + D) (by omega) hμ
      have he : a + (D + 1) = a + D + 1 := by omega
      rw [he]
      omega

/-- The offset of a machine really is the offset of a job, hence in `{1, …, n}`. -/
lemma one_le_openerOff {a : ℕ} (ha : a < R P k * P.m) {μ : ℕ} (hμ : μ < k) :
    1 ≤ openerOff P k Z S.c a μ := by
  obtain ⟨⟨x, hx, hcx⟩, -⟩ :=
    exists_opener_closer P k S.hk S.hfeas S.hcard S.hlt S.hindep ha hμ
  rw [openerOff_eq P k S.hk S.hindep hx hcx]
  exact one_le_off P k x

lemma openerOff_le_n {a : ℕ} (ha : a < R P k * P.m) {μ : ℕ} (hμ : μ < k) :
    openerOff P k Z S.c a μ ≤ P.n := by
  obtain ⟨⟨x, hx, hcx⟩, -⟩ :=
    exists_opener_closer P k S.hk S.hfeas S.hcard S.hlt S.hindep ha hμ
  rw [openerOff_eq P k S.hk S.hindep hx hcx]
  exact off_le P k x

/-- **Some segment is stable**: across all of its `m` epochs, no machine's offset moves. -/
theorem exists_stable_segment (hm : 0 < P.m) :
    ∃ r, r + 1 < R P k ∧ ∀ j, j < P.m → ∀ μ, μ < k →
      openerOff P k Z S.c (r * P.m + j) μ = openerOff P k Z S.c (r * P.m) μ := by
  have hbound : ∀ r, r < R P k → r * P.m < R P k * P.m := fun r hr =>
    (Nat.mul_lt_mul_right hm).mpr hr
  obtain ⟨r, hr, hstable⟩ :=
    exists_stable_gap (n := P.n) (k := k) (R := R P k)
      (fun r μ => openerOff P k Z S.c (r * P.m) μ) (by simp [R])
      (fun r μ hrR hμ => by
        have hlt : (r + 1) * P.m < R P k * P.m := hbound (r + 1) hrR
        have he : (r + 1) * P.m = r * P.m + P.m := by ring
        rw [he]
        exact S.openerOff_mono hμ P.m (r * P.m) (by omega))
      (fun r μ hrR hμ => S.one_le_openerOff (hbound r hrR) hμ)
      (fun r μ hrR hμ => S.openerOff_le_n (hbound r hrR) hμ)
  refine ⟨r, hr, fun j hj μ hμ => le_antisymm ?_ ?_⟩
  · -- squeezed from above by the next segment, which the gap says is equal
    have hup : openerOff P k Z S.c (r * P.m + j) μ
        ≤ openerOff P k Z S.c ((r + 1) * P.m) μ := by
      have he : (r + 1) * P.m = r * P.m + j + (P.m - j) := by
        have : (r + 1) * P.m = r * P.m + P.m := by ring
        omega
      rw [he]
      exact S.openerOff_mono hμ (P.m - j) (r * P.m + j) (by rw [← he]; exact hbound (r + 1) hr)
    rw [hstable μ hμ] at *
    exact hup
  · -- and from below by monotonicity within the segment
    exact S.openerOff_mono hμ j (r * P.m) (by
      have : (r + 1) * P.m = r * P.m + P.m := by ring
      have := hbound (r + 1) hr
      omega)

end Setup

variable (P k)

/-! ## 17. Lemma 9

The stable segment hands over the hitting set. In each of its `m` epochs Lemma 8 puts one
selection job; that job opens its epoch, so `openerOff_eq` says its offset is the machine's
offset, and stability says that value does not depend on which epoch of the segment we look
at. A selection job for `F j` exists only for elements of `F j`, so the `k` machine offsets
of the stable segment already hit every set. -/

variable {P k}

namespace Setup

variable {Z : Finset (Jobs P k)} (S : Setup Z)

/-- **Lemma 9.** A feasible set of the target size yields a hitting set of size `k`. -/
theorem lemma9 {Z : Finset (Jobs P k)} (S : Setup Z) (hkn : k ≤ P.n) :
    P.HasHittingSet k := by
  classical
  -- a set of `k` elements always exists, and enlarging a hitting set keeps it one
  have hpad : ∀ H : Finset (Fin P.n), H.card ≤ k →
      ∃ H' : Finset (Fin P.n), H ⊆ H' ∧ H'.card = k := by
    intro H hH
    have hsd : ((Finset.univ : Finset (Fin P.n)) \ H).card = P.n - H.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    obtain ⟨T, hT, hTc⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin P.n)) \ H)
        (n := k - H.card) (by omega)
    refine ⟨H ∪ T, Finset.subset_union_left, ?_⟩
    have hdis : Disjoint H T := Finset.disjoint_left.mpr fun a ha haT =>
      (Finset.mem_sdiff.mp (hT haT)).2 ha
    rw [Finset.card_union_of_disjoint hdis, hTc]
    omega
  rcases Nat.eq_zero_or_pos P.m with hm | hm
  · -- no sets to hit at all
    obtain ⟨H, hsub, hcard⟩ := hpad ∅ (by simp)
    exact ⟨H, hcard, fun j => absurd j.isLt (by omega)⟩
  obtain ⟨r, hr, hstable⟩ := S.exists_stable_segment hm
  have hrb : r * P.m < R P k * P.m := (Nat.mul_lt_mul_right hm).mpr (by omega)
  have hk0 : 0 < k := by have := S.hk; omega
  have hn : 0 < P.n := by
    have h1 := S.one_le_openerOff hrb (μ := 0) hk0
    have h2 := S.openerOff_le_n hrb (μ := 0) hk0
    omega
  -- the `k` machine offsets of the stable segment, as universe elements
  set elt : ℕ → Fin P.n := fun μ =>
    ⟨min (openerOff P k Z S.c (r * P.m) μ - 1) (P.n - 1),
      lt_of_le_of_lt (min_le_right _ _) (by omega)⟩ with helt
  refine hpad ((Finset.range k).image elt) (le_trans Finset.card_image_le (by simp)) |>.elim ?_
  rintro H ⟨hsub, hcard⟩
  refine ⟨H, hcard, fun j => ?_⟩
  -- the selection job of this epoch of the stable segment
  set a : ℕ := r * P.m + j.val with ha
  have hab : a < R P k * P.m := by
    have h1 : (r + 1) * P.m < R P k * P.m := (Nat.mul_lt_mul_right hm).mpr hr
    have h2 : (r + 1) * P.m = r * P.m + P.m := by ring
    have := j.isLt
    omega
  obtain ⟨hsel, -⟩ := lemma8 P k S.hk S.hfeas S.hcard hab
  obtain ⟨x, hx⟩ : ((epochOf P k Z a).filter (fun y => kind P k y = 0)).Nonempty :=
    Finset.card_pos.mp (by rw [← selCount]; omega)
  obtain ⟨hxe, hx0⟩ := Finset.mem_filter.mp hx
  have hxZ : x ∈ Z := (Finset.mem_filter.mp hxe).1
  have hxa : epochIdx P k x = a := (Finset.mem_filter.mp hxe).2
  have hxop : x ∈ openers P k Z a := Finset.mem_filter.mpr ⟨hxe, by omega⟩
  -- its offset is the machine's, and the segment is stable
  have hcx : S.c x < k := S.hlt x hxZ
  have hoff : off P k x = openerOff P k Z S.c (r * P.m) (S.c x) := by
    rw [← openerOff_eq P k S.hk S.hindep hxop rfl, ha, hstable j.val j.isLt (S.c x) hcx]
  -- and a selection job for `F j` exists only for elements of `F j`
  rcases x with u | u | u
  · obtain ⟨r₀, j₀, i⟩ := u
    have hgp : gp P r₀.val j₀ = gp P r j := by
      have : gp P r₀.val j₀ = a := hxa
      simp only [ha, gp] at this ⊢
      omega
    obtain ⟨-, hj⟩ := gp_inj P hgp
    subst hj
    refine ⟨i.val, ?_, i.2⟩
    have hval : off P k (Sum.inl (r₀, ⟨j₀, i⟩) : Jobs P k) = i.val.val + 1 := rfl
    have hlo := S.one_le_openerOff hrb hcx
    have hhi := S.openerOff_le_n hrb hcx
    refine hsub (Finset.mem_image.mpr ⟨S.c (Sum.inl (r₀, ⟨j₀, i⟩)), Finset.mem_range.mpr hcx, ?_⟩)
    have hiv : i.val.val < P.n := i.val.isLt
    rw [helt]
    apply Fin.ext
    simp only
    omega
  · simp [kind] at hx0
  · simp [kind] at hx0

end Setup

end Theorem1

end FlexFlowJIT

end Lax496464Proofs
