import Lax496464Proofs.Ram.Imp
import Lax496464.ParameterizedComplexity
import Lax808846.RamComputes

/-!
# From the concepts' word-length hypothesis to the pipeline's

A running-time statement of this submission admits a word length by two inequalities: the
`Fits c w x` of `ParameterizedComplexity`, which says that a constant times the length of
the word plus any entry of it is a word, and a second clause bounding whatever table the
algorithm allocates. The pipeline asks instead for `L.FitsWords (B x) w`: a single bound
`B x` on every value of the run, which must itself be a word and whose layout span must be
a word too.

`fitsWords_of_fits` is the translation, and it is the same for every algorithm here. The
bound is `‖x‖ + max x + 1` — room for the numbers the word carries and for any index into
it — plus `T x`, room for the table. The two admissibility clauses each give a word's worth
of room, so a constant with a factor two to spare buys their sum.
-/

namespace Lax496464Proofs.Ram.Fits

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax496464.ParameterizedComplexity

/-- The largest entry of a word. -/
def maxEntry (x : List ℕ) : ℕ := x.foldr max 0

theorem le_maxEntry {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ maxEntry x := by
  induction x with
  | nil => exact absurd h (List.not_mem_nil)
  | cons a l ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact Nat.le_max_left _ _
      · exact le_trans (ih h') (Nat.le_max_right _ _)

theorem maxEntry_mem {x : List ℕ} (h : x ≠ []) : maxEntry x ∈ x := by
  induction x with
  | nil => exact absurd rfl h
  | cons a l ih =>
      cases l with
      | nil => simp [maxEntry]
      | cons b l' =>
        have hne : (b :: l') ≠ [] := by simp
        rcases Nat.le_total a (maxEntry (b :: l')) with hle | hle
        · have heq : maxEntry (a :: b :: l') = maxEntry (b :: l') := by
            simp only [maxEntry, List.foldr_cons]
            exact Nat.max_eq_right hle
          rw [heq]
          exact List.mem_cons_of_mem _ (ih hne)
        · have heq : maxEntry (a :: b :: l') = a := by
            simp only [maxEntry, List.foldr_cons]
            exact Nat.max_eq_left hle
          rw [heq]
          exact List.mem_cons_self

/-- The bound on the values of a run: room for the word's own numbers and for any index
into it, plus room for the table the algorithm allocates. -/
def bound (x : List ℕ) (T : ℕ) : ℕ := x.length + maxEntry x + 1 + T

theorem lt_bound {x : List ℕ} {v T : ℕ} (h : v ∈ x) : v < bound x T := by
  have := le_maxEntry h
  simp only [bound]
  omega

/-- The constant a layout needs: two spans' worth, so that the two admissibility clauses
can be added. -/
def const (L : Layout) : ℕ := 2 * (L.temps + 2 + L.scalars.length + L.arrays.length)

/-- **The translation.** The two inequalities the concepts state about the word length are
exactly `L.FitsWords` at the bound above. -/
theorem fitsWords_of_fits {L : Layout} {w T : ℕ} {x : List ℕ} (hx : x ≠ [])
    (hfits : Fits (const L) w x) (hT : const L * T ≤ 2 ^ w) :
    L.FitsWords (bound x T) w := by
  set κ := L.temps + 2 + L.scalars.length + L.arrays.length with hκ
  have hκ1 : 1 ≤ κ := by omega
  have hmem := maxEntry_mem hx
  have hA := hfits (maxEntry x) hmem
  have hlen : 1 ≤ x.length := List.length_pos_iff.mpr hx
  -- both clauses are `2κ · _ ≤ 2 ^ w`, so each half fits in half a word
  have hhalf : ∀ a b : ℕ, 2 * κ * a ≤ 2 ^ w → 2 * κ * b ≤ 2 ^ w → κ * (a + b) ≤ 2 ^ w := by
    intro a b ha hb
    have : 2 * (κ * (a + b)) = 2 * κ * a + 2 * κ * b := by ring
    omega
  have hspan : κ * bound x T ≤ 2 ^ w := by
    refine hhalf _ _ ?_ hT
    simpa [const, hκ, bound] using hA
  refine ⟨?_, ?_, ?_⟩
  · simp only [bound]; omega
  · calc bound x T ≤ κ * bound x T := Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ 2 ^ w := hspan
  · refine le_trans ?_ hspan
    simp only [Layout.span, hκ, bound]
    have h1 : L.arrays.length * (x.length + maxEntry x + 1 + T)
        ≤ L.arrays.length * (x.length + maxEntry x + 1 + T) := le_rfl
    have h2 : 1 ≤ x.length + maxEntry x + 1 + T := by omega
    calc L.temps + 2 + L.scalars.length + L.arrays.length * (x.length + maxEntry x + 1 + T)
        ≤ (L.temps + 2 + L.scalars.length) * (x.length + maxEntry x + 1 + T)
            + L.arrays.length * (x.length + maxEntry x + 1 + T) := by
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (by omega)) _
      _ = (L.temps + 2 + L.scalars.length + L.arrays.length)
            * (x.length + maxEntry x + 1 + T) := by ring

/-! ## The end of every runtime proof -/

open Lax808846Proofs.Transfer Lax808846.Ram Lax808846.RamComputes

/-- **The shape every running-time statement of this submission ends in.** An IMP+ program
that solves the problem within cost `K`, with every value below `bound x (T x)`, compiles
to a machine program that decides it within `Tm`, at every word length the concept's two
admissibility clauses admit. -/
theorem computesInTime_of_solves_fits {L : Layout} {c : Com} {D : Set (List ℕ)}
    {f : List ℕ → List ℕ} {T K Tm : List ℕ → ℕ} {w : ℕ}
    (hne : ∀ x ∈ D, x ≠ [])
    (hfits : ∀ x ∈ D, Fits (const L) w x)
    (hTab : ∀ x ∈ D, const L * T x ≤ 2 ^ w)
    (hsolves : Solves L c D f (fun x => bound x (T x)) K)
    (hT : ∀ x ∈ D, L.const * K x + 1 ≤ Tm x) :
    ComputesInTime w (compileProgram L c) D f Tm :=
  computesInTime_of_solves hsolves
    (fun x hx => fitsWords_of_fits (hne x hx) (hfits x hx) (hTab x hx)) hT

end Lax496464Proofs.Ram.Fits
