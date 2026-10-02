import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
import Lax496464.WH_C3_WeightedSat

/-! # The formula the reduction writes

The fixed data of the reduction (`Data`): the arity `s` of `X`, the number `r` of bound variables, the
CNF of the quantifier-free part (atoms on positions `0, …, r-1`), the relation atoms `(i, arity)` to be
checked against the vocabulary, and whether every `X`-atom has arity `s`.

With `U = UW s r x` (`n` elements), the propositional variable `c < n^s` stands for the tuple of
elements of `U` at the positions given by the base-`n` digits of `c`. For every `z < n^r` (an
assignment of elements of `U` to the variables, by the digits of `z`) and every clause `C`: if a
literal of `C` without `X` holds, the clause `Y₀ ∨ ¬Y₀` is written, else the clause of the
`X`-literals of `C`, each `(¬)X ȳ` as `(¬)Y_c` for the code `c` of the positions of `ȳ`. Then the
clauses `Y_c ∨ ¬Y_c` for all `c < n^s`, so that the variables are exactly `0, …, n^s - 1`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The fixed data of the reduction. -/
structure Data where
  /-- The arity of `X`. -/
  s : ℕ
  /-- The number of bound variables. -/
  r : ℕ
  /-- The CNF of the quantifier-free part. -/
  cnf : List (List Lit)
  /-- The relation atoms, as symbol and number of arguments. -/
  rels : List (ℕ × ℕ)
  /-- Every `X`-atom has arity `s`. -/
  sfit : Bool

/-- The literal is an `X`-literal. -/
def isXLit (l : Lit) : Bool :=
  match l.atom with
  | .setVar _ => true
  | _ => false

/-- The value of a literal without `X`, positions valued by `ε`, read off the word. -/
def nonXVal (x : List ℕ) (ε : ℕ → ℕ) (l : Lit) : Bool :=
  match l.atom with
  | .rel i js => decide (memW x i (js.map ε)) == l.pos
  | .eq a b => decide (ε a = ε b) == l.pos
  | .setVar _ => false

/-- The elements of the reduction. -/
abbrev U (D : Data) (x : List ℕ) : List ℕ := UW D.s D.r x

/-- Their number. -/
abbrev nW (D : Data) (x : List ℕ) : ℕ := (U D x).length

/-- The elements at the positions `ds`. -/
def epsW (D : Data) (x : List ℕ) (ds : List ℕ) : ℕ → ℕ := fun j => (U D x).getD (ds.getD j 0) 0

/-- The propositional variable of an `X`-literal under the digits `ds`. -/
def codeW (D : Data) (x : List ℕ) (ds : List ℕ) (l : Lit) : ℕ :=
  codeOf (nW D x) (l.atom.idxs.map fun j => ds.getD j 0)

/-- Some literal without `X` holds. -/
def satNonX (D : Data) (x : List ℕ) (ds : List ℕ) (C : List Lit) : Bool :=
  C.any fun l => !isXLit l && nonXVal x (epsW D x ds) l

/-- The clause written for `C` under the digits `ds`. -/
def clauseOut (D : Data) (x : List ℕ) (ds : List ℕ) (C : List Lit) : Lax429075.CNF.Clause :=
  if satNonX D x ds C then [⟨0, true⟩, ⟨0, false⟩]
  else (C.filter isXLit).map fun l => ⟨codeW D x ds l, l.pos⟩

/-- The clause `Y_c ∨ ¬Y_c`. -/
def taut (c : ℕ) : Lax429075.CNF.Clause := [⟨c, true⟩, ⟨c, false⟩]

/-- The clauses of the assignment `z`. -/
def zClauses (D : Data) (x : List ℕ) (z : ℕ) : Lax429075.CNF.Formula :=
  D.cnf.map (clauseOut D x (digits (nW D x) D.r z))

/-- **The formula.** -/
def alphaW (D : Data) (x : List ℕ) : Lax429075.CNF.Formula :=
  ((List.range (nW D x ^ D.r)).flatMap (zClauses D x)) ++ (List.range (nW D x ^ D.s)).map taut

/-- The vocabulary of the word fits the relation atoms, and the `X`-atoms have arity `s`. -/
def fitW (D : Data) (x : List ℕ) : Prop :=
  D.sfit = true ∧ ∀ p ∈ D.rels, p.1 < spW x ∧ x.getD (1 + p.1) 0 = p.2

instance (D : Data) (x : List ℕ) : Decidable (fitW D x) := by unfold fitW; infer_instance

/-- **The reduction.** When the formula does not fit, the no-instance `(Y₀-free empty clause, k)`. -/
def R (D : Data) (x : List ℕ) : List ℕ :=
  if fitW D x then Lax496464.WH_C3_WeightedSat.encode (alphaW D x) ++ [kW x] else [1, 0, kW x]

/-- The clause width. -/
def dBound (D : Data) : ℕ := 2 + (D.cnf.map List.length).sum

theorem le_sum_of_mem {L : List (List Lit)} {C : List Lit} (h : C ∈ L) :
    C.length ≤ (L.map List.length).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem h)

theorem isDCNF_alphaW (D : Data) (x : List ℕ) :
    Lax496464.WH_C3_WeightedSat.IsDCNF (dBound D) (alphaW D x) := by
  intro C hC
  unfold alphaW at hC
  rcases List.mem_append.mp hC with hC | hC
  · obtain ⟨z, -, hz⟩ := List.mem_flatMap.mp hC
    obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hz
    unfold clauseOut dBound
    split_ifs
    · simp
    · have := le_sum_of_mem hC0
      have h2 := List.length_filter_le isXLit C0
      simp only [List.length_map]; omega
  · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hC
    simp [taut, dBound]

theorem R_mem (D : Data) (x : List ℕ) :
    R D x ∈ (Lax496464.WH_C3_WeightedSat.pWSat
      {α | Lax496464.WH_C3_WeightedSat.IsDCNF (dBound D) α}).Domain := by
  unfold R
  split_ifs
  · exact ⟨_, isDCNF_alphaW D x, kW x, rfl⟩
  · refine ⟨[[]], fun C hC => ?_, kW x, rfl⟩
    simp at hC; subst hC; simp

/-! ### The data of a formula -/

/-- The relation atom of an atomic formula. -/
def relPair : Formula → Option (ℕ × ℕ)
  | .rel i ys => some (i, ys.length)
  | _ => none

/-- An `X`-atom has arity `s`. -/
def setOk (s : ℕ) : Formula → Bool
  | .setVar ys => ys.length == s
  | _ => true

/-- **The data of `∀ xs ψ`** with `X` of arity `s`. -/
def dataOf (xs : List ℕ) (ψ : Formula) (s : ℕ) : Data where
  s := s
  r := xs.dedup.length
  cnf := cnf xs.dedup ψ true
  rels := (atoms ψ).filterMap relPair
  sfit := (atoms ψ).all (setOk s)

/-- **The fit test of the word is the fit of the formula.** -/
theorem fitW_iff {x : List ℕ} {A : Structure} {k : ℕ} {bl : List (List ℕ)} (he : Enc x A k bl)
    (xs : List ℕ) (ψ : Formula) (s : ℕ) :
    fitW (dataOf xs ψ s) x ↔ (Formula.allBlock xs ψ).Fits A.arities s := by
  rw [Lax496464Proofs.WHierarchy.Logic.SatFacts.fits_allBlock, fits_iff_atoms]
  unfold fitW dataOf
  simp only [List.all_eq_true, List.mem_filterMap, he.spW_eq]
  constructor
  · rintro ⟨hs, hr⟩ a ha
    rcases isAtom_of_mem_atoms ψ a ha with ⟨i, ys, rfl⟩ | ⟨ys, rfl⟩ | ⟨u, v, rfl⟩
    · obtain ⟨h1, h2⟩ := hr (i, ys.length) ⟨_, ha, rfl⟩
      have h2' : x.getD (1 + i) 0 = ys.length := h2
      rw [he.arity h1] at h2'
      exact ⟨h1, h2'.symm⟩
    · have := hs _ ha
      simpa [setOk, Formula.Fits] using this
    · trivial
  · intro h
    refine ⟨fun a ha => ?_, ?_⟩
    · rcases isAtom_of_mem_atoms ψ a ha with ⟨i, ys, rfl⟩ | ⟨ys, rfl⟩ | ⟨u, v, rfl⟩
      · rfl
      · have := h _ ha
        simpa [setOk, Formula.Fits] using this
      · rfl
    · rintro ⟨i, l⟩ ⟨a, ha, hp⟩
      rcases isAtom_of_mem_atoms ψ a ha with ⟨i', ys, rfl⟩ | ⟨ys, rfl⟩ | ⟨u, v, rfl⟩
      · simp only [relPair, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        obtain ⟨h1, h2⟩ := h _ ha
        exact ⟨h1, by rw [he.arity h1, h2]⟩
      · simp [relPair] at hp
      · simp [relPair] at hp

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
