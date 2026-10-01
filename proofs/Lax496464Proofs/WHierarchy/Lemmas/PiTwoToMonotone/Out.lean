import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf
import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Eval

/-! # The reduction on words

With `U = UW s r x` (`n` elements) and the tuple codes `c < N = n^s` (the tuple of elements of `U`
at the base-`n` digits of `c`), the assignments of the positions are the pairs `za < n^p`,
`zb < n^q`: position `j < q` takes the digit `j` of `zb`, position `q + i` the digit `i` of `za`
(`dsOf`). The oracle of a block with values evaluates relation atoms by scanning the word
(`memW`), equations by comparing elements, and `X`-atoms by `Blocks.dec` on the code of the tuple.
`good za b v zb`: the evaluation gives *true* without meeting an undecided atom.

`R`: the word of the monotone formula `Cnf.Par.alpha` with the parameter `W = (k+1)^D`; or, when
the formula does not fit the vocabulary of the word, the no-instance `[[]]` with parameter `k`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out

open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Eval
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Blocks Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Cnf

variable (Dt : Data) (x : List ℕ)

/-- The elements of the reduction. -/
abbrev U : List ℕ := UW Dt.s Dt.r x

/-- Their number. -/
abbrev nU : ℕ := (U Dt x).length

/-- The parameters of the formula. -/
def par : Par := ⟨kW x, nU Dt x ^ Dt.s, Dt.D, nU Dt x ^ Dt.p, nU Dt x ^ Dt.q⟩

/-- The digits of the positions under `(za, zb)`. -/
def dsOf (za zb : ℕ) : List ℕ := digits (nU Dt x) Dt.q zb ++ digits (nU Dt x) Dt.p za

/-- The element at position `j`. -/
def elemOf (ds : List ℕ) (j : ℕ) : ℕ := (U Dt x).getD (ds.getD j 0) 0

/-- The code of the tuple at the positions `js`. -/
def codeW (ds : List ℕ) (js : List ℕ) : ℕ := codeOf (nU Dt x) (js.map fun j => ds.getD j 0)

/-- **The oracle** of block `b` with values `v` under the digits `ds`. -/
def oracle (ds : List ℕ) (b v : ℕ) : Oracle where
  relv i js := decide (memW x i (js.map (elemOf Dt x ds)))
  eqv a c := decide (elemOf Dt x ds a = elemOf Dt x ds c)
  xdec js := dec (kW x) Dt.D ((par Dt x).bd b) ((par Dt x).vd v) (codeW Dt x ds js)

/-- The block `b` with values `v` makes `ψ` true under `(za, zb)`. -/
def good (za b v zb : ℕ) : Bool := ev (oracle Dt x (dsOf Dt x za zb) b v) Dt.ψ == (true, false)

/-- **The formula.** -/
def alphaW : Lax429075.CNF.Formula := (par Dt x).alpha (good Dt x)

/-- **The reduction.** -/
def R : List ℕ :=
  if fitW Dt x then Lax496464.WH_C3_WeightedSat.encode (alphaW Dt x) ++ [(par Dt x).W] else [1, 0, kW x]

theorem R_mem : R Dt x ∈ (Lax496464.WH_C3_WeightedSat.pWSat
    {α | Lax496464.WH_C3_WeightedSat.IsMonotone α}).Domain := by
  unfold R
  split_ifs
  · exact ⟨_, isMonotone_alpha _ _, _, rfl⟩
  · refine ⟨[[]], fun C hC => ?_, kW x, rfl⟩
    simp at hC; subst hC; simp

theorem R_last : (R Dt x).getLast?.getD 0 ≤ (kW x + 1) ^ Dt.D + kW x := by
  unfold R
  split_ifs
  · simp [par, Par.W]
  · simp

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Out
