import Lax496464.WH_D08_WSatInA1
import Lax496464Proofs.WHierarchy.Logic.Words
import Lax496464Proofs.WHierarchy.Logic.SatFacts
import Lax496464Proofs.WHierarchy.HittingSet.Firsts

/-! # `p-WSat(d-CNF) ≤fpt p-MC(Σ_1)`: the construction

The input word lists the clauses of `α` by their literal codes; `cl` is that list of lists of codes
and `k` the weight. The literal occurrences are numbered `0, …, L - 1` in the order of the word
(`flat cl`), and a variable is represented by its **first occurrence** (`fst`). The universe of the
structure is `{0, …, L}`; the extra element `L` is a padding element `z`.

* `Z = {(z)}`, `C = {(fst j) : j < L}` (the variables),
* `N = {key c}`: for each clause `c` the tuple of length `d + 1` whose entry `p` is the first
  occurrence of the variable of the `p`-th literal of `c` when that literal is negative, and `z`
  otherwise;
* `Lr = {key c ++ pad ch}`: for each clause `c` and each branch word `b < d ^ k` for which the
  bounded search `sim c b` succeeds with the set `ch` (listed, at most `k` elements), padded with `z`
  to length `k + 1`. `ch` hits every clause with the same key as `c`, and every set of at most `k`
  elements hitting those clauses contains the result of some branch word.

The sentence is `∃ x_0 … x_{k-1} w (y_{t,j})_{t,j}`
`(Z w ∧ ⋀_i C x_i ∧ ⋀_{j<i} ¬ x_i = x_j ∧ ⋀_{t} (¬ N v_t ∨ (Lr (v_t, y_t) ∧ ⋀_j ⋁_{i ≤ k} y_{t,j} = x_i)))`,
where `t` ranges over the maps `{0,…,d} → {x_0, …, x_{k-1}, w}` (as numbers written in base `k+1`,
digit `k` standing for `w`).

The structure is written as the program writes it: every tuple of every relation becomes one number
(its tag, then its entries in base `M = L + 4`), all numbers are stored in one array, and a relation
lists the numbers with its tag that are the first occurrence of their value. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder Lax496464.WH_B3_LogicProblems
open Lax496464Proofs.WHierarchy.Logic.StructureCode

/-! ### Numbers in base `M` -/

/-- The number with digits `l` (least significant first) in base `M`. -/
def num (M : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => a + M * num M l

/-- The first `a` digits of `e` in base `M`. -/
def digitsOf (M a e : ℕ) : List ℕ := (List.range a).map fun p => e / M ^ p % M

/-! ### Decoding the input word -/

/-- The clauses: `n` times a length followed by that many codes. -/
def parseCl : ℕ → List ℕ → List (List ℕ)
  | 0, _ => []
  | n + 1, w => (w.drop 1).take (w.getD 0 0) :: parseCl n ((w.drop 1).drop (w.getD 0 0))

/-- The clauses of an input word. -/
def clOf (x : List ℕ) : List (List ℕ) := parseCl (x.getD 0 0) (x.drop 1)

/-- The weight of an input word: its last entry. -/
def kOf (x : List ℕ) : ℕ := x.getLast?.getD 0

/-- The word of a list of clauses and a weight. -/
def wordOf' (cl : List (List ℕ)) (k : ℕ) : List ℕ :=
  cl.length :: (cl.flatMap fun c => c.length :: c) ++ [k]

/-! ### The data of the clauses -/

section Data

variable (cl : List (List ℕ))

/-- The number of literal occurrences. -/
def nL : ℕ := cl.flatten.length

/-- The code of occurrence `j`. -/
def code (j : ℕ) : ℕ := cl.flatten.getD j 0

/-- The variables of the occurrences. -/
def varList : List ℕ := cl.flatten.map (· / 2)

/-- The first occurrence of the variable of occurrence `j`. -/
def fst (j : ℕ) : ℕ := (varList cl).idxOf (code cl j / 2)

/-- The first occurrence of clause `c`. -/
def off (c : ℕ) : ℕ := ((cl.take c).map List.length).sum

/-- The length of clause `c`. -/
def len (c : ℕ) : ℕ := (cl.getD c []).length

/-- The base of the numbers of the tuples. -/
def MM : ℕ := nL cl + 4

/-- Entry `p` of the key of clause `c`. -/
def keyE (c p : ℕ) : ℕ :=
  if p < len cl c then
    (if code cl (off cl c + p) % 2 = 0 then nL cl else fst cl (off cl c + p))
  else nL cl

/-- The key of clause `c`: its negative part, as a tuple of length `d + 1` padded with `z = L`. -/
def key (d c : ℕ) : List ℕ := (List.range (d + 1)).map (keyE cl c)

/-- `ch` hits clause `c`: some positive literal of `c` has its variable in `ch`. -/
def hitB (ch : List ℕ) (c : ℕ) : Bool :=
  (List.range (len cl c)).any fun i =>
    decide (code cl (off cl c + i) % 2 = 0 ∧ fst cl (off cl c + i) ∈ ch)

/-- One step of the bounded search for clause `c` along the digit function `δ`: an unhit clause of
the group of `c` is hit by the literal the next digit names, or the search fails. -/
def simStep (d k c : ℕ) (δ : ℕ → ℕ) : Option (List ℕ) → ℕ → Option (List ℕ)
  | none, _ => none
  | some ch, c2 =>
    if key cl d c2 = key cl d c ∧ hitB cl ch c2 = false then
      if ch.length = k then none
      else if δ ch.length < len cl c2 ∧ code cl (off cl c2 + δ ch.length) % 2 = 0 then
        some (ch ++ [fst cl (off cl c2 + δ ch.length)])
      else none
    else some ch

/-- The bounded search along a digit function. -/
def simD (d k c : ℕ) (δ : ℕ → ℕ) : Option (List ℕ) :=
  (List.range cl.length).foldl (simStep cl d k c δ) (some [])

/-- The digits of the branch word `b`. -/
def bdig (d b : ℕ) : ℕ → ℕ := fun n => b / d ^ n % d

/-- The bounded search along the branch word `b < d ^ k`. -/
def sim (d k c b : ℕ) : Option (List ℕ) := simD cl d k c (bdig d b)

/-- A found set, padded with `z` to length `k + 1`. -/
def pad (k : ℕ) (ch : List ℕ) : List ℕ :=
  (List.range (k + 1)).map fun q => if q < ch.length then ch.getD q 0 else nL cl

/-- The tuples of the relation `Lr`, in the order the program finds them. -/
def lTuples (d k : ℕ) : List (List ℕ) :=
  (List.range cl.length).flatMap fun c =>
    (List.range (d ^ k)).filterMap fun b => (sim cl d k c b).map fun ch => key cl d c ++ pad cl k ch

/-! ### The numbers of the tuples -/

/-- The numbers of the variables of the occurrences (tag `0`). -/
def varNums : List ℕ := (List.range (nL cl)).map fun j => code cl j / 2 * MM cl

/-- The numbers of the tuples of `C` (tag `1`). -/
def canonNums : List ℕ := (List.range (nL cl)).map fun j => 1 + MM cl * fst cl j

/-- The number of the key of clause `c` (tag `2`). -/
def nNum (d c : ℕ) : ℕ := 2 + MM cl * num (MM cl) (key cl d c)

/-- The numbers of the tuples of `N`. -/
def nNums (d : ℕ) : List ℕ := (List.range cl.length).map (nNum cl d)

/-- The numbers of the tuples of `Lr` (tag `3`). -/
def lNums (d k : ℕ) : List ℕ := (lTuples cl d k).map fun t => 3 + MM cl * num (MM cl) t

/-- The size of the array of numbers. -/
def sz (d k : ℕ) : ℕ := 2 * nL cl + cl.length + cl.length * d ^ k

/-- The array of numbers, after all tuples are stored. -/
def hs (d k : ℕ) : List ℕ :=
  varNums cl ++ canonNums cl ++ nNums cl d ++ lNums cl d k ++
    List.replicate (sz cl d k - (2 * nL cl + cl.length + (lNums cl d k).length)) 0

/-- The first occurrences of the values of the array. -/
def fe (d k : ℕ) : List ℕ := Lax496464Proofs.WHierarchy.HittingSet.Firsts.firsts (hs cl d k)

/-- The tuples with tag `g` and arity `a`: one per value, in the order of first occurrence. -/
def emitList (d k g a : ℕ) : List (List ℕ) :=
  ((List.range (sz cl d k)).filter fun t =>
      decide ((hs cl d k).getD t 0 % MM cl = g ∧ (fe cl d k).getD t 0 = t)).map
    fun t => digitsOf (MM cl) a ((hs cl d k).getD t 0 / MM cl)

/-- The vocabulary: `Z`, `C` unary, `N` of arity `d + 1`, `Lr` of arity `d + k + 2`. -/
def arities (d k : ℕ) : List ℕ := [1, 1, d + 1, d + k + 2]

/-- The lists of tuples of the four relations. -/
def tss (d k : ℕ) : List (List (List ℕ)) :=
  [[[nL cl]], emitList cl d k 1 1, emitList cl d k 2 (d + 1), emitList cl d k 3 (d + k + 2)]

/-- **The word of the structure.** -/
def structWord (d k : ℕ) : List ℕ := wordOf (arities d k) (nL cl + 1) (tss cl d k)

end Data

/-! ### The sentence -/

/-- The true formula `x_0 = x_0`. -/
def tru : Formula := .eq 0 0

/-- The false formula `¬ x_0 = x_0`. -/
def fls : Formula := .neg (.eq 0 0)

/-- A right-nested conjunction, closed by `tru`. -/
def bigAnd : List Formula → Formula
  | [] => tru
  | φ :: l => .and φ (bigAnd l)

/-- A right-nested disjunction, closed by `fls`. -/
def bigOr : List Formula → Formula
  | [] => fls
  | φ :: l => .or φ (bigOr l)

section Sentence

variable (d k : ℕ)

/-- The number of maps `{0, …, d} → {0, …, k}`. -/
def FF : ℕ := (k + 1) ^ (d + 1)

/-- The variable `y_{t,j}`. -/
def yv (t j : ℕ) : ℕ := (k + 1) + t * (k + 1) + j

/-- The variables `v_t`: the digits of `t` in base `k + 1`. -/
def vt (t : ℕ) : List ℕ := (List.range (d + 1)).map fun p => t / (k + 1) ^ p % (k + 1)

/-- The variables `y_t`. -/
def yt (t : ℕ) : List ℕ := (List.range (k + 1)).map (yv k t)

/-- `y_{t,j}` is one of `x_0, …, x_{k-1}, w`. -/
def inS (t j : ℕ) : Formula := bigOr ((List.range (k + 1)).map fun i => .eq (yv k t j) i)

/-- The conjunct for the map `t`. -/
def clauseF (t : ℕ) : Formula :=
  .or (.neg (.rel 2 (vt d k t)))
    (.and (.rel 3 (vt d k t ++ yt k t)) (bigAnd ((List.range (k + 1)).map (inS k t))))

/-- The distinctness conjuncts `¬ x_i = x_j` for `j < i < k`. -/
def distinctL : List Formula := (List.range k).flatMap fun i => (List.range i).map fun j => .neg (.eq i j)

/-- The quantifier-free part. -/
def psi : Formula :=
  .and (.rel 0 [k])
    (.and (bigAnd ((List.range k).map fun i => .rel 1 [i]))
      (.and (bigAnd (distinctL k)) (bigAnd ((List.range (FF d k)).map (clauseF d k)))))

/-- The number of quantified variables. -/
def nv : ℕ := (k + 1) + FF d k * (k + 1)

/-- **The sentence.** -/
def phi : Formula := Formula.exBlock (List.range (nv d k)) (psi d k)

end Sentence

/-- **The reduction**, on words. -/
def red (d : ℕ) (x : List ℕ) : List ℕ := structWord (clOf x) d (kOf x) ++ (phi d (kOf x)).encode

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs
