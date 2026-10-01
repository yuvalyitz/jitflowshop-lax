import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core
import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.CsrWord

/-!
# Σ₁[2] model checking to Clique: the map on words

Everything is read off the word `x = (structure) ++ (formula)` by total functions that mirror the
program step for step (every read of the word is a read with default `0`):

* `hp x i`: the start of the block of symbol `i`, walking the header (clamped to `|x|`);
* `tok x`: the tokenizer, run `|x|` times from the start of the formula: it skips the quantifier
  prefix and lists the nodes of the quantifier-free part in prefix order (tag and atom number),
  the two variables of each atom (`vs`), and for each atom the block start and arity of its symbol
  (arity `0` for an equation); `fl` records whether the atoms fit the vocabulary;
* `okv x c`: the formula evaluated, right to left with a stack, under the valuation `c` of the atoms;
* `elL x`: the candidate values — the entries of the word below the size of the universe, then
  `0, …, min(size, |x| + k) - 1`;
* the graph `Core.graph (paramsX x)` on `NGX x = 2^q · ne · k` vertices, `k = 2q`.

The reduction writes the compressed sparse row word of that graph, then `k`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs

open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core

/-- A read of the word, `0` out of range. -/
def rd (x : List ℕ) (i : ℕ) : ℕ := x.getD i 0

/-- The number of symbols. -/
def sX (x : List ℕ) : ℕ := rd x 0

/-- The size of the universe. -/
def NsX (x : List ℕ) : ℕ := rd x (sX x + 1)

/-- The start of the first block. -/
def hp0 (x : List ℕ) : ℕ := if x.length < sX x + 2 then x.length else sX x + 2

/-- One step of the header walk: past the block of symbol `i` that starts at `p`. -/
def hpStep (x : List ℕ) (i p : ℕ) : ℕ :=
  if x.length < p + 1 + rd x p * rd x (1 + i) then x.length else p + 1 + rd x p * rd x (1 + i)

/-- The start of the block of symbol `i` (for `i` the number of symbols: the formula). -/
def hp (x : List ℕ) : ℕ → ℕ
  | 0 => hp0 x
  | i + 1 => hpStep x i (hp x i)

/-! ### The tokenizer -/

/-- The tokenizer state. -/
structure TS where
  /-- The position in the word. -/
  p : ℕ
  /-- The nodes so far: tag and atom number. -/
  nd : List (ℕ × ℕ)
  /-- The two variables of each atom so far. -/
  vs : List ℕ
  /-- The block start of the symbol of each atom so far (`0` for an equation). -/
  ab : List ℕ
  /-- The arity of the symbol of each atom so far (`0` for an equation). -/
  ar : List ℕ
  /-- `1` while every atom fits the vocabulary. -/
  fl : ℕ

/-- A relation atom `0, i, n, y₁, …`. -/
def relStep (x : List ℕ) (st : TS) : TS :=
  { p := if rd x (st.p + 2) < x.length then st.p + 3 + rd x (st.p + 2) else x.length
    nd := st.nd ++ [(0, st.ab.length)]
    vs := st.vs ++ [if rd x (st.p + 2) = 0 then 0 else rd x (st.p + 3),
      if rd x (st.p + 2) = 2 then rd x (st.p + 4)
        else if rd x (st.p + 2) = 0 then 0 else rd x (st.p + 3)]
    ab := st.ab ++ [if rd x (st.p + 1) < sX x then hp x (rd x (st.p + 1)) else 0]
    ar := st.ar ++ [if rd x (st.p + 1) < sX x then rd x (1 + rd x (st.p + 1)) else 0]
    fl := if rd x (st.p + 1) < sX x then
        (if rd x (st.p + 2) = rd x (1 + rd x (st.p + 1)) then st.fl else 0) else 0 }

/-- An equation `2, y₁, y₂`. -/
def eqStep (x : List ℕ) (st : TS) : TS :=
  { p := st.p + 3
    nd := st.nd ++ [(2, st.ab.length)]
    vs := st.vs ++ [rd x (st.p + 1), rd x (st.p + 2)]
    ab := st.ab ++ [0]
    ar := st.ar ++ [0]
    fl := st.fl }

/-- Any other tag: a connective node. -/
def otherStep (x : List ℕ) (st : TS) : TS :=
  { st with p := st.p + 1, nd := st.nd ++ [(rd x st.p, 0)] }

/-- One step of the tokenizer. -/
def tokStep (x : List ℕ) (st : TS) : TS :=
  if st.p < x.length then
    if rd x st.p = 6 then { st with p := st.p + 2 }
    else if rd x st.p = 0 then relStep x st
    else if rd x st.p = 2 then eqStep x st
    else otherStep x st
  else st

/-- The initial state: at the start of the formula. -/
def tokInit (x : List ℕ) : TS := ⟨hp x (sX x), [], [], [], [], 1⟩

/-- The tokenizer, run `|x|` times. -/
def tok (x : List ℕ) : TS := (tokStep x)^[x.length] (tokInit x)

/-- The number of atoms. -/
def qX (x : List ℕ) : ℕ := (tok x).ab.length

/-- The number of rows (and the new parameter). -/
def kX (x : List ℕ) : ℕ := 2 * qX x

/-- The number of valuations of the atoms. -/
def CX (x : List ℕ) : ℕ := 2 ^ qX x

/-! ### The evaluation -/

/-- One step of the right-to-left evaluation, with the stack top first. -/
def evStep (c : ℕ) (nd : ℕ × ℕ) (l : List ℕ) : List ℕ :=
  if nd.1 = 0 then bitv c nd.2 :: l
  else if nd.1 = 2 then bitv c nd.2 :: l
  else if nd.1 = 3 then (if l.length = 0 then l else (1 - l.headD 0) :: l.tail)
  else if nd.1 = 4 then
    (if l.length < 2 then l else (if l.headD 0 = 0 then 0 else l.tail.headD 0) :: l.tail.tail)
  else if nd.1 = 5 then
    (if l.length < 2 then l else (if l.tail.headD 0 + l.headD 0 = 0 then 0 else 1) :: l.tail.tail)
  else l

/-- The stack after evaluating a list of nodes right to left. -/
def evalNd (c : ℕ) (nd : List (ℕ × ℕ)) : List ℕ := nd.foldr (evStep c) []

/-- The formula under the valuation `c`. -/
def okv (x : List ℕ) (c : ℕ) : ℕ := (evalNd c (tok x).nd).headD 0

/-! ### Candidate values -/

/-- The bound `min(size, |x| + k)` of the second part of the candidates. -/
def limX (x : List ℕ) : ℕ := if NsX x < x.length + kX x then NsX x else x.length + kX x

/-- The candidate values. -/
def elL (x : List ℕ) : List ℕ := x.filter (fun v => decide (v < NsX x)) ++ List.range (limX x)

/-- The number of candidates (`0` when the formula does not fit). -/
def neX (x : List ℕ) : ℕ := if (tok x).fl = 1 then (elL x).length else 0

/-- The number of vertices. -/
def NGX (x : List ℕ) : ℕ := CX x * (neX x * kX x)

/-! ### The atom test -/

/-- The number of tuples scanned in a block. -/
def cntX (x : List ℕ) (sb : ℕ) : ℕ := if x.length < rd x sb then x.length else rd x sb

/-- The tuple `j` of the block at `sb`, of arity `sa`, begins with `w1` (and continues with `w2`
when `sa ≠ 1`). -/
def tupHit (x : List ℕ) (sb sa w1 w2 j : ℕ) : Bool :=
  rd x (sb + 1 + j * sa) == w1 && (sa == 1 || rd x (sb + 1 + j * sa + 1) == w2)

/-- Some of the first `n` tuples of the block hits. -/
def memN (x : List ℕ) (sb sa w1 w2 n : ℕ) : Bool := (List.range n).any (tupHit x sb sa w1 w2)

/-- The scan of a block. -/
def memX (x : List ℕ) (sb sa w1 w2 : ℕ) : Bool := memN x sb sa w1 w2 (cntX x sb)

/-- The truth of atom `m` at the values `w1, w2`. -/
def atomT (x : List ℕ) (m w1 w2 : ℕ) : ℕ :=
  if (tok x).ar.getD m 0 = 0 then (if w1 = w2 then 1 else 0)
  else if memX x ((tok x).ab.getD m 0) ((tok x).ar.getD m 0) w1 w2 then 1 else 0

/-- The data of the graph. -/
def paramsX (x : List ℕ) : Params where
  k := kX x
  ne := neX x
  E e := (elL x).getD e 0
  vs r := (tok x).vs.getD r 0
  ok := okv x
  atm := atomT x

/-- The adjacency of the graph. -/
def adjX (x : List ℕ) : ℕ → ℕ → Bool := adjP (paramsX x)

/-- **The reduction**: the compressed sparse row word of the graph, then `k`. -/
def reduce (x : List ℕ) : List ℕ :=
  Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.CsrWord.csrWord (adjX x) (NGX x) ++ [kX x]

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
