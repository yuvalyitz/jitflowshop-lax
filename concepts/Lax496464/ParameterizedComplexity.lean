import Lax808846.RamComputes

/-!
---
title: Parameterized Problems and FPT-Reductions on a Word RAM
type: definition
---
A *parameterized problem* is a set of admissible input words, a yes-instance predicate on
them, and a parameter read off the word. It is *fixed-parameter tractable* if one word
RAM program decides it, on every admissible word $x$ of parameter $k$, within
$c\,g(k)\,(|x|+1)^c$ instructions, for a constant $c$ and a function $g$ of the parameter
alone.

An *fpt-reduction* from $P$ to $Q$ is a map on words that sends admissible words to
admissible words, preserves and reflects yes-instances, raises the parameter by at most a
function of it, and is computed by one word RAM program within the same kind of bound.
Fpt-reductions compose, and a problem that is fixed-parameter tractable and receives an
fpt-reduction makes the source problem fixed-parameter tractable as well.

# Formalization Notes

The parameter is read off the input word rather than carried beside it. This is what lets
one program serve every parameter: a program that had to be told $k$ from outside would
be a family of programs, one per parameter, free to hide unbounded advice in its
literals. The quantifier order says the same thing — the program and the constant come
before the instance, the parameter and the word length.

`Fits` is the fitting condition, an explicit inequality against $2^w$ rather than a
statement about logarithms. It says of each entry $v$ of a word that $c(|x|+v+1) \le
2^w$: every entry is a genuine word, with room left for the constant multiple of the
length that bounds the addresses and the step count. Entries are not bounded by the
length here — a due date or a weight may be any number at all — so quantifying over them
is what makes a claim about them honest rather than a silent assumption that they are
small.

A reduction's *output* has to fit as well, since a machine at word length $w$ reduces
what it writes modulo $2^w$. Like every fitting condition this restricts the inputs
rather than appearing as a hypothesis: as a hypothesis it would be empty, because no word
length accommodates every encoding of a fixed instance at once.

The bound is elementary, `c * g k * (x.length + 1) ^ c`, with the `+ 1` making it
meaningful on the empty word. The same constant serves as the multiple and as the
exponent, which costs nothing — raising either is raising both — and keeps one number to
quantify. `g` is an arbitrary function of the parameter: it bounds a fixed program's
running time rather than defining it, so no computability requirement on `g` is intended.

The polynomial factor is what the definition of fixed-parameter tractability asks for,
$f(k) \cdot n^{O(1)}$, and it is what a reduction needs here: the construction of this
submission emits an instance polynomially larger than the one it reads, so no reduction
computing it can run in time linear in its input.
-/

namespace Lax496464.ParameterizedComplexity

open Lax808846.Ram Lax808846.RamComputes

/-- A parameterized problem: the words that encode an instance, which of them are
yes-instances, and the parameter each one carries. -/
structure Problem where
  /-- The words that encode an instance. A program may do anything on the others. -/
  Domain : Set (List ℕ)
  /-- The yes-instances. -/
  Yes : List ℕ → Prop
  /-- The parameter, read off the word. -/
  param : List ℕ → ℕ

/-- The word `x` fits at word length `w`, with room for `c` times its length: every entry
`v` of `x` satisfies `c * (x.length + v + 1) ≤ 2 ^ w`. -/
def Fits (c w : ℕ) (x : List ℕ) : Prop := ∀ v ∈ x, c * (x.length + v + 1) ≤ 2 ^ w

open Classical in
/-- At every word length, the program decides `P` on every admissible word that fits,
within `c * g k * (|x| + 1) ^ c` instructions, where `k` is the word's parameter. It writes
`1` for a yes-instance and `0` for a no-instance. -/
def Decides (P : Problem) (prog : Program) (c : ℕ) (g : ℕ → ℕ) : Prop :=
  ∀ w : ℕ, ComputesInTime w prog
    {x | x ∈ P.Domain ∧ Fits c w x}
    (fun x => if P.Yes x then [1] else [0])
    (fun x => c * g (P.param x) * (x.length + 1) ^ c)

/-- `P` is **fixed-parameter tractable**: one program and one constant decide it within
`c * g k * (|x| + 1) ^ c` instructions, for some function `g` of the parameter alone. -/
def FPT (P : Problem) : Prop := ∃ (prog : Program) (c : ℕ) (g : ℕ → ℕ), Decides P prog c g

/-- The map `f` is an fpt-reduction from `P` to `Q`, computed by `prog` within
`c * g k * (|x| + 1) ^ c` instructions and raising the parameter by at most `h`. -/
structure IsFptReduction (P Q : Problem) (f : List ℕ → List ℕ) (prog : Program)
    (c : ℕ) (g h : ℕ → ℕ) : Prop where
  /-- The image of an admissible word is admissible. -/
  maps_domain : ∀ x ∈ P.Domain, f x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (f x))
  /-- The new parameter is bounded by a function of the old one alone. -/
  param_le : ∀ x ∈ P.Domain, Q.param (f x) ≤ h (P.param x)
  /-- At every word length, the program computes `f` on every admissible word that fits
  and whose image fits, within the stated bound. -/
  time : ∀ w : ℕ, ComputesInTime w prog
    {x | x ∈ P.Domain ∧ Fits c w x ∧ Fits c w (f x)}
    f (fun x => c * g (P.param x) * (x.length + 1) ^ c)

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop :=
  ∃ (f : List ℕ → List ℕ) (prog : Program) (c : ℕ) (g h : ℕ → ℕ),
    IsFptReduction P Q f prog c g h

@[inherit_doc] infix:50 " ≤fpt " => FptReduces

end Lax496464.ParameterizedComplexity
