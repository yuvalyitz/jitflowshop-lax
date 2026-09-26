import Lax496464.BinaryEncoding
import Lax434930.NondeterministicPolynomialTime

/-!
---
title: NP-hardness, and strong NP-hardness, of a scheduling problem
type: definition
---
A property of instances is *NP-hard* if every language in NP has a polynomial-time
many-one reduction to it, the reduction's output being an instance in the binary
encoding.

It is *strongly NP-hard* if such a reduction exists whose emitted instances have all
their numbers bounded by a fixed polynomial in the length of the input. A strongly
NP-hard problem admits no pseudo-polynomial algorithm unless $\mathrm{P} =
\mathrm{NP}$: an algorithm polynomial in the magnitudes of the numbers would be
polynomial in the input length on the image of such a reduction.

# Formalization notes

Hardness is defined by quantifying over NP rather than against a fixed complete problem.
NP is available, so the definition a textbook gives can be written down.

The reduction's target is an instance with its threshold rather than a word, with the
encoding applied by the definition. This keeps a statement about a problem from also
being a statement about which words are well-formed.

"Strongly NP-hard on a class" is the same definition with one further clause, so that a
single reduction witnesses both the plain claim and the claim on the slice the
construction actually lands in — here, instances all of whose weights are one.

Strength is a clause on the reduction, not a different encoding. The usual formulation —
NP-hardness under the unary encoding — says the same thing: a polynomial-time reduction
writing numbers in unary is exactly a polynomial-time reduction whose numbers are
polynomially bounded. Stating it as a bound keeps one encoding in play and makes the
content visible, namely that the construction's numbers do not grow with the values it
reads but only with the size of what it reads.

The polynomial is written as $(|x|+1)^c$ rather than as an element of $\mathbb{N}[X]$.
Every polynomial with natural coefficients is dominated by such a power, so nothing is
lost, and the bound stays elementary, in the style of the running times on the word RAM.
-/

namespace Lax496464.NPHardness

open Lax496464.FlowShop Lax496464.BinaryEncoding
open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime

/-- A decision problem on instances with a threshold. -/
abbrev Problem := Instance → ℕ → Prop

/-- `Q` is **NP-hard**: every language in NP reduces to it in polynomial time. -/
def NPHard (Q : Problem) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → Instance × ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime id
        (fun z : Instance × ℕ => encodeDecisionInstance z.1 z.2) f) ∧
      ∀ x, x ∈ A ↔ Q (f x).1 (f x).2

/-- `Q` is **strongly NP-hard**: it is NP-hard by a reduction whose emitted instances
have all their numbers, and their threshold, bounded by a fixed polynomial in the length
of the input. -/
def StronglyNPHard (Q : Problem) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ (f : Word → Instance × ℕ) (c : ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime id
        (fun z : Instance × ℕ => encodeDecisionInstance z.1 z.2) f) ∧
      (∀ x, max (maxNumber (f x).1) (f x).2 ≤ (x.length + 2) ^ c) ∧
      ∀ x, x ∈ A ↔ Q (f x).1 (f x).2

/-- `Q` is **strongly NP-hard on `C`**: the same, by a reduction all of whose outputs
lie in `C`. -/
def StronglyNPHardOn (Q : Problem) (C : Instance → Prop) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ (f : Word → Instance × ℕ) (c : ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime id
        (fun z : Instance × ℕ => encodeDecisionInstance z.1 z.2) f) ∧
      (∀ x, max (maxNumber (f x).1) (f x).2 ≤ (x.length + 2) ^ c) ∧
      (∀ x, C (f x).1) ∧
      ∀ x, x ∈ A ↔ Q (f x).1 (f x).2

end Lax496464.NPHardness
