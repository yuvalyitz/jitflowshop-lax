import Lax496464.HittingSetFromSat
import Lax434930.NondeterministicPolynomialTime
import Lax429075.Reductions

/-!
---
title: Hitting Set Is NP-Hard
type: theorem
---
Every language in NP reduces to Hitting Set in polynomial time, by a reduction whose
output instances stay of size polynomial in the length of the input and satisfy
$2 \le k \le n$.

This is Karp's theorem. The reduction is Cook's theorem, followed by the reduction from
satisfiability of `HittingSetFromSat`: a formula is satisfiable exactly when its instance has
a hitting set of the required size, and the reduction runs in polynomial time on a Turing
machine writing the binary word of the instance. The theorem is stated twice: as a
many-one reduction into the language of Hitting Set, and in the form the reduction of this
submission consumes it.

The two restrictions on $k$ cost nothing. A hitting set of size exactly $k$ cannot exist
once $k$ exceeds the universe, so the upper one is a normalization; for the lower one, pad
an instance with one fresh element and the singleton set containing it, which forces that
element into every hitting set and raises $k$ by one.

The universe of an emitted instance is no larger than $4 + m$ plus the total size of the
sets. The reduction from satisfiability satisfies this, since its pairs alone cover the
universe. The clause is what lets the next reduction, which reads the *word* of the emitted
instance, be polynomial-time in that word: the shop it builds has more than $n^2$ jobs, so a
universe larger than the sets that present it — which a word of $O(\log n)$ bits could
name — could not be written by any machine polynomial in the word. It is the same
restriction the admissible words of the fixed-parameter statements carry, that the
universe is no larger than the word that presents it.

That the size of the emitted instance stays polynomially bounded is automatic for a
polynomial-time reduction, since an instance cannot be larger than what was written. It
is stated because it is what makes the composed reduction of this submission a *strong*
NP-hardness statement: the numbers of the constructed shop are polynomial in $n$, $m$ and
$k$, hence in the length of the original input.

# Formalization Notes

Cook's theorem is the archive's Cook–Levin theorem (`lax-429075`), with the classes P and NP
of `lax-434930`; polynomial time on a Turing machine is established by a word RAM program
and the archive's equivalence of the two models (`lax-759944`).

The bound on the size of the emitted instance is a power of $|x| + 2$ rather than of
$|x| + 1$: the instance has at least two elements even for the empty word, which no power
of $1$ allows.

The parameterized counterpart — that Hitting Set is W[2]-complete for the solution size —
is not stated. It is instead built into the definition of W[2]-hardness, which asks for an
fpt-reduction from Hitting Set, so that no statement depends on it and the class W[2]
itself need not be formalized.
-/

namespace Lax496464.HittingSetHardness

open Lax496464.HittingSet Lax496464.HittingSetFromSat Lax434930.PolynomialTime
open Lax434930.NondeterministicPolynomialTime Lax429075.CNF

/-- **Correctness of the reduction from satisfiability**: a formula is satisfiable exactly
when its instance has a hitting set of the required size. -/
axiom fromSat_correct (F : Formula) : Satisfiable F ↔ (inst F).HasHittingSet (vars F)

/-- **The reduction from satisfiability runs in polynomial time**, as a Turing machine
writing the binary word of the instance. -/
axiom fromSat_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime id
      (fun z : Instance × ℕ => encodeInstance z.1 z.2) reduce)

/-- **Hitting Set is NP-hard** (Karp): every language in NP has a polynomial-time
many-one reduction to it. -/
axiom npHard : ∀ A : Language, A ∈ NP → Lax429075.Reductions.ManyOne A HittingSetLanguage

/-- **Hitting Set is NP-hard** (Karp), already on instances with `2 ≤ k ≤ n`, by a
reduction whose output stays polynomially bounded and whose universe is covered by its
sets. -/
axiom hittingSet_npHard :
    ∀ A : Language, A ∈ NP →
      ∃ (f : Word → Instance × ℕ) (c : ℕ),
        Nonempty (Turing.TM2ComputableInPolyTime id
          (fun z : Instance × ℕ => encodeInstance z.1 z.2) f) ∧
        (∀ x, 2 ≤ (f x).2 ∧ (f x).2 ≤ (f x).1.n) ∧
        (∀ x, (f x).1.n + (f x).1.m ≤ (x.length + 2) ^ c) ∧
        (∀ x, (f x).1.n ≤ 4 + (f x).1.m + ∑ j : Fin (f x).1.m, ((f x).1.F j).card) ∧
        (∀ x, x ∈ A ↔ Instance.HasHittingSet (f x).1 (f x).2)

end Lax496464.HittingSetHardness
