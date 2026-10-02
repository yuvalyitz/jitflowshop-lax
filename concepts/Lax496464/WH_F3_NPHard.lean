import Lax888481.ParameterizedComplexity
import Lax434930.NondeterministicPolynomialTime
import Lax759944.TuringPolytime

/-!
---
title: NP-Hardness of a Problem on Words of Numbers
type: definition
---
A problem is **NP-hard** if every language in NP reduces to its yes-instances by a map computable
in polynomial time: a map $f$ from binary words to words of numbers such that $x \in A$ if and only
if $f(x)$ is a yes-instance, for every $x$.

# Formalization Notes

**Machines.** The map is computed by a Turing machine in polynomial time
(`Turing.TM2ComputableInPolyTime`). The machine reads the binary word and writes the canonical
binary encoding of the resulting word of numbers (`Lax759944.BinaryWordEncoding.encode`), each
number a separator followed by its bits. By the equivalence proved in `Lax759944`, this is
polynomial time on the word RAM in the bit size of the word.

**Words outside the domain.** The condition is $x \in A \iff f(x)$ is a yes-instance. A word
that $f$ maps to a word presenting no instance is therefore a non-member of $A$. `NPHardIn` asks
in addition that no word is mapped outside the domain.
-/

namespace Lax496464.WH_F3_NPHard

open Lax434930.PolynomialTime Lax434930.NondeterministicPolynomialTime
open Lax888481.ParameterizedComplexity

/-- `P` is **NP-hard**: every language in NP reduces to it in polynomial time by a Turing
machine writing the canonical encoding of the resulting word. -/
def NPHard (P : Problem) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime id Lax759944.BinaryWordEncoding.encode f) ∧
      ∀ x, x ∈ A ↔ P.Yes (f x)

/-- `P` is **NP-hard on its domain**: as `NPHard`, and in addition the reduction always outputs a
word of the domain, that is a word presenting an instance of `P`. This is the form a reduction that
is correct only on instances can be composed with. -/
def NPHardIn (P : Problem) : Prop :=
  ∀ A : Language, A ∈ NP →
    ∃ f : Word → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime id Lax759944.BinaryWordEncoding.encode f) ∧
      ∀ x, f x ∈ P.Domain ∧ (x ∈ A ↔ P.Yes (f x))

end Lax496464.WH_F3_NPHard
