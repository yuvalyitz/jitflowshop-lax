import Lax496464.FlowShop
import Lax434930.PolynomialTime
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Bits

/-!
---
title: Binary encoding of an instance
type: definition
---
An instance as a binary word, the representation against which classical complexity
measures running time. A number is written as its binary digits preceded by their number
in unary, which makes the encoding self-delimiting; an instance is the number of jobs,
the number of machines, and then the four arrays of preprocessing times, processing
times, due dates and weights, in that order.

# Formalization notes

This encoding exists beside the word encoding and does not replace it. The two answer
different questions. A word RAM is handed numbers and charges one instruction per
operation on them, so its input is a list of numbers and its running time is counted in
their number; a Turing machine is handed bits, so a claim of polynomial time there is a
claim about a number of bits. The statement that quantifies over all of NP is a
Turing-machine statement and uses this encoding.

Numbers are written in binary rather than in unary. The difference is not cosmetic for a
hardness claim: under a unary encoding the input is exponentially longer, a
polynomial-time reduction correspondingly easier to achieve, and the resulting claim
weaker. Binary is what an unqualified claim of NP-hardness means, and the extra clause
that makes a claim of *strong* NP-hardness is stated separately, as a bound on the
numbers a reduction emits, rather than by changing the encoding under it.

The encoding need not be injective on instances that differ only in inaccessible data,
and nothing here claims it is. What the statements need is that it is computable in
polynomial time and that a reduction's image is determined, both obligations of the proof
layer.
-/

namespace Lax496464.BinaryEncoding

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax434930.PolynomialTime

/-- A natural number as a binary word: its digits, least significant first, preceded by
their number in unary. The unary prefix makes the code self-delimiting. -/
def encodeNat (n : ℕ) : Word :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

/-- An instance as a binary word: the two counts, then the preprocessing times, the
processing times, the due dates and the weights. -/
def encodeInstance (I : Instance) : Word :=
  encodeNat I.jobs ++ encodeNat I.machines ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.p j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.q j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.d j)) ++
    (List.finRange I.jobs).flatMap (fun j => encodeNat (I.w j))

/-- An instance together with a threshold, as a binary word. -/
def encodeDecisionInstance (I : Instance) (W : ℕ) : Word :=
  encodeInstance I ++ encodeNat W

/-- The largest number appearing in an instance. A reduction witnesses *strong*
NP-hardness when this stays polynomial in the length of its input. -/
def maxNumber (I : Instance) : ℕ :=
  ((List.finRange I.jobs).map fun j =>
      max (max (I.p j) (I.q j)) (max (I.d j) (I.w j))).foldr max (max I.jobs I.machines)

end Lax496464.BinaryEncoding
