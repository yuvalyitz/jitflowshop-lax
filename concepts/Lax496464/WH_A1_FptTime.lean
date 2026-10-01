import Lax759944.RamPolytime
import Mathlib.Computability.Partrec

/-!
---
title: Fixed-parameter time on the word RAM
type: definition
---
A function $F$ on words is computable in **fixed-parameter time** with respect to a parameter
$\kappa$ if a single word-RAM program computes it within $f(\kappa(x))\cdot(|x|+1)^d$ steps, for a
computable function $f$ and a constant $d$, where $|x|$ is the bit size of the input
[FG06, Definition 1.4]. It is computable in **polynomial time** if $f$ can be taken constant. Both
notions are relative to a set $D$ of admissible inputs; on words outside $D$ the program is
unconstrained.

These are the running times of fpt-algorithms and fpt-reductions; every notion of the hierarchies
is built on them.

# Formalization notes

The machine is the word RAM `Lax808846.Ram`, with the conventions of the archive's polynomial-time
word RAM `Lax759944.RamPolytime`:

* the input word $x$ is given as the length-prefixed tape `x.length :: x`;
* the input size is the bit size `Lax759944.BinaryWordEncoding.bitSize`, so a number counts with
  its binary length;
* the program must halt with the correct output within the bound at **every** word length from the
  bound on;
* the tape and the output fit in words of that length.

A single bound $B = f(\kappa(x))\cdot(|x|+1)^d$ serves as the time bound and as the least admissible
word length. That the word length may depend on the parameter is what makes fixed-parameter
computations compose (`WH_A4_MachineFacts`): the output of a first program, of size up to
$f(k)\cdot|x|^d$, is the input of the second.

On the set of all words, `PolyTimeOn` is the archive's `Lax759944.RamPolytime.RamPolytime`
(`WH_A5_Bridges.polyTimeOn_univ_iff`).
-/

namespace Lax496464.WH_A1_FptTime

open Lax808846.Ram Lax759944.BinaryWordEncoding Lax759944.RamPolytime

/-- The fixed-parameter bound `f(k) · (n + 1)^d`, for a parameter value `k` and an input size `n`. -/
def fptBound (f : ℕ → ℕ) (d k n : ℕ) : ℕ := f k * (n + 1) ^ d

/-- On every word `x` of `D`, the program `p` computes `F x` from the tape `x.length :: x`
within `B = f(κ x) · (bitSize x + 1)^d` instructions, at every word length `w ≥ B`; and the
tape and the output fit in words of length `B`. -/
def ComputesInFptTime (p : Program) (D : Set (List ℕ)) (κ : List ℕ → ℕ)
    (F : List ℕ → List ℕ) (f : ℕ → ℕ) (d : ℕ) : Prop :=
  ∀ x ∈ D,
    FitsInWords (fptBound f d (κ x) (bitSize x)) ((x.length :: x) ++ F x) ∧
      ∀ w : ℕ, fptBound f d (κ x) (bitSize x) ≤ w →
        ∃ t ≤ fptBound f d (κ x) (bitSize x), RunsTo w p (x.length :: x) (F x) t

/-- **Fixed-parameter time.** `F` is computable on the words of `D` in time `f(κ x) · (|x| + 1)^d`
by one program, for a computable `f` and a constant `d`. -/
def FptTimeOn (D : Set (List ℕ)) (κ : List ℕ → ℕ) (F : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (f : ℕ → ℕ) (d : ℕ), Computable f ∧ ComputesInFptTime p D κ F f d

/-- **Polynomial time.** `F` is computable on the words of `D` in time `c · (|x| + 1)^d` by one
program. -/
def PolyTimeOn (D : Set (List ℕ)) (F : List ℕ → List ℕ) : Prop :=
  ∃ (p : Program) (c d : ℕ), ComputesInFptTime p D (fun _ => 0) F (fun _ => c) d

end Lax496464.WH_A1_FptTime
