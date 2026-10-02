import Lax496464.WH_A1_FptTime
import Lax888481.ParameterizedComplexity

/-!
---
title: FPT-Reductions, FPT, Hardness and Completeness
type: definition
---
A *parameterized problem* consists of a set of instances, the yes-instances among them, and a
parameter $\kappa$ assigning a number to each instance; $\kappa$ is required to be computable in
polynomial time [FG06, Definition 1.1]. The problem is **fixed-parameter tractable** if it is
decided in time $f(\kappa(x))\cdot|x|^{O(1)}$ for a computable $f$ [FG06, Definition 1.4].

An **fpt-reduction** from $(P, \kappa)$ to $(Q, \kappa')$ is a map $R$ such that
[FG06, Definition 2.1]

1. $x$ is a yes-instance of $P$ if and only if $R(x)$ is a yes-instance of $Q$;
2. $\kappa'(R(x)) \le g(\kappa(x))$ for a computable function $g$;
3. $R$ is computable in time $f(\kappa(x))\cdot|x|^{O(1)}$ for a computable $f$.

For a class $C$ of parameterized problems, $[C]^{\mathrm{fpt}}$ is the class of parameterized
problems that fpt-reduce to a member of $C$. A problem is **$C$-hard** if every member of $C$
fpt-reduces to it, and **$C$-complete** if it is moreover a member of $C$ [FG06, Chapter 2].

# Formalization Notes

**Problems** are the archive's `Lax888481.ParameterizedComplexity.Problem`: a set `Domain` of words
encoding instances, a predicate `Yes`, and the parameter `param`. Reductions and algorithms are
constrained on the domain only.

**The three conditions** of an fpt-reduction are separate definitions — `IsReduction`,
`ParamBounded` and `FptTimeOn` — so that a hardness proof establishes the construction and its
correctness, the parameter bound, and the running time one at a time. `IsFptReduction` bundles
them, and `P ≤ᶠᵖᵗ Q` (`FptReduces`, scoped notation: `open Lax496464.WH_A2_FptReductions`) states
that one exists. Polynomial-time reductions and the archive's strict fpt-reductions are
fpt-reductions by `WH_A5_Bridges`.

**Classes.** `Closure C` contains only parameterized problems (`IsParameterized`); `Hard` places no
such condition on the hard problem. An algorithm witnessing `FPT` writes `[1]` on yes-instances
and `[0]` on no-instances.
-/

namespace Lax496464.WH_A2_FptReductions

open Lax888481.ParameterizedComplexity (Problem)
open Lax496464.WH_A1_FptTime

/-- **Step 1 of a reduction: construction and correctness.** `R` maps instances of `P` to
instances of `Q`, yes-instances to yes-instances and no-instances to no-instances. -/
structure IsReduction (P Q : Problem) (R : List ℕ → List ℕ) : Prop where
  /-- Instances go to instances. -/
  maps_domain : ∀ x ∈ P.Domain, R x ∈ Q.Domain
  /-- Yes-instances go to yes-instances, and no-instances to no-instances. -/
  correct : ∀ x ∈ P.Domain, (P.Yes x ↔ Q.Yes (R x))

/-- **Step 2 of a reduction: the parameter bound.** The parameter of `R x` is at most a computable
function of the parameter of `x`. -/
def ParamBounded (P Q : Problem) (R : List ℕ → List ℕ) : Prop :=
  ∃ g : ℕ → ℕ, Computable g ∧ ∀ x ∈ P.Domain, Q.param (R x) ≤ g (P.param x)

/-- An **fpt-reduction** [FG06, Definition 2.1]: a reduction with a bounded parameter,
computable in fixed-parameter time (**step 3**) on the instances of `P`. -/
structure IsFptReduction (P Q : Problem) (R : List ℕ → List ℕ) : Prop where
  /-- Construction and correctness. -/
  reduction : IsReduction P Q R
  /-- The parameter bound. -/
  param_bounded : ParamBounded P Q R
  /-- The running time. -/
  fpt_time : FptTimeOn P.Domain P.param R

/-- `P` **fpt-reduces** to `Q`. -/
def FptReduces (P Q : Problem) : Prop := ∃ R, IsFptReduction P Q R

@[inherit_doc] scoped infix:50 " ≤ᶠᵖᵗ " => FptReduces

/-- `P` is a **parameterized problem**: its parameter is computable
in polynomial time on its instances [FG06, Definition 1.1]. -/
def IsParameterized (P : Problem) : Prop := PolyTimeOn P.Domain fun x => [P.param x]

open Classical in
/-- **FPT**: the parameterized problems decided in fixed-parameter time, the program writing `[1]`
on yes-instances and `[0]` on no-instances [FG06, Definition 1.4]. -/
def FPT : Set Problem :=
  {P | IsParameterized P ∧ FptTimeOn P.Domain P.param fun x => if P.Yes x then [1] else [0]}

/-- `[C]^fpt`: the parameterized problems that fpt-reduce to a member of `C`. -/
def Closure (C : Set Problem) : Set Problem :=
  {P | IsParameterized P ∧ ∃ Q ∈ C, P ≤ᶠᵖᵗ Q}

/-- `Q` is **`C`-hard**: every member of `C` fpt-reduces to it. -/
def Hard (C : Set Problem) (Q : Problem) : Prop := ∀ P ∈ C, P ≤ᶠᵖᵗ Q

/-- `Q` is **`C`-complete**: it belongs to `C` and is `C`-hard. -/
def Complete (C : Set Problem) (Q : Problem) : Prop := Q ∈ C ∧ Hard C Q

end Lax496464.WH_A2_FptReductions
