import Lax496464.WH_B2_FirstOrder
import Lax888481.ParameterizedComplexity

/-!
---
title: Model Checking and Weighted Fagin Definability
type: definition
---
The two families of parameterized problems that define the hierarchies.

**Model checking** $p\text{-MC}(\Phi)$ for a class $\Phi$ of formulas. *Instance:* a structure
$\mathcal A$ and a formula $\varphi \in \Phi$. *Parameter:* $|\varphi|$. *Question:* is
$\varphi(\mathcal A) \ne \emptyset$, that is, do some elements of $\mathcal A$ satisfy $\varphi$
when assigned to its free variables? [FG06, Section 4.2]

**Weighted Fagin definability** $p\text{-WD}_\varphi$ for a formula $\varphi(X)$ with a free relation
variable $X$ of arity $s$. *Instance:* a structure $\mathcal A$ and $k \in \mathbb N$.
*Parameter:* $k$. *Question:* is there a relation $S \subseteq A^s$ with $|S| = k$ such that
$\mathcal A \models \varphi(S)$? [FG06, p. 95]

# Formalization Notes

**Words.** An instance of model checking is the word of the structure followed by the word of the
formula; an instance of weighted definability is the word of the structure followed by $k$. Both
parts are self-delimiting, so a word determines them. The parameter is the size of the formula, or
the last entry.

**Model checking.** The formula does not use the relation variable, and it is false in a structure
whose vocabulary it does not fit. Its free variables range over the universe. The class $\Phi$
restricts the instances only: the yes-instances of $p\text{-MC}(\Phi)$ are those of
$p\text{-MC}(\Phi')$ for every $\Phi' \supseteq \Phi$ that lie in the smaller domain.

**Weighted definability.** The formula of $p\text{-WD}_\varphi$ is fixed, so each formula and arity
give one problem. The formulas defining the hierarchies are sentences, evaluated under an arbitrary
assignment (here the one sending every variable to $0$). A relation of $k$ tuples is a finite set
of lists of length $s$ over the universe. A formula that does not fit the vocabulary has no
witness.
-/

namespace Lax496464.WH_B3_LogicProblems

open Lax496464.WH_B1_Structures Lax496464.WH_B2_FirstOrder
open Lax888481.ParameterizedComplexity (Problem)

/-- The word `x` is the word of the structure `A` followed by the word of the formula `φ`. -/
def EncodesMC (x : List ℕ) (A : Structure) (φ : Formula) : Prop :=
  ∃ y, Encodes y A ∧ x = y ++ φ.encode

/-- `φ(A) ≠ ∅`: the formula fits the vocabulary of `A`, does not use the relation variable, and is
satisfied by some assignment of universe elements to its free variables. -/
def Models (A : Structure) (φ : Formula) : Prop :=
  φ.Fits A.arities 0 ∧ φ.NoSetVar ∧
    ∃ ρ : Assignment, (∀ v ∈ φ.freeVars, ρ v < A.size) ∧ Sat A ∅ φ ρ

open Classical in
/-- The parameter of a model-checking word: the size of its formula (`0` on other words). -/
noncomputable def mcParam (x : List ℕ) : ℕ :=
  if h : ∃ p : Structure × Formula, EncodesMC x p.1 p.2 then (Classical.choose h).2.size else 0

/-- **`p-MC(Φ)`**, parameterized model checking for the class `Φ` of formulas. -/
noncomputable def pMC (Φ : Set Formula) : Problem where
  Domain := {x | ∃ A φ, EncodesMC x A φ ∧ φ ∈ Φ ∧ φ.NoSetVar}
  Yes x := ∃ A φ, EncodesMC x A φ ∧ Models A φ
  param := mcParam

/-- The word `x` is the word of the structure `A` followed by the number `k`. -/
def EncodesWD (x : List ℕ) (A : Structure) (k : ℕ) : Prop :=
  ∃ y, Encodes y A ∧ x = y ++ [k]

/-- A **witness** of weight `k` for `φ(X)` in `A`, with `X` of arity `s`: a set of `k` tuples of
length `s` over the universe that, taken as the value of `X`, makes `φ` true. -/
def Witness (A : Structure) (φ : Formula) (s k : ℕ) : Prop :=
  φ.Fits A.arities s ∧ ∃ S : Finset (List ℕ), S.card = k ∧
    (∀ t ∈ S, t.length = s ∧ ∀ a ∈ t, a < A.size) ∧ Sat A ↑S φ fun _ => 0

/-- **`p-WD_φ`**, weighted Fagin definability of `φ(X)` with `X` of arity `s`. -/
def pWD (φ : Formula) (s : ℕ) : Problem where
  Domain := {x | ∃ A k, EncodesWD x A k}
  Yes x := ∃ A k, EncodesWD x A k ∧ Witness A φ s k
  param x := x.getLast?.getD 0

end Lax496464.WH_B3_LogicProblems
