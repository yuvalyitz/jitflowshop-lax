import Lax496464.WH_B1_Structures

/-!
---
title: First-order formulas and the classes Σ_t and Π_t
type: definition
---
First-order formulas over a relational vocabulary, with equality and one free *relation variable*
$X$; their satisfaction in a structure; their free variables; and the syntactic classes that define
the hierarchies [FG06, Section 4.2]:

* $\Sigma_0 = \Pi_0$ is the class of quantifier-free formulas; $\Sigma_{t+1}$ consists of the
  formulas $\exists x_1 \dots \exists x_k\,\varphi$ with $\varphi \in \Pi_t$, and $\Pi_{t+1}$ of the
  formulas $\forall x_1 \dots \forall x_k\,\varphi$ with $\varphi \in \Sigma_t$;
* a formula is *positive* if it contains no negation symbol, as in $\Sigma_1^+$;
* a formula is *at most $u$-ary* if every relation symbol in it has arity at most $u$, as in
  $\Sigma_1[2]$.

# Formalization notes

**Syntax.** Variables and relation symbols are numbers: `rel i xs` is the atom
$R_i\,x_{a_1}\dots x_{a_r}$ for symbol $i$ and the variables listed in `xs`, and `setVar xs` is the
atom $X x_{a_1}\dots x_{a_s}$. The connectives are negation, conjunction and disjunction;
$\varphi \to \psi$ abbreviates $\neg\varphi \vee \psi$ (`Formula.imp`).

**Semantics.** A formula is evaluated under an assignment of numbers to variables and an
interpretation $S$ of $X$ as a set of tuples; quantifiers range over the universe. A formula *fits*
a vocabulary if every symbol it mentions belongs to the vocabulary and is applied to the right
number of arguments, and every atom of $X$ has the declared arity $s$. The problems built on
formulas treat a formula that does not fit as false.

**Free variables and sentences** are syntactic (`Formula.freeVars`, `IsSentence`), so whether a
concrete formula is a sentence is decided by computation.

**The classes.** Quantifier blocks may be empty, so $\Sigma_t \cup \Pi_t \subseteq \Sigma_{t+1}
\cap \Pi_{t+1}$. Atoms of the relation variable are quantifier-free.

**Size and words.** $|\varphi|$ counts symbols: an atom counts one plus its number of arguments, an
equation three, a connective one, a quantifier two; this is within a constant factor of the length
of $\varphi$ as a string. The word of a formula (`Formula.encode`) is in prefix notation and
self-delimiting, so a formula may be followed by further entries.
-/

namespace Lax496464.WH_B2_FirstOrder

open Lax496464.WH_B1_Structures

/-- First-order formulas, with atoms for the vocabulary's relation symbols and for one free relation
variable. -/
inductive Formula
  /-- The atom `R_i x_{a_1} … x_{a_r}`. -/
  | rel (i : ℕ) (xs : List ℕ)
  /-- The atom `X x_{a_1} … x_{a_s}` of the free relation variable. -/
  | setVar (xs : List ℕ)
  /-- The equation `x = y`. -/
  | eq (x y : ℕ)
  /-- Negation. -/
  | neg (φ : Formula)
  /-- Conjunction. -/
  | and (φ ψ : Formula)
  /-- Disjunction. -/
  | or (φ ψ : Formula)
  /-- Existential quantification. -/
  | ex (x : ℕ) (φ : Formula)
  /-- Universal quantification. -/
  | all (x : ℕ) (φ : Formula)

/-- The implication `φ → ψ`, an abbreviation of `¬φ ∨ ψ`. -/
def Formula.imp (φ ψ : Formula) : Formula := .or (.neg φ) ψ

/-- An assignment of universe elements to variables. -/
abbrev Assignment := ℕ → ℕ

/-- The assignment `ρ` changed to send `x` to `a`. -/
def Assignment.update (ρ : Assignment) (x a : ℕ) : Assignment :=
  fun y => if y = x then a else ρ y

/-- **Satisfaction.** The formula holds in `A`, with the relation variable interpreted as `S`,
under the assignment `ρ`. -/
def Sat (A : Structure) (S : Set (List ℕ)) : Formula → Assignment → Prop
  | .rel i xs, ρ => xs.map ρ ∈ A.rel i
  | .setVar xs, ρ => xs.map ρ ∈ S
  | .eq x y, ρ => ρ x = ρ y
  | .neg φ, ρ => ¬ Sat A S φ ρ
  | .and φ ψ, ρ => Sat A S φ ρ ∧ Sat A S ψ ρ
  | .or φ ψ, ρ => Sat A S φ ρ ∨ Sat A S ψ ρ
  | .ex x φ, ρ => ∃ a, a < A.size ∧ Sat A S φ (ρ.update x a)
  | .all x φ, ρ => ∀ a, a < A.size → Sat A S φ (ρ.update x a)

/-- The free (individual) variables of a formula. -/
def Formula.freeVars : Formula → Finset ℕ
  | .rel _ xs => xs.toFinset
  | .setVar xs => xs.toFinset
  | .eq x y => {x, y}
  | .neg φ => φ.freeVars
  | .and φ ψ => φ.freeVars ∪ ψ.freeVars
  | .or φ ψ => φ.freeVars ∪ ψ.freeVars
  | .ex x φ => φ.freeVars.erase x
  | .all x φ => φ.freeVars.erase x

/-- The formula is a **sentence**: it has no free individual variables (the relation variable may
occur). -/
def IsSentence (φ : Formula) : Prop := φ.freeVars = ∅

/-- The formula fits the vocabulary `arities`, and uses the relation variable at arity `s`. -/
def Formula.Fits (arities : List ℕ) (s : ℕ) : Formula → Prop
  | .rel i xs => i < arities.length ∧ xs.length = arities.getD i 0
  | .setVar xs => xs.length = s
  | .eq _ _ => True
  | .neg φ => φ.Fits arities s
  | .and φ ψ => φ.Fits arities s ∧ ψ.Fits arities s
  | .or φ ψ => φ.Fits arities s ∧ ψ.Fits arities s
  | .ex _ φ => φ.Fits arities s
  | .all _ φ => φ.Fits arities s

/-- The formula does not use the relation variable. -/
def Formula.NoSetVar : Formula → Prop
  | .setVar _ => False
  | .rel _ _ => True
  | .eq _ _ => True
  | .neg φ => φ.NoSetVar
  | .and φ ψ => φ.NoSetVar ∧ ψ.NoSetVar
  | .or φ ψ => φ.NoSetVar ∧ ψ.NoSetVar
  | .ex _ φ => φ.NoSetVar
  | .all _ φ => φ.NoSetVar

/-- The formula is quantifier-free. -/
def Formula.IsQF : Formula → Prop
  | .ex _ _ => False
  | .all _ _ => False
  | .neg φ => φ.IsQF
  | .and φ ψ => φ.IsQF ∧ ψ.IsQF
  | .or φ ψ => φ.IsQF ∧ ψ.IsQF
  | _ => True

/-- The formula is **positive**: it contains no negation symbol. -/
def Formula.IsPositive : Formula → Prop
  | .neg _ => False
  | .and φ ψ => φ.IsPositive ∧ ψ.IsPositive
  | .or φ ψ => φ.IsPositive ∧ ψ.IsPositive
  | .ex _ φ => φ.IsPositive
  | .all _ φ => φ.IsPositive
  | _ => True

/-- Every relation symbol occurring in the formula is applied to at most `u` variables. -/
def Formula.ArityAtMost (u : ℕ) : Formula → Prop
  | .rel _ xs => xs.length ≤ u
  | .neg φ => φ.ArityAtMost u
  | .and φ ψ => φ.ArityAtMost u ∧ ψ.ArityAtMost u
  | .or φ ψ => φ.ArityAtMost u ∧ ψ.ArityAtMost u
  | .ex _ φ => φ.ArityAtMost u
  | .all _ φ => φ.ArityAtMost u
  | _ => True

/-- A block of existential quantifiers over the variables `xs`. -/
def Formula.exBlock (xs : List ℕ) (φ : Formula) : Formula := xs.foldr Formula.ex φ

/-- A block of universal quantifiers over the variables `xs`. -/
def Formula.allBlock (xs : List ℕ) (φ : Formula) : Formula := xs.foldr Formula.all φ

/-- `Alt true t φ` is `φ ∈ Σ_t` and `Alt false t φ` is `φ ∈ Π_t`: `t` alternating blocks of
quantifiers, the first existential or universal respectively, in front of a quantifier-free
formula. -/
def Alt : Bool → ℕ → Formula → Prop
  | _, 0, φ => φ.IsQF
  | true, t + 1, φ => ∃ xs ψ, φ = Formula.exBlock xs ψ ∧ Alt false t ψ
  | false, t + 1, φ => ∃ xs ψ, φ = Formula.allBlock xs ψ ∧ Alt true t ψ

/-- `φ ∈ Σ_t`. -/
abbrev IsSigma (t : ℕ) (φ : Formula) : Prop := Alt true t φ

/-- `φ ∈ Π_t`. -/
abbrev IsPi (t : ℕ) (φ : Formula) : Prop := Alt false t φ

/-- The size `|φ|` of a formula: the number of its symbols. -/
def Formula.size : Formula → ℕ
  | .rel _ xs => xs.length + 1
  | .setVar xs => xs.length + 1
  | .eq _ _ => 3
  | .neg φ => φ.size + 1
  | .and φ ψ => φ.size + ψ.size + 1
  | .or φ ψ => φ.size + ψ.size + 1
  | .ex _ φ => φ.size + 2
  | .all _ φ => φ.size + 2

/-- The word of a formula, in prefix notation. -/
def Formula.encode : Formula → List ℕ
  | .rel i xs => 0 :: i :: xs.length :: xs
  | .setVar xs => 1 :: xs.length :: xs
  | .eq x y => [2, x, y]
  | .neg φ => 3 :: φ.encode
  | .and φ ψ => 4 :: (φ.encode ++ ψ.encode)
  | .or φ ψ => 5 :: (φ.encode ++ ψ.encode)
  | .ex x φ => 6 :: x :: φ.encode
  | .all x φ => 7 :: x :: φ.encode

end Lax496464.WH_B2_FirstOrder
