import Lax808846Proofs.Transfer
import Lax496464Proofs.WHierarchy.Machine.ReadTape

/-!
# The IMP+ Programs of the Two Clique Reductions: Definitions

The array `a` holds the word `x` (a CSR graph followed by `k`); `g_n` holds the number of vertices.

* `adjTest` sets `g_f` to `1` iff `g_v` occurs in the block of `g_u`;
* `countPass` sets `g_M` to the number of adjacent ordered pairs;
* `emitPass` writes the adjacent ordered pairs `u, v` in lexicographic order;
* `graphCom` writes the word of the graph structure;
* `formulaCom` writes the code of `clique_k` for `k = g_k`;
* `progWD` and `progMC` are the two whole programs.

All scalars introduced here are prefixed `g_`.
-/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs

open Lax808846Proofs.Imp

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-! ### The adjacency test -/

/-- `if a[3 + n + lo + t] = v then f := 1`. -/
def adjStep : Com :=
  .ite (.eq (.get "a" (.add (.add (.add (.lit 3) (V "g_n")) (V "g_lo")) (V "g_t"))) (V "g_v"))
    (.assign "g_f" (.lit 1)) .skip

/-- The body of the scan of the block. -/
def adjBody : Com := .seq adjStep (bump "g_t")

/-- The scan of the block of `g_u`. -/
def adjLoop : Com := .seq (.assign "g_t" (.lit 0)) (.while (.lt (V "g_t") (V "g_d")) adjBody)

/-- Reading the block bounds. -/
def adjPrep : Com :=
  .seq (.assign "g_lo" (.get "a" (.add (.lit 2) (V "g_u"))))
  (.seq (.assign "g_hi" (.get "a" (.add (.lit 3) (V "g_u"))))
  (.seq (.assign "g_d" (.sub (V "g_hi") (V "g_lo")))
        (.assign "g_f" (.lit 0))))

/-- **The adjacency test.** -/
def adjTest : Com := .seq adjPrep adjLoop

/-! ### The two passes over the pairs -/

/-- Inner body of the counting pass. -/
def countBody : Com := .seq adjTest (.seq (.assign "g_M" (.add (V "g_M") (V "g_f"))) (bump "g_v"))

/-- Inner loop of the counting pass. -/
def countRow : Com := .seq (.assign "g_v" (.lit 0)) (.while (.lt (V "g_v") (V "g_n")) countBody)

/-- Outer loop of the counting pass. -/
def countLoop : Com :=
  .seq (.assign "g_u" (.lit 0)) (.while (.lt (V "g_u") (V "g_n")) (.seq countRow (bump "g_u")))

/-- **The counting pass.** -/
def countPass : Com := .seq (.assign "g_M" (.lit 0)) countLoop

/-- Write `u, v` if the pair is adjacent. -/
def emitIf : Com := .ite (.eq (V "g_f") (.lit 1)) (.seq (.write (V "g_u")) (.write (V "g_v"))) .skip

/-- Inner body of the emitting pass. -/
def emitBody : Com := .seq adjTest (.seq emitIf (bump "g_v"))

/-- Inner loop of the emitting pass. -/
def emitRow : Com := .seq (.assign "g_v" (.lit 0)) (.while (.lt (V "g_v") (V "g_n")) emitBody)

/-- **The emitting pass.** -/
def emitPass : Com :=
  .seq (.assign "g_u" (.lit 0)) (.while (.lt (V "g_u") (V "g_n")) (.seq emitRow (bump "g_u")))

/-- **The word of the graph structure**: `1, 2, n, M`, the pairs. -/
def graphCom : Com :=
  .seq (.write (.lit 1))
  (.seq (.write (.lit 2))
  (.seq (.write (V "g_n"))
  (.seq countPass
  (.seq (.write (V "g_M")) emitPass))))

/-! ### The formula -/

/-- One quantifier `6, i`. -/
def quantBody : Com := .seq (.write (.lit 6)) (.seq (.write (V "g_i")) (bump "g_i"))

/-- The quantifier block. -/
def quantLoop : Com := .seq (.assign "g_i" (.lit 0)) (.while (.lt (V "g_i") (V "g_k")) quantBody)

/-- Write the values of a list of expressions. -/
def writeExprs : List Expr → Com
  | [] => .skip
  | e :: es => .seq (.write e) (writeExprs es)

/-- The code of the item of the pair `i, j`. -/
def itemCom : Com :=
  writeExprs [.lit 4, .lit 4, .lit 3, .lit 2, V "g_i", V "g_j", .lit 0, .lit 0, .lit 2, V "g_i",
    V "g_j"]

/-- Write the item if `i < j`. -/
def itemIf : Com := .ite (.lt (V "g_i") (V "g_j")) itemCom .skip

/-- Inner loop over `j`. -/
def pairRow : Com :=
  .seq (.assign "g_j" (.lit 0)) (.while (.lt (V "g_j") (V "g_k")) (.seq itemIf (bump "g_j")))

/-- Outer loop over `i`. -/
def pairLoop : Com :=
  .seq (.assign "g_i" (.lit 0)) (.while (.lt (V "g_i") (V "g_k")) (.seq pairRow (bump "g_i")))

/-- **The code of `clique_k`.** -/
def formulaCom : Com :=
  .seq quantLoop (.seq pairLoop (.seq (.write (.lit 2)) (.seq (.write (.lit 0)) (.write (.lit 0)))))

/-! ### The whole programs -/

/-- Read `n` and the parameter. -/
def headCom : Com :=
  .seq (.assign "g_n" (.get "a" (.lit 0)))
    (.assign "g_k" (.get "a" (.sub (V "rt_n") (.lit 1))))

/-- **The program of `p-Clique ≤ p-WD_clique`.** -/
def progWD : Com :=
  .seq Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape (.seq headCom (.seq graphCom (.write (V "g_k"))))

/-- Write a fixed word. -/
def writeList (l : List ℕ) : Com := writeExprs (l.map .lit)

/-- The choice of the three branches of the reduction to model checking. -/
def branchMC : Com :=
  .ite (.eq (V "g_k") (.lit 0)) (writeList [0, 1, 6, 0, 2, 0, 0])
    (.ite (.lt (V "g_n") (V "g_k")) (writeList [0, 0, 6, 0, 2, 0, 0]) (.seq graphCom formulaCom))

/-- **The program of `p-Clique ≤ p-MC(Σ_1)`.** -/
def progMC : Com := .seq Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape (.seq headCom branchMC)

/-- The scalars of the adjacency test. -/
def adjVars : List String := ["g_lo", "g_hi", "g_d", "g_f", "g_t"]

/-- The scalars the programs assign. -/
def progVars : List String :=
  ["rt_n", "rt_i", "rt_v", "g_n", "g_k", "g_lo", "g_hi", "g_d", "g_f", "g_t", "g_M", "g_u", "g_v",
    "g_i", "g_j"]

end Lax496464Proofs.WHierarchy.Reductions.CliqueLogic.ProgDefs
