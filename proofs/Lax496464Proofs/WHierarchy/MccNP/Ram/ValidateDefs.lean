import Lax808846Proofs.Tactic

/-!
# The Validator: Definitions

`validate` reads `L` and array `a` and sets `ok` to `1` if the word is `Shape.Valid` and to `0`
otherwise. It is total on every word, never stores into an array, and assigns only `ok` and scalars
prefixed `v_`; its cost is `Kval x = 400 * (|x| + 1)`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Validate

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.bin .add (V s) (.lit 1))
abbrev fail : Com := .assign "ok" (.lit 0)

/-- One step of the run of ones from the index variable `i`. -/
def runBody (i : String) : Com :=
  .ite (.lt (V i) (V "L"))
    (.ite (.eq (.get "a" (V i)) (.lit 1)) (bump i) (.assign "v_go" (.lit 0)))
    (.assign "v_go" (.lit 0))

/-- Run of ones from the index variable `i`: on exit `i` is the first index `≥` its start
holding a non-one (or `"L"`). -/
def runLoop (i : String) : Com :=
  .while (.eq (V "v_go") (.lit 1)) (runBody i)

/-- `i := start; go := 1;` then the run of ones from `i`. -/
def runFrom (i : String) (start : Expr) : Com :=
  .seq (.assign i start) (.seq (.assign "v_go" (.lit 1)) (runLoop i))

/-- The cell `(u, w)` with `t = u * n + w`, and its transpose: `c` and `d`. -/
def matRead : Com :=
  .seq (.assign "v_u" (.bin .div (V "v_t") (V "v_n")))
  (.seq (.assign "v_w" (.bin .sub (V "v_t") (.bin .mul (V "v_u") (V "v_n"))))
  (.seq (.assign "v_c" (.get "a" (.bin .add (V "v_n") (.bin .add (.lit 1) (V "v_t")))))
        (.assign "v_d" (.get "a" (.bin .add (.bin .add (V "v_n") (.lit 1))
          (.bin .add (.bin .mul (V "v_w") (V "v_n")) (V "v_u")))))))

/-- The gates: entry `≤ 1`, symmetric, zero on the diagonal. -/
def matGates : Com :=
  .seq (.ite (.lt (V "v_c") (.lit 2)) .skip fail)
  (.seq (.ite (.eq (V "v_c") (V "v_d")) .skip fail)
        (.ite (.eq (V "v_u") (V "v_w")) (.ite (.eq (V "v_c") (.lit 0)) .skip fail) .skip))

/-- One cell of the matrix, `t = u * n + w`. -/
def matBody : Com := .seq matRead (.seq matGates (bump "v_t"))

def matLoop : Com :=
  .seq (.assign "v_t" (.lit 0)) (.while (.lt (V "v_t") (V "v_nn")) matBody)

/-- After the matrix: the run of ones `k`, then `k` ends the word and the last entry is `0`. -/
def finalGate : Com :=
  .ite (.eq (.bin .add (V "v_k") (.lit 1)) (V "L"))
    (.ite (.eq (.get "a" (V "v_k")) (.lit 0)) .skip fail)
    fail

/-- The rest of the checks once the matrix fits and `a[n] = 0`. -/
def afterMat : Com :=
  .seq matLoop (.seq (runFrom "v_k" (V "v_s")) finalGate)

/-- `n < L`, `a[n] = 0` -/
def checkA : Com := .ite (.eq (.get "a" (V "v_n")) (.lit 0)) afterMat fail

/-- The matrix fits: `n + 1 + n * n < L`. -/
def checkS : Com := .ite (.lt (V "v_s") (V "L")) checkA fail

/-- The validator. -/
def validate : Com :=
  .seq (.assign "ok" (.lit 1))
  (.seq (runFrom "v_n" (.lit 0))
  (.seq (.assign "v_nn" (.bin .mul (V "v_n") (V "v_n")))
  (.seq (.assign "v_s" (.bin .add (.bin .add (V "v_n") (.lit 1)) (V "v_nn")))
    checkS)))

/-- The value bound. -/
def Bval (x : List ℕ) : ℕ := (x.length + 2) ^ 2

/-- The cost bound. -/
def Kval (x : List ℕ) : ℕ := 400 * (x.length + 1)

end Lax496464Proofs.WHierarchy.MccNP.Validate
