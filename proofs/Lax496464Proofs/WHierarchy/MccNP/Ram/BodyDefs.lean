import Lax808846Proofs.Transfer
import Lax496464Proofs.WHierarchy.MccNP.Shape

/-!
# The IMP+ Program of the Reduction: Definitions

`body` writes the word of the multicoloured graph of the instance held in array `a`; `readStruct`
fills `a` from the input tape using the structure of the word. The scalars of both are prefixed
`b_`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs

open Lax808846Proofs.Imp

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- `while a[off + cnt] = 1 do cnt := cnt + 1`. -/
def runOnes (cnt off : String) : Com :=
  .while (.eq (.get "a" (.add (V off) (V cnt))) (.lit 1)) (bump cnt)

/-- The division step of the adjacency test: `b_cs, b_us, b_ct, b_ut` are the colour and the
vertex of the copies `b_s` and `b_t`. -/
def adjPrep : Com :=
  .seq (.assign "b_cs" (.div (V "b_s") (V "b_n")))
  (.seq (.assign "b_us" (.sub (V "b_s") (.mul (V "b_cs") (V "b_n"))))
  (.seq (.assign "b_ct" (.div (V "b_t") (V "b_n")))
        (.assign "b_ut" (.sub (V "b_t") (.mul (V "b_ct") (V "b_n"))))))

/-- The comparison step: `b_f := 1` iff the colours differ, the vertices differ and the matrix
entry is `0`. -/
def adjTest : Com :=
  .seq (.assign "b_f" (.lit 0))
   (.ite (.eq (V "b_cs") (V "b_ct")) .skip
    (.ite (.eq (V "b_us") (V "b_ut")) .skip
     (.ite (.eq (.get "a" (.add (.add (V "b_base") (.mul (V "b_us") (V "b_n"))) (V "b_ut")))
         (.lit 0)) (.assign "b_f" (.lit 1)) .skip)))

/-- Sets `b_f` to `1` if the copies `b_s` and `b_t` are adjacent in the construction, else `0`. -/
def adjCom : Com := .seq adjPrep adjTest

/-- `b_d :=` the degree of `b_s`. -/
def rowCount : Com :=
  .seq (.assign "b_d" (.lit 0))
   (.seq (.assign "b_t" (.lit 0))
    (.while (.lt (V "b_t") (V "b_N"))
     (.seq adjCom (.seq (.assign "b_d" (.add (V "b_d") (V "b_f"))) (bump "b_t")))))

/-- Write `b_t` if `b_f = 1`. -/
def emitIf : Com := .ite (.eq (V "b_f") (.lit 1)) (.write (V "b_t")) .skip

/-- Writes the neighbours of `b_s` in increasing order. -/
def rowEmit : Com :=
  .seq (.assign "b_t" (.lit 0))
   (.while (.lt (V "b_t") (V "b_N"))
    (.seq adjCom (.seq emitIf (bump "b_t"))))

/-- `b_M :=` the sum of the degrees. -/
def pass1 : Com :=
  .seq (.assign "b_M" (.lit 0))
   (.seq (.assign "b_s" (.lit 0))
    (.while (.lt (V "b_s") (V "b_N"))
     (.seq rowCount (.seq (.assign "b_M" (.add (V "b_M") (V "b_d"))) (bump "b_s")))))

/-- Writes the running offsets after each vertex. -/
def pass2 : Com :=
  .seq (.assign "b_off" (.lit 0))
   (.seq (.assign "b_s" (.lit 0))
    (.while (.lt (V "b_s") (V "b_N"))
     (.seq rowCount (.seq (.assign "b_off" (.add (V "b_off") (V "b_d")))
       (.seq (.write (V "b_off")) (bump "b_s"))))))

/-- Writes the targets. -/
def pass3 : Com :=
  .seq (.assign "b_s" (.lit 0))
   (.while (.lt (V "b_s") (V "b_N")) (.seq rowEmit (bump "b_s")))

/-- Writes the colours. -/
def pass4 : Com :=
  .seq (.assign "b_s" (.lit 0))
   (.while (.lt (V "b_s") (V "b_N"))
    (.seq (.write (.div (V "b_s") (V "b_n"))) (bump "b_s")))

/-- The header: `n`, `base = n + 1`, `K0 = base + n²`, `k`, `N = k n`. -/
def header : Com :=
  .seq (.assign "b_o" (.lit 0))
  (.seq (.assign "b_n" (.lit 0))
  (.seq (runOnes "b_n" "b_o")
  (.seq (.assign "b_base" (.add (V "b_n") (.lit 1)))
  (.seq (.assign "b_K0" (.add (V "b_base") (.mul (V "b_n") (V "b_n"))))
  (.seq (.assign "b_o" (V "b_K0"))
  (.seq (.assign "b_k" (.lit 0))
  (.seq (runOnes "b_k" "b_o")
        (.assign "b_N" (.mul (V "b_k") (V "b_n"))))))))))

/-- **The body**: array `a` holds the word; the word of the construction is written. -/
def body : Com :=
  .seq header
  (.seq pass1
  (.seq (.write (V "b_N"))
  (.seq (.write (.div (V "b_M") (.lit 2)))
  (.seq (.write (.lit 0))
  (.seq pass2
  (.seq pass3
  (.seq pass4 (.write (V "b_k")))))))))

/-- `read v; while v = 1 do a[i] := 1; i := i + 1; read v`: reads a run of ones and its terminator. -/
def onesRead : Com :=
  .seq (.read "b_v")
   (.while (.eq (V "b_v") (.lit 1))
    (.seq (.store "a" (V "b_i") (.lit 1)) (.seq (bump "b_i") (.read "b_v"))))

/-- Reads the `n²` matrix entries into `a[b_i], …, a[b_e - 1]`. -/
def matLoop : Com :=
  .while (.lt (V "b_i") (V "b_e"))
   (.seq (.read "b_v") (.seq (.store "a" (V "b_i") (V "b_v")) (bump "b_i")))

/-- **The reader**: fills the array `a` with the word from the bare input tape, using the word's own
structure (`1^n 0`, `n²` entries, `1^k 0`). -/
def readStruct : Com :=
  .seq (.assign "b_i" (.lit 0))
  (.seq onesRead
  (.seq (.assign "b_rn" (V "b_i"))
  (.seq (.assign "b_i" (.add (V "b_i") (.lit 1)))
  (.seq (.assign "b_e" (.add (V "b_i") (.mul (V "b_rn") (V "b_rn"))))
  (.seq matLoop onesRead)))))

/-- The scalars `readStruct` may assign. -/
def readVars : List String := ["b_i", "b_v", "b_rn", "b_e"]

/-- The scalars `body` may assign. -/
def bodyVars : List String :=
  ["b_o", "b_n", "b_base", "b_K0", "b_k", "b_N", "b_M", "b_s", "b_t", "b_f", "b_d", "b_off",
    "b_cs", "b_us", "b_ct", "b_ut"]

/-- The number of entries of the targets array of the construction on `x`. -/
noncomputable def Mx (x : List ℕ) : ℕ :=
  (Lax496464.WH_F2_MccConstruction.targets (Shape.decode x)).length

/-- The bound on every value `body` computes (it must be `< B`). -/
noncomputable def Bbody (x : List ℕ) : ℕ := x.length + Shape.kOf x * Shape.order x + Mx x + 2

/-- The constant of the cost bound. -/
def bodyC : ℕ := 1200

/-- The cost bound of `body`. -/
def Kbody (x : List ℕ) : ℕ := bodyC * (Shape.kOf x + 1) ^ 2 * (x.length + 1)

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyDefs
