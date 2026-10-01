import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs
import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax

/-!
# The IMP+ program of `p-WD_φ ≤ p-WSat(monotone)`: definitions

The setup is the one of `Lemmas/WDToWSat` (read the tape, the header, the fit test, the block
positions, `L`, the elements `U`, powers of `n = |U|`), run for the data `wd Dt` of that reduction
with the same `s`, `r` and relation atoms. Then:

* constants: `N = n^s`, `M = N + 1`, `C = M^D`, `k+1`, `W = (k+1)^D`, `D`, `D·D`, `2C`, `W·C·Q`;
* the number of clauses `W + W·C·W·C + P`;
* phase B: the block clauses; phase X: the clauses of pairs of blocks with values (the slots of the
  two blocks decoded into `bd1, vd1, bd2, vd2`, the conflict test `cfCom`); phase M: for every
  universal assignment `za` (its digits into `od[q..r)`), the clause of the blocks with values
  that make `ψ` true under some existential assignment `zb` (its digits into `od[0..q)`), evaluated
  by `evalCom`, which follows `Eval.ev` (value in `w_f`, the undecided flag in `g_und`);
* `W`.

Scalars of the new part are prefixed `g_`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList headCom fitCom boCom LCom uCom
  powCom relCom atomCom codeCom noCom)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax

/-- The data of the setup of `Lemmas/WDToWSat`. -/
def wd (Dt : Data) : Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output.Data :=
  ⟨Dt.s, Dt.r, [], Dt.rels, Dt.sfit⟩

/-! ### Generic pieces -/

/-- The `c` lowest base-`bs` digits of `w` into `arr[j], …, arr[j+c-1]` (destroying `w`). -/
def decG (arr w bs : String) : ℕ → ℕ → Com
  | _, 0 => .skip
  | j, c + 1 => .seq (.store arr (.lit j) (.sub (V w) (.mul (.div (V w) (V bs)) (V bs))))
      (.seq (.assign w (.div (V w) (V bs))) (decG arr w bs (j + 1) c))

/-- `dst := bs ^ e`. -/
def powG (dst bs : String) : ℕ → Com
  | 0 => .assign dst (.lit 1)
  | e + 1 => .seq (powG dst bs e) (.assign dst (.mul (V dst) (V bs)))

/-- A counted loop `x := 0; while x < m do (body; x := x + 1)`. -/
def loopC (x m : String) (body : Com) : Com :=
  .seq (.assign x (.lit 0)) (.while (.lt (V x) (V m)) (.seq body (bump x)))

/-- `2 · (1 + b + W · e)`, the code of the positive literal `Z(b, e)`. -/
def litE (b e : String) : Expr :=
  .mul (.lit 2) (.add (.add (.lit 1) (V b)) (.mul (V "g_W") (V e)))

/-- `j := i / D; j2 := i - j·D`. -/
def splitI : Com :=
  .seq (.assign "g_j" (.div (V "g_i") (V "g_D")))
    (.assign "g_j2" (.sub (V "g_i") (.mul (V "g_j") (V "g_D"))))

/-- Set the flag `f` if the condition holds. -/
def setIf (b : Cond) (f : String) : Com := .ite b (.assign f (.lit 1)) .skip

/-! ### The constants -/

/-- The constants of the formula. -/
def constCom (D : ℕ) : Com :=
  seqList [.assign "g_NT" (V "w_PS"), .assign "g_M" (.add (V "g_NT") (.lit 1)),
    powG "g_C" "g_M" D, .assign "g_k1" (.add (V "w_k") (.lit 1)), powG "g_W" "g_k1" D,
    .assign "g_D" (.lit D), .assign "g_DD" (.lit (D * D)),
    .assign "g_C2" (.mul (.lit 2) (V "g_C")),
    .assign "g_WCQ" (.mul (.mul (V "g_W") (V "g_C")) (V "g_Q"))]

/-- The number of clauses. -/
def countCom : Com :=
  .write (.add (.add (V "g_W") (.mul (.mul (.mul (V "g_W") (V "g_C")) (V "g_W")) (V "g_C")))
    (V "g_P"))

/-! ### Phase B -/

/-- The clause of block `g_b`. -/
def bBody : Com :=
  .seq (.write (V "g_C")) (loopC "g_e" "g_C" (.write (litE "g_b" "g_e")))

/-- **Phase B.** -/
def phaseB : Com := loopC "g_b" "g_W" bBody

/-! ### Phase X -/

/-- One pair of slots of the conflict test. -/
def cfTest : Com :=
  .ite (.lt (.get "bd1" (V "g_j")) (V "w_k"))
    (.seq (setIf (.lt (V "g_NT") (.add (.get "vd1" (V "g_j")) (.lit 1))) "g_cf")
      (.ite (.lt (.get "bd2" (V "g_j2")) (V "w_k"))
        (.seq
          (.ite (.eq (.get "bd1" (V "g_j")) (.get "bd2" (V "g_j2")))
            (.ite (.eq (.get "vd1" (V "g_j")) (.get "vd2" (V "g_j2"))) .skip
              (.assign "g_cf" (.lit 1))) .skip)
          (.ite (.lt (.get "bd1" (V "g_j")) (.get "bd2" (V "g_j2")))
            (setIf (.lt (.get "vd2" (V "g_j2")) (.add (.get "vd1" (V "g_j")) (.lit 1))) "g_cf")
            .skip))
        .skip))
    .skip

/-- **The conflict test** of the blocks with values in `bd1, vd1, bd2, vd2`, into `g_cf`. -/
def cfCom : Com := .seq (.assign "g_cf" (.lit 0)) (loopC "g_i" "g_DD" (.seq splitI cfTest))

/-- A literal of the first half of a pair clause. -/
def lit1 : Com :=
  .ite (.eq (V "g_cf") (.lit 0)) (.write (litE "g_b1" "g_e"))
    (.ite (.eq (V "g_e") (V "g_v1")) (.write (.lit 0)) (.write (litE "g_b1" "g_e")))

/-- A literal of the second half. -/
def lit2 : Com :=
  .ite (.eq (V "g_cf") (.lit 0)) (.write (.lit 0))
    (.ite (.eq (V "g_e") (V "g_v2")) (.write (.lit 0)) (.write (litE "g_b2" "g_e")))

/-- Decode block `b` into `bd`. -/
def decB (b bd : String) (D : ℕ) : Com := .seq (.assign "g_w" (V b)) (decG bd "g_w" "g_k1" 0 D)

/-- Decode values `v` into `vd`. -/
def decV (v vd : String) (D : ℕ) : Com := .seq (.assign "g_w" (V v)) (decG vd "g_w" "g_M" 0 D)

/-- The clause of the pair. -/
def xv2Body (D : ℕ) : Com :=
  seqList [decV "g_v2" "vd2" D, cfCom, .write (V "g_C2"), loopC "g_e" "g_C" lit1,
    loopC "g_e" "g_C" lit2]

/-- The clauses of the second block. -/
def xb2Body (D : ℕ) : Com := .seq (decB "g_b2" "bd2" D) (loopC "g_v2" "g_C" (xv2Body D))

/-- The clauses of the values of the first block. -/
def xv1Body (D : ℕ) : Com := .seq (decV "g_v1" "vd1" D) (loopC "g_b2" "g_W" (xb2Body D))

/-- The clauses of the first block. -/
def xb1Body (D : ℕ) : Com := .seq (decB "g_b1" "bd1" D) (loopC "g_v1" "g_C" (xv1Body D))

/-- **Phase X.** -/
def phaseX (D : ℕ) : Com := loopC "g_b1" "g_W" (xb1Body D)

/-! ### The evaluation -/

/-- A used slot has the value `w_c`. -/
def tBody : Com :=
  .ite (.lt (.get "bd1" (V "g_j")) (V "w_k"))
    (setIf (.eq (.get "vd1" (V "g_j")) (V "w_c")) "g_fT") .skip

/-- The slot shows `w_c` below index `0` or above index `k-1`. -/
def f1Body : Com :=
  .seq
    (.ite (.eq (.get "bd1" (V "g_j")) (.lit 0))
      (setIf (.lt (V "w_c") (.get "vd1" (V "g_j"))) "g_fF") .skip)
    (.ite (.eq (.add (.get "bd1" (V "g_j")) (.lit 1)) (V "w_k"))
      (setIf (.lt (.get "vd1" (V "g_j")) (V "w_c")) "g_fF") .skip)

/-- Two slots show `w_c` strictly between consecutive indices. -/
def f2Test : Com :=
  .ite (.eq (.add (.get "bd1" (V "g_j")) (.lit 1)) (.get "bd1" (V "g_j2")))
    (.ite (.lt (.get "bd1" (V "g_j2")) (V "w_k"))
      (.ite (.lt (.get "vd1" (V "g_j")) (V "w_c"))
        (setIf (.lt (V "w_c") (.get "vd1" (V "g_j2"))) "g_fF") .skip) .skip) .skip

/-- **The decision** on the code in `w_c` by the block in `bd1, vd1`: `w_f` and `g_und`. -/
def decCom : Com :=
  seqList [.assign "g_fT" (.lit 0), loopC "g_j" "g_D" tBody, .assign "g_fF" (.lit 0),
    setIf (.eq (V "w_k") (.lit 0)) "g_fF", loopC "g_j" "g_D" f1Body,
    loopC "g_i" "g_DD" (.seq splitI f2Test),
    .ite (.eq (V "g_fT") (.lit 1)) (.assign "w_f" (.lit 1))
      (.ite (.eq (V "g_fF") (.lit 1)) (.assign "w_f" (.lit 0))
        (.seq (.assign "w_f" (.lit 0)) (.assign "g_und" (.lit 1))))]

/-- **The evaluation of a quantifier-free formula**, following `Eval.ev`. -/
def evalCom : Formula → Com
  | .rel i js => relCom i js
  | .eq a c => atomCom (.eq a c)
  | .setVar js => .seq (codeCom js) decCom
  | .neg φ => .seq (evalCom φ) (.assign "w_f" (.sub (.lit 1) (V "w_f")))
  | .and φ ψ => .seq (evalCom φ) (.ite (.eq (V "w_f") (.lit 1)) (evalCom ψ) .skip)
  | .or φ ψ => .seq (evalCom φ) (.ite (.eq (V "w_f") (.lit 1)) .skip (evalCom ψ))
  | .ex _ _ => .assign "w_f" (.lit 0)
  | .all _ _ => .assign "w_f" (.lit 0)

/-! ### Phase M -/

/-- The literal of the block `g_b1` with values `g_v1` under `(g_za, g_zb)`. -/
def litM : Com :=
  .ite (.eq (V "w_f") (.lit 1))
    (.ite (.eq (V "g_und") (.lit 0)) (.write (litE "g_b1" "g_v1")) (.write (.lit 0)))
    (.write (.lit 0))

/-- One existential assignment. -/
def mzbBody (Dt : Data) : Com :=
  seqList [.assign "g_w" (V "g_zb"), decG "od" "g_w" "w_n" 0 Dt.q, .assign "g_und" (.lit 0),
    evalCom Dt.ψ, litM]

/-- One block with values. -/
def mvBody (Dt : Data) : Com := .seq (decV "g_v1" "vd1" Dt.D) (loopC "g_zb" "g_Q" (mzbBody Dt))

/-- One block. -/
def mbBody (Dt : Data) : Com := .seq (decB "g_b1" "bd1" Dt.D) (loopC "g_v1" "g_C" (mvBody Dt))

/-- One universal assignment: its digits, the length of its clause, the clause. -/
def mzaBody (Dt : Data) : Com :=
  seqList [.assign "g_w" (V "g_za"), decG "od" "g_w" "w_n" Dt.q Dt.p, .write (V "g_WCQ"),
    loopC "g_b1" "g_W" (mbBody Dt)]

/-- **Phase M.** -/
def phaseM (Dt : Data) : Com := loopC "g_za" "g_P" (mzaBody Dt)

/-! ### The program -/

/-- **The main part.** -/
def mainCom (Dt : Data) : Com :=
  seqList [boCom, LCom (wd Dt), uCom, powCom "w_PS" Dt.s, powCom "g_P" Dt.p, powCom "g_Q" Dt.q,
    constCom Dt.D, countCom, phaseB, phaseX Dt.D, phaseM Dt, .write (V "g_W")]

/-- **The program.** -/
def prog (Dt : Data) : Com :=
  .seq Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape
    (.seq headCom (.seq (fitCom (wd Dt)) (.ite (.eq (V "w_ft") (.lit 1)) (mainCom Dt) noCom)))

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs
