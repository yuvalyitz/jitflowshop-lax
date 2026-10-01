import Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs
import Lax808846Proofs.Transfer

/-! # The layout of the program

The scalars and arrays of the negation-elimination program, and `cmd_ok`: the program compiles under
this layout. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLayout

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs

/-- The scalars of the program. -/
def progVars : List String :=
  ["rt_n", "rt_i", "rt_v", "s", "N", "T", "p", "i", "c", "cr", "k", "q", "q2", "f", "t", "cn", "M",
    "r", "u", "v", "o", "dd", "lt", "l1", "x1", "x2", "g", "nn", "l2", "bs", "j", "fd", "w", "js",
    "mx", "t2", "bb", "KK", "wk", "wg", "wn", "wl", "k1", "g1", "k2", "g2", "lm", "ll", "e1", "e2",
    "ri", "ln", "fc", "h", "pl", "tg", "F0"]

/-- **The layout.** -/
def layout : Layout := ⟨progVars, ["a", "E", "fo", "R", "st"], 12⟩

set_option maxHeartbeats 8000000 in
theorem cmd_ok : Com.Ok layout cmd := by
  simp [layout, progVars, cmd, Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape,
    Lax496464Proofs.WHierarchy.Machine.ReadTape.readLoop, Lax496464Proofs.WHierarchy.Machine.ReadTape.readBody, body,
    header, entPass, entBody, entIn, foPass, foBody, foIn, rkPass, rkBody, rkIn, Mcom, hdOut, hdBody,
    ltOut, ltBody, ltIn, symPass, symBody, symW, copyBlock, fBlock, lBlock, sBlock, zBlock, minFind,
    maxFind, minBody, maxBody, sBody, succFind, sfBody, sfInner, cmpC, cmpStep, wR, wTup, mxPass,
    mxBody, qOut, qBody, trPass, trBody, dispatch, relBr, svBr, eqBr, negBr, conBr, qBr, posRelC,
    negRelC, negBig, wseqOf, wseq, lexOf, lexCom, lexBody, elems, writes, loop, Com.Ok, Expr.Ok,
    Cond.Ok, condExpr]

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.PLayout
