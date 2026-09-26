import Lax496464Proofs.Ram.D2Prog

/-!
# Theorem 2's program: its layout
-/

namespace Lax496464Proofs.Ram.D2Layout

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.D2Prog Lax496464Proofs.Ram.D2Core Lax496464Proofs.Ram.D2Step
open Lax496464Proofs.Ram.D2Setup Lax496464Proofs.Ram.D2Bsearch Lax496464Proofs.Ram.D2Scan1
open Lax496464Proofs.Ram.D2Valid1 Lax496464Proofs.Ram.D2Rows

/-- The layout: every scalar and array every part of the program mentions. -/
def L2 : Layout :=
  ⟨["n", "m", "len", "i", "v", "W", "en", "sn", "si", "sw", "snp", "spc", "slo", "smid", "shi",
    "sj", "sk", "sx", "sy", "ct1", "ct2", "sc", "stl", "boff", "bi", "bt", "bv", "nb", "R", "pi",
    "N", "cinf", "mi", "mv", "dj", "bl", "bh", "bm", "ex", "qx", "tt", "zk", "zi2", "cc", "zc",
    "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi", "zlim", "zx", "zq", "zu", "zp",
    "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp", "ri", "z1", "zr", "ct", "cf",
    "cw", "ce", "cg", "ans"],
   ["A", "SA", "SB", "PS", "QS", "DS", "WS", "PW", "NX", "TAB", "VALID"], 12⟩

set_option maxHeartbeats 8000000 in
theorem prog2_ok : Com.Ok L2 prog2 := by
  simp [prog2, Lax496464Proofs.Ram.W3Front2.sortSetup3, writeW, finishCom, core2, setup2, loopCom,
    bodyCom, topCom, stepCom, stepIsCode, pwSetup, pwBody, code0Loop, codeBody,
    Lax496464Proofs.Ram.Corollary1Init.maxScan, Lax496464Proofs.Ram.Corollary1Init.maxBody,
    nxLoop, nxBody, bsLoop, bsBody, scanCom, scanInit, scanLoop, scanBody, scanFin, digE, vphase,
    rowsLoop, rowBody, Lax496464Proofs.Ram.Col1.fCom,
    Lax496464Proofs.Ram.Decode.readInstance, Lax496464Proofs.Ram.Decode.readLoop,
    Lax496464Proofs.Ram.Decode.readBody, Lax496464Proofs.Ram.EstSort.estSortCom,
    Lax496464Proofs.Ram.EstSort.fillIdent, Lax496464Proofs.Ram.EstSort.estCmp,
    Lax496464Proofs.Ram.EstSort.estSums, Lax496464Proofs.Ram.EstSort.estDecide,
    Lax496464Proofs.Ram.Sort.tlSetup, Lax496464Proofs.Ram.Sort.moveK,
    Lax496464Proofs.Ram.Sort.mergeBody, Lax496464Proofs.Ram.Sort.mergeLoop,
    Lax496464Proofs.Ram.Sort.blockSetup, Lax496464Proofs.Ram.Sort.blockBody,
    Lax496464Proofs.Ram.Sort.blockLoop, Lax496464Proofs.Ram.Sort.copyLoop,
    Lax496464Proofs.Ram.Sort.npLoop, Lax496464Proofs.Ram.Sort.passCom,
    Lax496464Proofs.Ram.Sort.passBody, Lax496464Proofs.Ram.Sort.sortCom,
    Lax496464Proofs.Ram.BuildSorted.buildSorted, Lax496464Proofs.Ram.BuildSorted.buildRow,
    Lax496464Proofs.Ram.W3Front.buildW, Lax496464Proofs.Ram.W3Front.dueSortCom,
    Lax496464Proofs.Ram.W3Front.dueCmp, Lax496464Proofs.Ram.W3Front.dueLoad,
    Com.Ok, Expr.Ok, Cond.Ok, L2, condExpr, Lax496464Proofs.Ram.Sort.V,
    Lax496464Proofs.Ram.Sort.bump]

end Lax496464Proofs.Ram.D2Layout
