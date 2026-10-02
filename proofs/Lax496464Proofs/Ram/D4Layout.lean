import Lax496464Proofs.Ram.D4Prog

/-!
# Corollary 2's Program: Its Layout
-/

namespace Lax496464Proofs.Ram.D4Layout

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.D4Prog Lax496464Proofs.Ram.D4Core Lax496464Proofs.Ram.D4Step
open Lax496464Proofs.Ram.D4Sum Lax496464Proofs.Ram.D4Row
open Lax496464Proofs.Ram.D2Step (stepIsCode)
open Lax496464Proofs.Ram.D2Setup Lax496464Proofs.Ram.D2Bsearch Lax496464Proofs.Ram.D2Scan1
open Lax496464Proofs.Ram.D2Valid1

/-- The layout: every scalar and array every part of the program mentions. -/
def L4 : Layout :=
  ⟨["n", "m", "len", "i", "v", "W", "en", "sn", "si", "sw", "snp", "spc", "slo", "smid", "shi",
    "sj", "sk", "sx", "sy", "ct1", "ct2", "sc", "stl", "boff", "bi", "bt", "bv", "nb", "R", "pi",
    "N", "cinf", "mi", "mv", "dj", "bl", "bh", "bm", "ex", "qx", "tt", "zk", "zi2", "cc", "zc",
    "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi", "zlim", "zx", "zq", "zu", "zp",
    "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp", "ri", "z1", "zr", "ct", "cf",
    "cw", "ce", "cg", "ans", "sI"],
   ["A", "SA", "SB", "PS", "QS", "DS", "WS", "PW", "NX", "TAB", "VALID"], 12⟩

set_option maxHeartbeats 8000000 in
theorem prog4_ok : Com.Ok L4 prog4 := by
  simp [prog4, Lax496464Proofs.Ram.W3Front2.sortSetup3, Lax496464Proofs.Ram.D2Prog.writeW,
    finishCom4, core4, setup4, loopCom4,
    bodyCom4, topCom4, stepCom4, stepIsCode4, sumCom, sumLoop, sumBody, pwSetup, pwBody, code0Loop,
    codeBody, nxLoop, nxBody, bsLoop, bsBody, scanCom, scanInit, scanLoop, scanBody, scanFin, digE,
    vphase, rowsLoop4, rowBody4,
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
    Com.Ok, Expr.Ok, Cond.Ok, L4, condExpr, Lax496464Proofs.Ram.Sort.V,
    Lax496464Proofs.Ram.Sort.bump]

end Lax496464Proofs.Ram.D4Layout
