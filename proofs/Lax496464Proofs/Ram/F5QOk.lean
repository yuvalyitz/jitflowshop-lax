import Lax496464Proofs.Ram.F5QProg
import Lax496464Proofs.Ram.Q3Final

/-!
# Theorem 5 (profile sweep): the layout of `prog5`
-/

namespace Lax496464Proofs.F5QOk

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax496464Proofs.Ram.Q3Core Lax496464Proofs.Ram.Q3Loop
open Lax496464Proofs.F5QProg

/-- The layout: `Q3Final.L3` plus the three scalars of the new passes. -/
def L5 : Layout :=
  ⟨["n", "m", "len", "i", "v", "W", "en", "sn", "boff", "bi", "bt", "bv", "si", "sw", "snp", "spc",
    "slo", "smid", "shi", "sj", "sk", "sx", "sy", "ct1", "ct2", "sc", "stl",
    "qm", "bb", "w1", "N", "cinf", "jj", "pt", "pj", "qj", "dj", "wj", "rf", "dl", "pwd", "pwq",
    "ex", "ok", "u1", "u2", "u3", "u4", "u5", "u6", "wm", "kk", "best"],
   ["A", "SA", "SB", "PS", "QS", "DS", "WS", "T", "S", "G"], 12⟩

set_option maxHeartbeats 16000000 in
theorem prog5_ok : Com.Ok L5 prog5 := by
  simp [prog5, Lax496464Proofs.F5QRest.rest5, Lax496464Proofs.Ram.Q3Front.frontQ,
    Lax496464Proofs.Ram.Decode.readInstance,
    Lax496464Proofs.Ram.Decode.readLoop, Lax496464Proofs.Ram.Decode.readBody,
    Lax496464Proofs.Ram.EstSort.estSortCom,
    Lax496464Proofs.Ram.EstSort.fillIdent, Lax496464Proofs.Ram.EstSort.estCmp,
    Lax496464Proofs.Ram.EstSort.estSums, Lax496464Proofs.Ram.EstSort.estDecide,
    Lax496464Proofs.Ram.Sort.tlSetup, Lax496464Proofs.Ram.Sort.moveK,
    Lax496464Proofs.Ram.Sort.mergeBody, Lax496464Proofs.Ram.Sort.mergeLoop,
    Lax496464Proofs.Ram.Sort.blockSetup, Lax496464Proofs.Ram.Sort.blockBody,
    Lax496464Proofs.Ram.Sort.blockLoop, Lax496464Proofs.Ram.Sort.copyLoop,
    Lax496464Proofs.Ram.Sort.npLoop, Lax496464Proofs.Ram.Sort.passCom,
    Lax496464Proofs.Ram.Sort.passBody, Lax496464Proofs.Ram.Sort.sortCom,
    Lax496464Proofs.Ram.BuildSorted.buildSorted, Lax496464Proofs.Ram.BuildSorted.buildRow,
    Lax496464Proofs.Ram.W3Front.buildW,
    coreCom, mainLoop, eventCom, Lax496464Proofs.Ram.Q3Event.prepCom,
    Lax496464Proofs.Ram.Q3Event.loadCom, Lax496464Proofs.Ram.Q3Event.refCom,
    Lax496464Proofs.Ram.Q3Init.powCom, Lax496464Proofs.Ram.Q3Init.powBody,
    Lax496464Proofs.Ram.Q3Init.maxCom, Lax496464Proofs.Ram.Q3Init.maxBody,
    Lax496464Proofs.Ram.Q3Init.gInitCom, Lax496464Proofs.Ram.Q3Init.gBody,
    Lax496464Proofs.Ram.Q3Init.gCalc, Lax496464Proofs.Ram.Q3Init.gWrite,
    Lax496464Proofs.Ram.Q3Passes.fillCom, Lax496464Proofs.Ram.Q3Passes.fillBody,
    Lax496464Proofs.Ram.Q3Passes.margCom, Lax496464Proofs.Ram.Q3Passes.margBody,
    Lax496464Proofs.Ram.Q3Passes.takeCom, Lax496464Proofs.Ram.Q3Passes.takeBody,
    Lax496464Proofs.Ram.Q3Passes.takeCond, Lax496464Proofs.Ram.Q3Passes.takeP1,
    Lax496464Proofs.Ram.Q3Passes.takeP2, Lax496464Proofs.Ram.Q3Passes.takeP3,
    Lax496464Proofs.Ram.F5QFit.fitCom, Lax496464Proofs.Ram.F5QFit.fitBody,
    Lax496464Proofs.Ram.F5QScale.kCom, Lax496464Proofs.Ram.F5QScale.wCom,
    Lax496464Proofs.Ram.F5QScale.rescaleCom, Lax496464Proofs.Ram.F5QScale.rescaleBody,
    Lax496464Proofs.Ram.F5QScan.scanCom, Lax496464Proofs.Ram.F5QScan.scanBody,
    Lax496464Proofs.Ram.F5QScan.outCom,
    Com.Ok, Expr.Ok, Cond.Ok, L5, condExpr, Lax496464Proofs.Ram.Sort.V,
    Lax496464Proofs.Ram.Sort.bump]

end Lax496464Proofs.F5QOk
