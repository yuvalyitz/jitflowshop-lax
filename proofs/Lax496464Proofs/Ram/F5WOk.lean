import Lax496464Proofs.Ram.F5WRest

/-!
# Theorem 5 (endpoint sweep): the whole program and its layout
-/

namespace Lax496464Proofs.F5WOk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.W3Loops (V)
open Lax496464Proofs.Ram.W3Sweep Lax496464Proofs.Ram.W3SweepEv Lax496464Proofs.Ram.W3Loops
open Lax496464Proofs.F5WRest Lax496464Proofs.F5WPre

/-- **The whole program.** -/
def prog5w : Com := .seq Lax496464Proofs.Ram.W3Front2.sortSetup3 rest5w

/-- The layout: `W3Final.L3` plus the five scalars of the new passes. -/
def L5W : Layout :=
  ⟨["n", "m", "v", "i", "len", "en", "sn", "sc", "si", "sx", "sy", "ct1", "ct2", "shi", "sj",
    "sk", "slo", "smid", "snp", "spc", "stl", "sw", "bi", "boff", "bt", "bv", "W", "cinf", "mi",
    "mv", "N", "sh", "X", "c", "ri", "tv", "gx", "sp", "sq", "sd", "b2", "W1", "MK", "n2", "ci",
    "nx", "fp", "ip", "kp", "ist", "jj", "bb", "p0", "ck", "ans",
    "u1", "u2", "wm", "kk", "best"],
   ["A", "SA", "SB", "PS", "QS", "DS", "WS", "TB", "PC", "FS", "SLT", "P2"], 12⟩

set_option maxHeartbeats 16000000 in
theorem prog5w_ok : Com.Ok L5W prog5w := by
  simp [prog5w, rest5w, pre5w, Lax496464Proofs.Ram.F5QFit.fitCom,
    Lax496464Proofs.Ram.F5QFit.fitBody,
    Lax496464Proofs.Ram.F5QScale.kCom, Lax496464Proofs.Ram.F5QScale.wCom,
    Lax496464Proofs.Ram.F5QScale.rescaleCom, Lax496464Proofs.Ram.F5QScale.rescaleBody,
    Lax496464Proofs.Ram.F5WScan.scanW, Lax496464Proofs.Ram.F5WScan.scanWBody,
    Lax496464Proofs.Ram.F5QScan.outCom,
    core, initCore, sweepLoop, stepBody, decideCom, startEv, dueEv, dueSetup,
    dueTail, pickRecycle, pickFresh, setParams, startTail, startCommon, fillTB, fillBody,
    Lax496464Proofs.Ram.W3Front2.sortSetup3, Lax496464Proofs.Ram.W3Front.buildW,
    Lax496464Proofs.Ram.W3Front.dueSortCom, Lax496464Proofs.Ram.W3Front.dueCmp,
    Lax496464Proofs.Ram.W3Front.dueLoad,
    dueLoop, dueBody, startLoop, startBody, startSet, growPC, growBody,
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
    Lax496464Proofs.Ram.BuildSorted.buildSorted,
    Lax496464Proofs.Ram.BuildSorted.buildRow, Lax496464Proofs.Ram.Corollary1Init.maxScan,
    Lax496464Proofs.Ram.Corollary1Init.maxBody,
    condExpr, Com.Ok, Expr.Ok, Cond.Ok, L5W, Lax496464Proofs.Ram.Sort.V,
    Lax496464Proofs.Ram.Sort.bump]

end Lax496464Proofs.F5WOk
