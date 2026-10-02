import Lax496464Proofs.Ram.F5MRest
import Lax496464Proofs.Ram.D2Layout

/-!
# Theorem 5 (Table of Section 3): the Whole Program and Its Layout
-/

namespace Lax496464Proofs.F5MOk

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.D2Prog Lax496464Proofs.Ram.D2Core Lax496464Proofs.Ram.D2Step
open Lax496464Proofs.Ram.D2Setup Lax496464Proofs.Ram.D2Bsearch Lax496464Proofs.Ram.D2Scan1
open Lax496464Proofs.Ram.D2Valid1 Lax496464Proofs.Ram.D2Rows Lax496464Proofs.Ram.D2Layout
open Lax496464Proofs.F5MRest Lax496464Proofs.F5WPre

/-- **The whole program.** -/
def prog5m : Com := .seq Lax496464Proofs.Ram.W3Front2.sortSetup3 rest5m

/-- The layout: `D2Layout.L2` plus the scalars of the new passes. -/
def L5M : Layout :=
  ⟨L2.scalars ++ ["wm", "kk", "best", "u1", "u2", "sb"], L2.arrays, L2.temps⟩

set_option maxHeartbeats 16000000 in
theorem prog5m_ok : Com.Ok L5M prog5m := by
  simp [prog5m, rest5m, guardM, mainM, pre5w, Lax496464Proofs.Ram.F5QFit.fitCom,
    Lax496464Proofs.Ram.F5QFit.fitBody,
    Lax496464Proofs.Ram.F5QScale.kCom, Lax496464Proofs.Ram.F5QScale.wCom,
    Lax496464Proofs.Ram.F5QScale.rescaleCom, Lax496464Proofs.Ram.F5QScale.rescaleBody,
    Lax496464Proofs.Ram.F5MScan.scanM, Lax496464Proofs.Ram.F5MScan.scanMLoop,
    Lax496464Proofs.Ram.F5MScan.scanMBody,
    Lax496464Proofs.Ram.F5QScan.outCom,
    Lax496464Proofs.Ram.W3Front2.sortSetup3, core2, setup2, loopCom,
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
    Com.Ok, Expr.Ok, Cond.Ok, L5M, L2, condExpr, Lax496464Proofs.Ram.Sort.V,
    Lax496464Proofs.Ram.Sort.bump]

end Lax496464Proofs.F5MOk
