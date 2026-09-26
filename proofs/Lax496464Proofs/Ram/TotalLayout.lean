import Lax496464Proofs.Ram.TotalReduction

/-!
# `totalProg`'s layout

The final `RamPolytime f` assembly (`RamBridge.ramPolytime_of_poly`) needs `totalProg` compiled
against a `Layout` (`compileProgram`), and `Com.Ok` checked against it — exactly what
`Corollary4.lean`'s `Lred`/`prog_ok` do for the old, domain-restricted `prog`. `totalProg` is a
strict extension of `prog` (the same `progTail`, plus `parseCom`, `bridgeCopy`, `validate`, and
`rejectProg` in front of it), so `Ltotal` below is `Lred`'s own scalar/array lists (`Corollary4.
Lred`) unioned with the new front end's own names.
-/

namespace Lax496464Proofs.Ram.TotalLayout

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.ScanProg (parseCom initVars scanLoop scanBody stepCom stepPh0 stepPh1
  stepPh0B1 stepPh0Cc0 stepPh0CcPos stepPh1Prefix afterNumberCom dispatchBody)
open Lax496464Proofs.Ram.RCBridge (bridgeCopy)
open Lax496464Proofs.Ram.CopyArr (copyLoop copyBody)
open Lax496464Proofs.Ram.Validate (validate checkOffsets checkMembers checkSorted sortedBody
  checkUniverseBound failIf failUnless)
open Lax496464Proofs.Ram.Reject (rejectProg)
open Lax496464Proofs.Ram.TotalProg (totalProg progTail)
open Lax496464Proofs.Ram.Build (build)
open Lax496464Proofs.Ram.Program (consts)
open Lax496464Proofs.Ram.PrintNat (printNat computeSize sizeLoop sizeBody onesOutLoop onesOutBody
  digitsOutLoop digitsOutBody)
open Lax496464Proofs.Ram.PrintTail (printTail printExpr printLoop printBody targetPrep)
open Lax496464Proofs.Ram.Gen (gen selPass selRow selInner selElem selVals storeTriple epoch
  dumPass dumRBody dumJ dumJBody dumI dumElem valsA valsB)

/-- The scalars: `Corollary4.Lred`'s own list (`progTail`'s needs) unioned with the scan's
scalars (`ScanProg`), the bridge's (`RCBridge`), `validate`'s, and `ReadAll`'s. -/
def scalars : List String :=
  ["n", "m", "mp1", "L", "i", "v", "k", "j", "bs", "be", "bl", "tt", "f", "s", "Lc", "x1", "x2",
    "R", "Q", "dc", "sc", "nj", "t", "r", "u", "e", "g", "gq", "gg", "GG", "gn", "a", "b", "c",
    "ph", "tgt", "cc", "ii", "vv", "off", "sz", "cb", "cb2", "valid", "rt", "rv", "ci", "p", "cnt", "jj", "xx"]

/-- The arrays: `Lred`'s own list unioned with the scan's scratch arrays. -/
def arrays : List String := ["OFF", "MEM", "MJ", "MI", "PA", "QA", "DA", "OFFS", "MEMS", "a"]

def Ltotal : Layout := ⟨scalars, arrays, 6⟩

set_option maxHeartbeats 4000000 in
theorem totalProg_ok : Com.Ok Ltotal totalProg := by
  simp [totalProg, progTail, parseCom, Lax391470Proofs.ReadAll.readAll,
    Lax391470Proofs.ReadAll.readLoop, Lax391470Proofs.ReadAll.readBody, initVars, scanLoop,
    scanBody, stepCom, stepPh0, stepPh1, stepPh0B1, stepPh0Cc0, stepPh0CcPos, stepPh1Prefix,
    afterNumberCom, dispatchBody, bridgeCopy, copyLoop, copyBody, validate, checkOffsets,
    checkMembers, checkSorted, sortedBody, checkUniverseBound, failIf, failUnless, rejectProg, build, Lax496464Proofs.Ram.Build.jBody,
    Lax496464Proofs.Ram.Build.jSetup, Lax496464Proofs.Ram.Build.iLoop,
    Lax496464Proofs.Ram.Build.iBody, Lax496464Proofs.Ram.Build.scanLoop,
    Lax496464Proofs.Ram.Build.scanBody, Lax496464Proofs.Ram.Build.collect,
    selPass, selRow, selInner, selElem, selVals, storeTriple, epoch, dumPass, dumRBody, dumJ,
    dumJBody, dumI, dumElem, valsA, valsB,
    consts, gen, printTail, printExpr, printLoop, printBody,
    targetPrep, printNat, computeSize, sizeLoop, sizeBody, onesOutLoop, onesOutBody,
    digitsOutLoop, digitsOutBody,
    
    Com.Ok, Expr.Ok, Cond.Ok, Ltotal, scalars, arrays, condExpr]

end Lax496464Proofs.Ram.TotalLayout
