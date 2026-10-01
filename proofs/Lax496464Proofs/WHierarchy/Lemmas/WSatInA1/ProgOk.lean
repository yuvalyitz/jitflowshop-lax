import Lax808846Proofs.Compile
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs

/-! # The program compiles

The scalars and arrays of the program, and `cmd_ok`: the program compiles under this layout. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgOk

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs
open Lax496464Proofs.WHierarchy.HittingSet.Firsts (firstsLoop firstBody scanLoop scanBody)

/-- The scalars of the program. -/
def progVars : List String :=
  ["rt_n", "rt_i", "rt_v", "hs_t", "fp_p", "fp_q", "fp_r",
    "w_F", "w_K1", "w_L", "w_M", "w_acc", "w_ar", "w_b", "w_c", "w_c2", "w_cn", "w_cur", "w_d1",
    "w_dg", "w_dk", "w_e", "w_f", "w_hit", "w_i", "w_ii", "w_j", "w_jj", "w_k", "w_key", "w_ln",
    "w_m", "w_md", "w_nch", "w_nv", "w_o", "w_ok", "w_p", "w_pb", "w_pi", "w_pn", "w_pos", "w_pr",
    "w_pw", "w_pw2", "w_q", "w_t", "w_tg", "w_v"]

/-- **The layout.** -/
def layout : Layout := ⟨progVars, ["a", "co", "cd", "hs_mem", "fp_f", "ch"], 8⟩

theorem writeLits_ok (L : Layout) (h : 0 < L.temps) : ∀ l : List ℕ, Com.Ok L (writeLits l)
  | [] => trivial
  | _ :: l => ⟨⟨trivial, h⟩, writeLits_ok L h l⟩

set_option maxHeartbeats 16000000 in
theorem cmd_ok (d : ℕ) : Com.Ok layout (cmd d) := by
  simp only [cmd, body, Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape,
    Lax496464Proofs.WHierarchy.Machine.ReadTape.readLoop, Lax496464Proofs.WHierarchy.Machine.ReadTape.readBody,
    Lax496464Proofs.WHierarchy.Machine.ReadTape.V, parse, parseBody, copyBody, consts, powCom, varRows,
    firstsLoop, firstBody, scanLoop, scanBody, canonRows, nRows, nBody, keyBody, keyEc, lRows,
    lBody, simBody, simHead, simTail, lRow, padBody, c2Body, c2Step, c2Grp, grpCom, grpHead,
    grpTail, hitLoop, hitLit, chLoop, pick, structOut, structHead, emitT, emitCom, tagIte, digits,
    digBody, formOut, qOut, cOut, dOut, dInner, eOut, clauseOut, vtOut, ytOut, yOut, yInner, yvE,
    loop, bump, modE, par, V, Lax496464Proofs.WHierarchy.HittingSet.ReadNat.V,
    Lax496464Proofs.WHierarchy.HittingSet.ReadNat.bump, Com.Ok, Expr.Ok, Cond.Ok, condExpr]
  simp [layout, progVars, writeLits_ok]

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgOk
