import Lax496464Proofs.Ram.D2Core
import Lax496464Proofs.Ram.D5Loop

/-!
# Corollary 3's Machine, Part 5: the Core

`core5 = setup2 ; loopComU`.  The set-up of Theorem 2 is used at the table parameter `W := n`
(the scalar `"W"` holds `n` when it runs, so `R := n + 1`, the block width), and the actual
threshold is in `"Wc"`.  `core5_spec` describes the finished table: every entry of the block of
the first `m` indices is the capped dual value on the good cells.
-/

namespace Lax496464Proofs.Ram.D5Core

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.Sort (V bump)
open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder
open Lax496464Proofs.Ram.D2Digits Lax496464Proofs.Ram.D2Valid Lax496464Proofs.Ram.D2Step
open Lax496464Proofs.Ram.D2Core
open Lax496464Proofs.Ram.D5Pure Lax496464Proofs.Ram.D5Step Lax496464Proofs.Ram.D5Loop
open Lax496464Proofs.Ram.DpMArr (wv)

/-- The whole core. -/
def core5 : Com := .seq setup2 loopComU

theorem setup2_wvars_ne : ∀ y ∈ setup2.wvars, y ≠ "Wc" := by decide

theorem loopComU_wvars : ∀ y ∈ loopComU.wvars,
    y ∈ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi", "zlim", "zx",
      "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp", "lim", "ri",
      "z1", "ct"] := by decide

/-- **The core's specification.** -/
theorem core5_spec {J : Instance} {B n m Wr p : ℕ} (ci : CI J B n m n) (hWr : Wr < B)
    (hwW : ∀ k < n, wv J k + Wr < B) (hp : ∀ i : J.Job, J.p i = p) :
    Spec B (fun σ => CPre J n m n σ ∧ σ.vars "Wc" = Wr) core5
      (fun _σ σ' => σ'.vars "zk" = codeL n m (List.range (min m n)) ∧ σ'.vars "R" = n + 1 ∧
        σ'.vars "Wc" = Wr ∧
        UTab J n m Wr p ((n + 1) ^ m) 0 (σ'.arrs "TAB"))
      (setupCost n m + (loopWork n m n ((n + 1) ^ m) + 4)) := by
  refine Spec.of_exists fun σ ⟨hσ, hWc⟩ => ?_
  obtain ⟨σ1, hr1, ⟨inf, NXl, PWl, sc, hSt, hcc, hzk, hW, hT, hV⟩, hfv1, hfa1, -, -⟩ :=
    (setup2_spec ci).frame.run (σ := σ) hσ
  have hWc1 : σ1.vars "Wc" = Wr := by
    rw [hfv1 "Wc" (fun h => setup2_wvars_ne _ h rfl)]; exact hWc
  obtain ⟨σ2, hr2, ⟨hcc2, hT2⟩, hfv2, hfa2, -, -⟩ :=
    (loopComU_spec sc hWr hwW hp).frame.run (σ := σ1)
      ⟨⟨⟨hSt, hWc1⟩, by rw [hcc], by rw [hT, hcc]; exact utab_init J n m Wr p,
        by rw [hcc, hV]; exact validOK_init n m⟩, hcc⟩
  have hfv : ∀ y, y ∉ ["zc", "cc", "zx1", "zx2", "zt", "zsuf", "zv", "zj", "zy", "zcur", "zi",
      "zlim", "zx", "zq", "zu", "zp", "zw", "zcode", "zb1", "zb2", "zbc", "wj", "cd", "cq", "cp",
      "lim", "ri", "z1", "ct"] → σ2.vars y = σ1.vars y :=
    fun y hy => hfv2 y (fun h => hy (loopComU_wvars y h))
  refine ⟨σ2, _, hr1.seq hr2, le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [hfv "zk" (by decide)]; exact hzk
  · rw [hfv "R" (by decide)]; exact hSt.2.2.2.1
  · rw [hfv "Wc" (by decide)]; exact hWc1
  · exact hT2

end Lax496464Proofs.Ram.D5Core
