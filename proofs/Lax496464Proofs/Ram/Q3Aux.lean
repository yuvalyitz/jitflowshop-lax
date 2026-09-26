import Lax496464Proofs.Ram.Q3Defs
import Lax496464Proofs.Ram.Q3Tab
import Lax496464Proofs.Ram.Q3Model
import Lax496464Proofs.Ram.T4Tail

/-!
# Theorem 3, profile sweep: small glue lemmas between the pure layer and the loops
-/

namespace Lax496464Proofs.Ram.Q3Aux

open Lax496464Proofs.Ram.Q3Defs Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

/-- A table meaning `R` also means anything pointwise equivalent on the profiles `< bt`. -/
theorem tabSem_congr {bt w1 INF : ℕ} {R R' : ℕ → ℕ → ℕ → Prop} {T : List ℕ}
    (h : ∀ x < bt, ∀ c P, R x c P ↔ R' x c P) (hT : TabSem bt w1 INF R T) :
    TabSem bt w1 INF R' T := by
  intro x hx c hc
  obtain ⟨h1, h2⟩ := hT x hx c hc
  exact ⟨h1, fun P hP => (h2 P hP).trans (h x hx c P)⟩

/-- Every entry of a table whose cells are all `≤ INF` is `≤ INF`. -/
theorem getD_le_of_cells {bt w1 INF : ℕ} {T : List ℕ} (hw1 : 0 < w1)
    (hTl : T.length = bt * w1) (h : ∀ x < bt, ∀ c < w1, cell w1 T x c ≤ INF) (i : ℕ) :
    T.getD i 0 ≤ INF := by
  by_cases hi : i < bt * w1
  · have hx : i / w1 < bt := (Nat.div_lt_iff_lt_mul hw1).mpr hi
    have hc : i % w1 < w1 := Nat.mod_lt _ hw1
    have := h _ hx _ hc
    unfold cell at this
    rwa [show i / w1 * w1 + i % w1 = i by rw [Nat.mul_comm]; exact Nat.div_add_mod i w1] at this
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

theorem getD_map_range (f : ℕ → ℕ) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl

end Lax496464Proofs.Ram.Q3Aux
