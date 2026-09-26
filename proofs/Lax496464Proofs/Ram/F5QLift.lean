import Lax496464Proofs.Ram.F5QScan
import Lax496464Proofs.Ram.F5QMath
import Lax496464Proofs.Ram.Q3Model
import Lax496464Proofs.Ram.Q3Tab
import Lax496464Proofs.Ram.Q3Aux

/-!
# Theorem 5 (profile sweep): what the passes compute, as the pure objects of `F5Math`

The fit pass, the scale factor and the rescaling pass, run on the sorted arrays of an instance `J`,
compute exactly `zeroUnfit J`, `scaleK J e` and the weights of `scaled J e`; the scan finds
`scaledOpt J e`.
-/

namespace Lax496464Proofs.F5QLift

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.Fptas
open Lax496464Proofs.F5Math Lax496464Proofs.Ram.F5QFit Lax496464Proofs.Ram.F5QScale
open Lax496464Proofs.Ram.Q3Defs Lax496464Proofs.Ram.Q3Aux
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

/-- The four sorted arrays of `J`. -/
def PSl (J : Instance) : List ℕ := (List.range J.jobs).map (pv J)
def QSl (J : Instance) : List ℕ := (List.range J.jobs).map (qv J)
def DSl (J : Instance) : List ℕ := (List.range J.jobs).map (dv J)
def WSl (J : Instance) : List ℕ := (List.range J.jobs).map (wv J)

theorem getD_map_range' (f : ℕ → ℕ) (n k : ℕ) (hk : k < n) :
    ((List.range n).map f).getD k 0 = f k := getD_map_range f n k hk

theorem fitVal_eq (J : Instance) (k : ℕ) (hk : k < J.jobs) :
    fitVal (PSl J) (QSl J) (DSl J) (WSl J) k = (zeroUnfit J).w ⟨k, hk⟩ := by
  unfold fitVal PSl QSl DSl WSl
  rw [getD_map_range' _ _ _ hk, getD_map_range' _ _ _ hk, getD_map_range' _ _ _ hk,
    getD_map_range' _ _ _ hk]
  simp only [pv, qv, dv, wv, dif_pos hk]
  show _ = if Fit J ⟨k, hk⟩ then J.w ⟨k, hk⟩ else 0
  by_cases h : J.d ⟨k, hk⟩ < J.p ⟨k, hk⟩ + J.q ⟨k, hk⟩
  · have hf : ¬ Fit J ⟨k, hk⟩ := by unfold Fit; omega
    rw [if_pos h, if_neg hf]
  · have hf : Fit J ⟨k, hk⟩ := by unfold Fit; omega
    rw [if_neg h, if_pos hf]

theorem fitArr_eq (J : Instance) :
    fitArr (PSl J) (QSl J) (DSl J) (WSl J) J.jobs =
      (List.finRange J.jobs).map (zeroUnfit J).w := by
  apply List.ext_getElem
  · simp [fitArr]
  · intro k h1 h2
    simp only [fitArr, List.getElem_map, List.getElem_range, List.getElem_finRange]
    exact fitVal_eq J k (by simpa [fitArr] using h1)

theorem wm_eq (J : Instance) :
    (fitArr (PSl J) (QSl J) (DSl J) (WSl J) J.jobs).foldr max 0 = wmaxFit J := by
  rw [fitArr_eq]; rfl

theorem rescVal_eq (J : Instance) (e : ℕ) (k : ℕ) (hk : k < J.jobs) :
    rescVal (scaleK J e) (fitVal (PSl J) (QSl J) (DSl J) (WSl J) k) = wv (scaled J e) k := by
  rw [fitVal_eq J k hk]
  have hwv : wv (scaled J e) k = (scaled J e).w ⟨k, hk⟩ := by
    unfold wv; rw [dif_pos (show k < (scaled J e).jobs from hk)]
  have h1 : wv (scaled J e) k =
      if Fit J ⟨k, hk⟩ ∧ 1 ≤ J.w ⟨k, hk⟩ then (J.w ⟨k, hk⟩ - 1) / scaleK J e + 1 else 0 := by
    rw [hwv]; exact scaled_w_eq J e ⟨k, hk⟩
  rw [h1]
  show rescVal _ (if Fit J ⟨k, hk⟩ then J.w ⟨k, hk⟩ else 0) = _
  unfold rescVal
  by_cases hf : Fit J ⟨k, hk⟩
  · rw [if_pos hf]
    by_cases hw : 1 ≤ J.w ⟨k, hk⟩
    · rw [if_pos (by omega), if_pos ⟨hf, hw⟩]
    · rw [if_neg (by omega), if_neg (fun h => hw h.2)]
  · rw [if_neg hf, if_neg (by omega), if_neg (fun h => hf h.1)]

theorem rescArr_eq (J : Instance) (e : ℕ) :
    rescArr (scaleK J e) (fitArr (PSl J) (QSl J) (DSl J) (WSl J) J.jobs) J.jobs =
      (List.range J.jobs).map (wv (scaled J e)) := by
  unfold rescArr
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.mp hk
  unfold fitArr
  rw [getD_map_range' _ _ _ hk']
  exact rescVal_eq J e k hk'

/-! ## Reading the table -/

theorem tab_col {bt w1 INF : ℕ} (hINF : 0 < INF) {R : ℕ → ℕ → ℕ → Prop} {T : List ℕ}
    (hT : TabSem bt w1 INF R T) {c : ℕ} (hc : c < w1) :
    (∃ x < bt, cell w1 T x c < INF) ↔ ∃ x < bt, R x c (INF - 1) := by
  have hI : INF - 1 < INF := by omega
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, ((hT x hx c hc).2 (INF - 1) hI).1 (by omega)⟩
  · rintro ⟨x, hx, h⟩
    have := ((hT x hx c hc).2 (INF - 1) hI).2 h
    exact ⟨x, hx, by omega⟩

theorem best_eq {N w1 INF bt opt best : ℕ} {T : List ℕ} (hw1 : 0 < w1) (hN : N = bt * w1)
    (hopt : opt < w1)
    (hfin : ∀ c < w1, (∃ x < bt, cell w1 T x c < INF) ↔ c ≤ opt)
    (hub : ∀ idx < N, T.getD idx 0 < INF → idx % w1 ≤ best)
    (hatt : best = 0 ∨ ∃ idx < N, T.getD idx 0 < INF ∧ idx % w1 = best) : best = opt := by
  apply le_antisymm
  · rcases hatt with h | ⟨idx, hidx, hfi, hm⟩
    · omega
    · have hx : idx / w1 < bt := (Nat.div_lt_iff_lt_mul hw1).mpr (by rw [← hN]; exact hidx)
      have hcl : idx % w1 < w1 := Nat.mod_lt _ hw1
      have hcell : cell w1 T (idx / w1) (idx % w1) = T.getD idx 0 := by
        unfold cell
        rw [show idx / w1 * w1 + idx % w1 = idx by rw [Nat.mul_comm]; exact Nat.div_add_mod idx w1]
      have := (hfin (idx % w1) hcl).mp ⟨idx / w1, hx, by rw [hcell]; exact hfi⟩
      omega
  · obtain ⟨x, hx, hfi⟩ := (hfin opt hopt).mpr le_rfl
    have hidx : x * w1 + opt < N := by
      have : (x + 1) * w1 ≤ bt * w1 := Nat.mul_le_mul_right _ hx
      have h2 : (x + 1) * w1 = x * w1 + w1 := by ring
      omega
    have := hub (x * w1 + opt) hidx hfi
    have hm : (x * w1 + opt) % w1 = opt := by
      rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hopt
    rw [hm] at this
    exact this

end Lax496464Proofs.F5QLift

namespace Lax496464Proofs.F5QLift
open Lax496464.FlowShop Lax496464.FlowShop.Instance
open Lax496464Proofs.Ram.Dp1 (pv qv dv)
open Lax496464Proofs.Ram.DpMArr (wv)

theorem PSl_getD (J : Instance) (k : ℕ) (hk : k < J.jobs) : (PSl J).getD k 0 = J.p ⟨k, hk⟩ := by
  unfold PSl; rw [getD_map_range' _ _ _ hk]; simp [pv, hk]
theorem QSl_getD (J : Instance) (k : ℕ) (hk : k < J.jobs) : (QSl J).getD k 0 = J.q ⟨k, hk⟩ := by
  unfold QSl; rw [getD_map_range' _ _ _ hk]; simp [qv, hk]
theorem DSl_getD (J : Instance) (k : ℕ) (hk : k < J.jobs) : (DSl J).getD k 0 = J.d ⟨k, hk⟩ := by
  unfold DSl; rw [getD_map_range' _ _ _ hk]; simp [dv, hk]
theorem WSl_getD (J : Instance) (k : ℕ) (hk : k < J.jobs) : (WSl J).getD k 0 = J.w ⟨k, hk⟩ := by
  unfold WSl; rw [getD_map_range' _ _ _ hk]; simp [wv, hk]

theorem PSl_length (J : Instance) : (PSl J).length = J.jobs := by simp [PSl]
theorem QSl_length (J : Instance) : (QSl J).length = J.jobs := by simp [QSl]
theorem DSl_length (J : Instance) : (DSl J).length = J.jobs := by simp [DSl]
theorem WSl_length (J : Instance) : (WSl J).length = J.jobs := by simp [WSl]

end Lax496464Proofs.F5QLift
