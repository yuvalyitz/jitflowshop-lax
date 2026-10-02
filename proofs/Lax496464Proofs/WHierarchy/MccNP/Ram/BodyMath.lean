import Lax496464Proofs.WHierarchy.MccNP.Shape
import Mathlib.Data.List.GetD

/-!
# Arithmetic of the Reduction Body

The adjacency test `adjW` and the degree `degW` read off the word, and the identification of the
word of the construction with the lists written by the passes of `body`.
-/

namespace Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath

open Lax496464Proofs.WHierarchy.MccNP Lax496464Proofs.WHierarchy.MccNP.Shape Lax496464.WH_F2_MccConstruction

/-- The adjacency test of the machine: different colours, different vertices, matrix entry `0`. -/
def adjW (x : List ℕ) (s t : ℕ) : Bool :=
  decide (s / order x ≠ t / order x ∧ s % order x ≠ t % order x ∧
    x.getD (order x + 1 + (s % order x) * order x + t % order x) 0 = 0)

/-- The number of vertices of the construction. -/
def nOf (x : List ℕ) : ℕ := kOf x * order x

/-- The degree of the vertex `s`. -/
def degW (x : List ℕ) (s : ℕ) : ℕ := ((List.range (nOf x)).filter (adjW x s)).length

/-- The neighbours of `s`. -/
def nbW (x : List ℕ) (s : ℕ) : List ℕ := (List.range (nOf x)).filter (adjW x s)

lemma order_pos_of_lt {x : List ℕ} {s : ℕ} (h : s < nOf x) : 0 < order x := by
  unfold nOf at h
  rcases Nat.eq_zero_or_pos (order x) with h0 | h0
  · rw [h0] at h; simp at h
  · exact h0

theorem adjB_eq {x : List ℕ} (hx : Valid x) {s t : ℕ} (hs : s < nOf x) (ht : t < nOf x) :
    adjB (decode x) s t = adjW x s t := by
  have hn := order_pos_of_lt hs
  have ho := order_decode hx
  have hk := threshold_decode hx
  have hsz : size (decode x) = nOf x := by unfold size nOf; rw [ho, hk]
  have hu : s % order x < order x := Nat.mod_lt _ hn
  have hv : t % order x < order x := Nat.mod_lt _ hn
  have hle := (hx.2.2.2.1 _ hu _ hv).1
  have hg := adjG_decode hx (s % order x) (t % order x)
  have key : adjG (decode x) (s % order x) (t % order x) = false ↔
      x.getD (order x + 1 + (s % order x) * order x + t % order x) 0 = 0 := by
    rw [hg]
    unfold entry at hle ⊢
    simp only [hu, hv, true_and, decide_eq_false_iff_not]
    omega
  unfold adjB adjW
  rw [ho, hsz]
  refine decide_eq_decide.mpr ?_
  rw [key]
  tauto

lemma size_decode {x : List ℕ} (hx : Valid x) : size (decode x) = nOf x := by
  unfold size nOf; rw [order_decode hx, threshold_decode hx]

theorem neighbours_eq {x : List ℕ} (hx : Valid x) {s : ℕ} (hs : s < nOf x) :
    neighbours (decode x) s = nbW x s := by
  unfold neighbours nbW
  rw [size_decode hx]
  refine List.filter_congr fun t ht => ?_
  exact adjB_eq hx hs (List.mem_range.mp ht)

/-- The targets, machine side. -/
def tgW (x : List ℕ) : List ℕ := (List.range (nOf x)).flatMap (nbW x)

/-- The prefix sum of degrees. -/
def psum (x : List ℕ) (s : ℕ) : ℕ := ((List.range s).map (degW x)).sum

theorem targets_eq {x : List ℕ} (hx : Valid x) : targets (decode x) = tgW x := by
  unfold targets tgW
  rw [size_decode hx]
  exact List.flatMap_congr fun s hs => neighbours_eq hx (List.mem_range.mp hs)

theorem offsets_eq {x : List ℕ} (hx : Valid x) :
    offsets (decode x) = (List.range (nOf x + 1)).map (psum x) := by
  unfold offsets psum
  rw [size_decode hx]
  refine List.map_congr_left fun s hs => ?_
  have hs' := List.mem_range.mp hs
  congr 1
  refine List.map_congr_left fun r hr => ?_
  have hr' := List.mem_range.mp hr
  rw [neighbours_eq hx (by omega)]
  rfl

theorem colours_eq {x : List ℕ} (hx : Valid x) :
    colours (decode x) = (List.range (nOf x)).map (fun s => s / order x) := by
  unfold colours
  rw [size_decode hx, order_decode hx]

theorem length_tgW (x : List ℕ) : (tgW x).length = psum x (nOf x) := by
  unfold tgW psum
  rw [List.length_flatMap]
  rfl

theorem offsets_cons (x : List ℕ) :
    (List.range (nOf x + 1)).map (psum x) =
      0 :: (List.range (nOf x)).map (fun s => psum x (s + 1)) := by
  rw [List.range_succ_eq_map]
  simp [List.map_map, Function.comp_def, psum]

theorem psum_succ (x : List ℕ) (s : ℕ) : psum x (s + 1) = psum x s + degW x s := by
  unfold psum; rw [List.range_succ]; simp

theorem word_eq {x : List ℕ} (hx : Valid x) :
    word (decode x) = [nOf x, psum x (nOf x) / 2, 0] ++
      (List.range (nOf x)).map (fun s => psum x (s + 1)) ++
      (List.range (nOf x)).flatMap (nbW x) ++
      (List.range (nOf x)).map (fun s => s / order x) ++ [kOf x] := by
  unfold word
  rw [size_decode hx, targets_eq hx, offsets_eq hx, colours_eq hx, threshold_decode hx,
    offsets_cons, length_tgW]
  simp [tgW]

theorem Mx_eq {x : List ℕ} (hx : Valid x) : Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath.psum x (nOf x) =
    (targets (decode x)).length := by
  rw [targets_eq hx, length_tgW]

end Lax496464Proofs.WHierarchy.MccNP.Ram.BodyMath
