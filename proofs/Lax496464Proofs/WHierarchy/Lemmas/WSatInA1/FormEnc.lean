import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Formula

/-! # The code of the sentence, as the program writes it

`encode_phi`: the code of the sentence of `Defs`, spelled out in the pieces the program writes one
after the other. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.FormEnc

open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Formula

theorem encode_bigAnd : ∀ l : List Formula,
    (bigAnd l).encode = l.flatMap (fun φ => 4 :: φ.encode) ++ [2, 0, 0]
  | [] => rfl
  | φ :: l => by simp [bigAnd, Formula.encode, encode_bigAnd l]

theorem encode_bigOr : ∀ l : List Formula,
    (bigOr l).encode = l.flatMap (fun φ => 5 :: φ.encode) ++ [3, 2, 0, 0]
  | [] => rfl
  | φ :: l => by simp [bigOr, Formula.encode, encode_bigOr l]

variable (d k : ℕ)

def qW : List ℕ := (List.range (nv d k)).flatMap fun v => [6, v]
def cW : List ℕ := (List.range k).flatMap fun i => [4, 0, 1, 1, i]
def dW : List ℕ := (List.range k).flatMap fun i => (List.range i).flatMap fun j => [4, 3, 2, i, j]
def yInW (t j : ℕ) : List ℕ := (List.range (k + 1)).flatMap fun i => [5, 2, yv k t j, i]
def yW (t : ℕ) : List ℕ :=
  (List.range (k + 1)).flatMap (fun j => 4 :: (yInW k t j ++ [3, 2, 0, 0])) ++ [2, 0, 0]
def clW (t : ℕ) : List ℕ :=
  [5, 3, 0, 2, d + 1] ++ vt d k t ++ [4, 0, 3, k + (d + 2)] ++ vt d k t ++ yt k t ++ yW k t
def eW : List ℕ := (List.range (FF d k)).flatMap (fun t => 4 :: clW d k t) ++ [2, 0, 0]

theorem encode_inS (t j : ℕ) : (inS k t j).encode = yInW k t j ++ [3, 2, 0, 0] := by
  simp [inS, encode_bigOr, yInW, Formula.encode, List.flatMap_map]

theorem encode_clauseF (t : ℕ) : (clauseF d k t).encode = clW d k t := by
  simp only [clauseF, Formula.encode, encode_bigAnd, List.flatMap_map, encode_inS, clW, yW,
    List.length_append, length_vt, length_yt]
  simp; ring_nf

/-- **The code of the sentence.** -/
theorem encode_phi : (phi d k).encode = qW d k ++ [4, 0, 0, 1] ++ [k] ++ [4] ++ cW k ++
    [2, 0, 0, 4] ++ dW k ++ [2, 0, 0] ++ eW d k := by
  unfold phi
  rw [encode_exBlock]
  simp only [psi, Formula.encode, encode_bigAnd, List.flatMap_map, encode_clauseF, qW, cW, dW, eW,
    distinctL, List.flatMap_assoc]
  simp

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.FormEnc
