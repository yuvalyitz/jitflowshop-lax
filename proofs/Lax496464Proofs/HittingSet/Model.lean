import Lax496464Proofs.HittingSet.Correct
import Lax391470Proofs.Bits

/-!
# The output, bit by bit

The zeros and ones of the encoding of the image, arranged the way the program produces
them: the three numbers, the pair of each variable, and the set of each clause as its size
followed by its elements in increasing order.
-/

namespace Lax496464Proofs.HittingSet.Model

open Lax429075.CNF Lax434930.PolynomialTime Lax391470Proofs.Bits
open Lax496464.HittingSet Lax496464.HittingSetFromSat Lax496464Proofs.HittingSet.Correct

theorem natBits_encodeNat (n : ℕ) : natBits (encodeNat n) = bitsNat n :=
  Lax391470Proofs.Bits.natBits_encodeNat n

theorem natBits_append (a b : Word) : natBits (a ++ b) = natBits a ++ natBits b := by
  simp [natBits]

theorem natBits_flatMap {α : Type} (l : List α) (f : α → Word) :
    natBits (l.flatMap f) = l.flatMap fun a => natBits (f a) := by
  simp [natBits, List.map_flatMap]

/-- The code of a set, from the list of its members. -/
def setBits (l : List ℕ) : List ℕ := bitsNat l.length ++ l.flatMap bitsNat

theorem card_eq_length_members (P : Instance) (j : Fin P.m) :
    (P.F j).card = (P.members j).length := by
  rw [← Finset.univ_inter (P.F j), ← Finset.filter_mem_eq_inter, Finset.card_def,
    Finset.filter_val, Fin.univ_def]
  rfl

theorem natBits_encodeInstance (P : Instance) (k : ℕ) :
    natBits (encodeInstance P k) =
      bitsNat P.n ++ bitsNat P.m ++ bitsNat k ++
        (List.finRange P.m).flatMap fun j =>
          bitsNat (P.members j).length ++ List.flatMap bitsNat (List.map Fin.val (P.members j)) := by
  simp only [encodeInstance, natBits_append, natBits_flatMap, natBits_encodeNat,
    card_eq_length_members, bind_pure_comp, List.map_eq_map]

/-! ### The sets of a formula's instance -/

/-- The members of the `j`-th set of the instance of `F`, as numbers. -/
def memb (F : Formula) (j : ℕ) : List ℕ :=
  (List.range (2 * vars F)).filter fun e => decide (e ∈ (sets F).getD j [])

theorem map_val_finRange (n : ℕ) :
    List.map Fin.val (List.finRange n) = List.range n := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp

theorem flatMap_map' {α β γ : Type} (l : List α) (f : α → β) (g : β → List γ) :
    (List.map f l).flatMap g = l.flatMap fun a => g (f a) := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]

theorem flatMap_finRange (n : ℕ) (g : ℕ → List ℕ) :
    (List.finRange n).flatMap (fun j : Fin n => g j) = (List.range n).flatMap g := by
  rw [← map_val_finRange n, flatMap_map']

theorem members_inst (F : Formula) (j : Fin (inst F).m) :
    List.map Fin.val ((inst F).members j) = memb F j := by
  unfold Instance.members memb
  have hq : (fun i : Fin (inst F).n => decide (i ∈ (inst F).F j)) =
      fun i : Fin (inst F).n => decide ((i : ℕ) ∈ (sets F).getD j []) :=
    funext fun i => by rw [decide_eq_decide]; exact mem_F_iff F j i
  rw [hq]
  change List.map Fin.val (List.filter _ (List.finRange (2 * vars F))) = _
  rw [← map_val_finRange (2 * vars F), List.filter_map]
  rfl

theorem filter_range_pair {n a : ℕ} (h : a + 1 < n) :
    (List.range n).filter (fun e => decide (e ∈ [a, a + 1])) = [a, a + 1] := by
  have hn : n = (a + 2) + (n - (a + 2)) := by omega
  rw [hn, List.range_add, List.filter_append, show a + 2 = a + 2 from rfl, List.range_add,
    List.filter_append]
  have h1 : (List.range a).filter (fun e => decide (e ∈ [a, a + 1])) = [] :=
    List.filter_eq_nil_iff.mpr fun e he => by simp at he ⊢; omega
  have h2 : ((List.range (n - (a + 2))).map (a + 2 + ·)).filter
      (fun e => decide (e ∈ [a, a + 1])) = [] :=
    List.filter_eq_nil_iff.mpr fun e he => by
      obtain ⟨t, -, rfl⟩ := List.mem_map.mp he; simp; omega
  rw [h1, h2]
  simp [List.range_succ]

theorem memb_pair (F : Formula) {j : ℕ} (hj : j < vars F) : memb F j = [2 * j, 2 * j + 1] := by
  unfold memb
  rw [sets_getD_pair F hj]
  exact filter_range_pair (by omega)

theorem memb_clause (F : Formula) {c : ℕ} (hc : c < F.length) :
    memb F (vars F + c) =
      (List.range (2 * vars F)).filter fun e => decide (e ∈ (F.getD c []).map elem) := by
  unfold memb; rw [sets_getD_clause F hc]

/-! ### The output -/

/-- The pairs: `2, 2j, 2j+1` for each variable. -/
def pairsOut (V : ℕ) : List ℕ :=
  (List.range V).flatMap fun j => bitsNat 2 ++ (bitsNat (2 * j) ++ bitsNat (2 * j + 1))

/-- The clause sets. -/
def clausesOut (F : Formula) : List ℕ :=
  (List.range F.length).flatMap fun c => setBits (memb F (vars F + c))

/-- The output of the program on the formula `F`. -/
def out (F : Formula) : List ℕ :=
  bitsNat (2 * vars F) ++ bitsNat (vars F + F.length) ++ bitsNat (vars F) ++
    (pairsOut (vars F) ++ clausesOut F)

theorem set_eq (F : Formula) (j : Fin (inst F).m) :
    bitsNat ((inst F).members j).length ++
      List.flatMap bitsNat (List.map Fin.val ((inst F).members j)) = setBits (memb F j) := by
  rw [setBits, ← members_inst, List.length_map]

theorem natBits_encodeInstance_inst (F : Formula) :
    natBits (encodeInstance (inst F) (vars F)) = out F := by
  rw [natBits_encodeInstance]
  simp only [set_eq]
  rw [flatMap_finRange (inst F).m (fun j => setBits (memb F j))]
  have h1 : (inst F).n = 2 * vars F := rfl
  have h2 : (inst F).m = vars F + F.length := rfl
  rw [h1, h2]
  unfold out pairsOut clausesOut
  rw [List.range_add, List.flatMap_append, flatMap_map']
  have hp : (List.range (vars F)).flatMap (fun j => setBits (memb F j)) =
      (List.range (vars F)).flatMap fun j =>
        bitsNat 2 ++ (bitsNat (2 * j) ++ bitsNat (2 * j + 1)) := by
    refine List.flatMap_congr fun j hj => ?_
    rw [memb_pair F (List.mem_range.mp hj)]
    simp [setBits]
  rw [hp]

/-- The reduction, on the zeros and ones the machine reads and writes. -/
def red (y : List ℕ) : List ℕ := natBits (reduceWord (bitsOf y))

theorem red_natBits (w : Word) : red (natBits w) = natBits (reduceWord w) := by simp [red]

theorem red_eq (y : List ℕ) : red y = out (parseF (bitsOf y)) := by
  rw [red, reduceWord]
  exact natBits_encodeInstance_inst _

end Lax496464Proofs.HittingSet.Model
