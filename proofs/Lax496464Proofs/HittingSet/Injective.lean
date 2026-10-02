import Lax496464Proofs.HittingSet.Model
import Lax496464Proofs.HittingSet.Words
import Lax391470Proofs.Encoding
import Lax429075.EncodingCorrect
import Lax429075Proofs.DecoderSoundness

/-!
# The Encoding Is Injective

The number code is prefix-free, and a set is written as its size followed by as many
members, so a word determines the instance it encodes and the solution size.
-/

namespace Lax496464Proofs.HittingSet.Injective

open Lax434930.PolynomialTime Lax496464.HittingSet Lax496464.HittingSetFromSat
open Lax391470Proofs.Encoding Lax496464Proofs.HittingSet.Model

theorem peel {a b : ℕ} {x y : Word} (h : encodeNat a ++ x = encodeNat b ++ y) :
    a = b ∧ x = y :=
  encodeNat_prefixFree a b x y h

/-- A set as a word: its size then its members. -/
def setWord (c : ℕ) (l : List ℕ) : Word := encodeNat c ++ l.flatMap encodeNat

/-- A family as a word. -/
def famWord (cs : List (ℕ × List ℕ)) : Word := cs.flatMap fun s => setWord s.1 s.2

/-- The sets of an instance, as sizes and member lists. -/
def setsOf (P : Instance) : List (ℕ × List ℕ) :=
  (List.finRange P.m).map fun j => ((P.F j).card, (P.members j).map Fin.val)

theorem encodeInstance_eq (P : Instance) (k : ℕ) :
    encodeInstance P k = encodeNat P.n ++ (encodeNat P.m ++ (encodeNat k ++ famWord (setsOf P))) := by
  unfold encodeInstance famWord setsOf setWord
  simp only [List.append_assoc, List.flatMap_map, bind_pure_comp, List.map_eq_map]

theorem flatMap_peel : ∀ (l l' : List ℕ) (x y : Word), l.length = l'.length →
    l.flatMap encodeNat ++ x = l'.flatMap encodeNat ++ y → l = l' ∧ x = y
  | [], [], x, y, _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, h, _ => by simp at h
  | a :: l, b :: l', x, y, hl, h => by
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨rfl, h2⟩ := peel h
      obtain ⟨rfl, rfl⟩ := flatMap_peel l l' x y (by simpa using hl) h2
      exact ⟨rfl, rfl⟩

theorem famWord_peel : ∀ (cs cs' : List (ℕ × List ℕ)) (x y : Word), cs.length = cs'.length →
    (∀ s ∈ cs, s.1 = s.2.length) → (∀ s ∈ cs', s.1 = s.2.length) →
    famWord cs ++ x = famWord cs' ++ y → cs = cs' ∧ x = y
  | [], [], x, y, _, _, _, h => ⟨rfl, by simpa [famWord] using h⟩
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | s :: cs, s' :: cs', x, y, hl, h1, h2, h => by
      simp only [famWord, List.flatMap_cons, List.append_assoc, setWord] at h
      obtain ⟨hc, h3⟩ := peel h
      have e1 := h1 s (List.mem_cons_self ..)
      have e2 := h2 s' (List.mem_cons_self ..)
      obtain ⟨hm, h4⟩ := flatMap_peel s.2 s'.2 _ _ (by rw [← e1, ← e2, hc]) h3
      obtain ⟨rfl, rfl⟩ := famWord_peel cs cs' x y (by simpa using hl)
        (fun t ht => h1 t (List.mem_cons_of_mem _ ht))
        (fun t ht => h2 t (List.mem_cons_of_mem _ ht)) h4
      exact ⟨by rw [Prod.ext_iff.mpr ⟨hc, hm⟩], rfl⟩

theorem setsOf_sizes (P : Instance) : ∀ s ∈ setsOf P, s.1 = s.2.length := by
  intro s hs
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hs
  simp only [List.length_map]
  exact card_eq_length_members P j

theorem mem_members_iff (P : Instance) (j : Fin P.m) (i : Fin P.n) :
    i ∈ P.members j ↔ i ∈ P.F j := by
  simp [Instance.members]

/-- Two instances of the same dimensions with the same member lists are equal. -/
theorem instance_ext {P P' : Instance} (hn : P.n = P'.n) (hm : P.m = P'.m)
    (hs : setsOf P = setsOf P') : P = P' := by
  obtain ⟨n, m, F⟩ := P
  obtain ⟨n', m', F'⟩ := P'
  simp only at hn hm
  subst hn hm
  congr
  funext j
  have hj : ((F j).card, (Instance.members ⟨n, m, F⟩ j).map Fin.val) =
      ((F' j).card, (Instance.members ⟨n, m, F'⟩ j).map Fin.val) := by
    have h1 := congrArg (fun l => l.getD (j : ℕ) (0, [])) hs
    simp only [setsOf] at h1
    rw [List.getD_eq_getElem _ _ (by simp [j.isLt]), List.getD_eq_getElem _ _ (by simp [j.isLt]),
      List.getElem_map, List.getElem_map, List.getElem_finRange] at h1
    exact h1
  have hm := (Prod.mk.inj hj).2
  ext i
  have h1 := mem_members_iff ⟨n, m, F⟩ j i
  have h2 := mem_members_iff ⟨n, m, F'⟩ j i
  simp only at h1 h2
  rw [← h1, ← h2]
  have : (i : ℕ) ∈ List.map Fin.val (Instance.members ⟨n, m, F⟩ j) ↔
      (i : ℕ) ∈ List.map Fin.val (Instance.members ⟨n, m, F'⟩ j) := by rw [hm]
  simpa [List.mem_map, Fin.val_inj] using this

/-- **The encoding is injective.** -/
theorem encodeInstance_inj {P P' : Instance} {k k' : ℕ}
    (h : encodeInstance P k = encodeInstance P' k') : P = P' ∧ k = k' := by
  rw [encodeInstance_eq, encodeInstance_eq] at h
  obtain ⟨hn, h⟩ := peel h
  obtain ⟨hm, h⟩ := peel h
  obtain ⟨hk, h⟩ := peel h
  have hlen : (setsOf P).length = (setsOf P').length := by simp [setsOf, hm]
  obtain ⟨hs, -⟩ := famWord_peel (setsOf P) (setsOf P') [] [] hlen (setsOf_sizes P)
    (setsOf_sizes P') (by simpa using h)
  exact ⟨instance_ext hn hm hs, hk⟩

/-- Correctness of the reduction into the language. -/
theorem reduceWord_correct (w : Word) :
    w ∈ Lax429075.Satisfiability.SAT ↔ reduceWord w ∈ HittingSetLanguage := by
  rw [Lax496464Proofs.HittingSet.Words.reduce_correct]
  constructor
  · intro h; exact ⟨(reduce w).1, (reduce w).2, rfl, h⟩
  · rintro ⟨P, k, hw, h⟩
    obtain ⟨rfl, rfl⟩ := encodeInstance_inj hw
    exact h

end Lax496464Proofs.HittingSet.Injective
