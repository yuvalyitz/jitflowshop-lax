import Lax808846Proofs.Tactic

/-! Reading the prefixed tape `x.length :: x` into the array `"a"`, in IMP+.

Every program of this submission starts with `readTape`: it reads the length into `"rt_n"` and then
the word into `"a"`, so that the rest of the program works on an array of known length. -/

namespace Lax496464Proofs.WHierarchy.Machine.ReadTape

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The value of a scalar. -/
abbrev V (s : String) : Expr := .var s

/-- One step of the copy: read an entry and store it at position `rt_i`. -/
def readBody : Com :=
  .seq (.read "rt_v") (.seq (.store "a" (V "rt_i") (V "rt_v"))
    (.assign "rt_i" (.add (V "rt_i") (.lit 1))))

/-- The copy loop, from `rt_i = 0` to `rt_n`. -/
def readLoop : Com := .seq (.assign "rt_i" (.lit 0)) (.while (.lt (V "rt_i") (V "rt_n")) readBody)

/-- Read the length into `rt_n`, then the word into `a`. -/
def readTape : Com := .seq (.read "rt_n") readLoop

/-- The scalars `readTape` assigns. -/
def readVars : List String := ["rt_n", "rt_i", "rt_v"]

theorem take_append_set (x : List ℕ) (i : ℕ) (h : i < x.length) :
    (x.take i ++ List.replicate (x.length - i) 0).set i (x.getD i 0) =
      x.take (i + 1) ++ List.replicate (x.length - (i + 1)) 0 := by
  have hlen : (x.take i).length = i := by simp; omega
  have hrep : x.length - i = (x.length - (i + 1)) + 1 := by omega
  have htake : x.take (i + 1) = x.take i ++ [x.getD i 0] := by
    rw [List.take_add_one, List.getD_eq_getElem?_getD]
    simp [List.getElem?_eq_getElem h]
  rw [hrep, List.replicate_succ, List.set_append_right _ _ (by omega), hlen, htake]
  simp

theorem drop_eq_getD_cons {x : List ℕ} {k : ℕ} (h : k < x.length) :
    x.drop k = x.getD k 0 :: x.drop (k + 1) := by
  rw [List.drop_eq_getElem_cons h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The copy invariant: `x` copied up to `rt_i`, the tape consumed accordingly. -/
def CopyInv (x : List ℕ) (σ0 : Env) (σ : Env) : Prop :=
  σ.vars "rt_n" = x.length ∧ σ.vars "rt_i" ≤ x.length ∧
    σ.arrs "a" = x.take (σ.vars "rt_i") ++ List.replicate (x.length - σ.vars "rt_i") 0 ∧
    σ.inp = x.drop (σ.vars "rt_i") ∧ σ.out = σ0.out ∧
    (∀ y, y ∉ readVars → σ.vars y = σ0.vars y) ∧ (∀ b, b ≠ "a" → σ.arrs b = σ0.arrs b)

theorem readBody_spec (x : List ℕ) (σ0 : Env) {B : ℕ} (hB : ∀ v ∈ x, v < B)
    (hlen : x.length < B) :
    Spec B (fun σ => CopyInv x σ0 σ ∧ σ.vars "rt_i" < x.length) readBody
      (fun σ σ' => CopyInv x σ0 σ' ∧ σ'.vars "rt_i" = σ.vars "rt_i" + 1) 12 := by
  unfold readBody
  refine Spec.pre (P := fun σ => CopyInv x σ0 σ ∧ σ.vars "rt_i" < x.length ∧
    σ.inp = x.getD (σ.vars "rt_i") 0 :: x.drop (σ.vars "rt_i" + 1) ∧
    σ.vars "rt_i" < (σ.arrs "a").length ∧ x.getD (σ.vars "rt_i") 0 < B ∧
    σ.vars "rt_i" + 1 < B) ?_ ?_
  · run_vcg
    · have hc : CopyInv x σ0 σ := ‹_›
      have hlt : σ.vars "rt_i" < x.length := ‹_›
      have hin : σ.inp = x.getD (σ.vars "rt_i") 0 :: List.drop (σ.vars "rt_i" + 1) x := ‹_›
      obtain ⟨hn, hi, ha, -, hout, hvars, harrs⟩ := hc
      have hset := take_append_set x _ hlt
      refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp [Env.setVar, Env.setArr, hn]
      · simp [Env.setVar, Env.setArr]; omega
      · simp only [Env.setVar, Env.setArr, hin, List.headD_cons, ↓reduceIte, ha]
        exact hset
      · simp [Env.setVar, Env.setArr, hin]
      · simp [Env.setVar, Env.setArr, hout]
      · intro y hy
        simp only [readVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [Env.setVar, Env.setArr, hy.2.1, hy.2.2]
        exact hvars y (by simp [readVars]; exact hy)
      · intro b hb
        simp [Env.setVar, Env.setArr, hb, harrs b hb]
      · simp [Env.setVar, Env.setArr]
    · have hin : σ.inp = x.getD (σ.vars "rt_i") 0 :: List.drop (σ.vars "rt_i" + 1) x := ‹_›
      have hv : x.getD (σ.vars "rt_i") 0 < B := ‹_›
      rw [List.getD_eq_getElem?_getD] at hv
      simp [Env.setVar, hin, hv]
  · intro σ ⟨hI, hlt⟩
    obtain ⟨hn, hi, ha, hinp, -⟩ := id hI
    have hmem : x.getD (σ.vars "rt_i") 0 ∈ x := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem _
    refine ⟨hI, hlt, by rw [hinp]; exact drop_eq_getD_cons hlt, by rw [ha]; simp; omega,
      hB _ hmem, by omega⟩

theorem readLoop_spec (x : List ℕ) (σ0 : Env) {B : ℕ} (hB : ∀ v ∈ x, v < B)
    (hlen : x.length < B) :
    Spec B (fun σ => CopyInv x σ0 (σ.setVar "rt_i" 0)) readLoop
      (fun _ σ' => CopyInv x σ0 σ' ∧ σ'.vars "rt_i" = x.length) (16 * x.length + 6) :=
  Spec.forRangeZero "rt_i" "rt_n" (CopyInv x σ0) x.length 12 hlen (fun _ h => h.2.1)
    (fun _ h => h.1) (readBody_spec x σ0 hB hlen)

/-- **The reader.** From a state whose tape is `x.length :: x` and whose array `a` has `x.length`
zeros, `readTape` ends with `a = x`, `rt_n = x.length`, the tape consumed, the output unchanged, and
every other scalar and array as before. -/
theorem readTape_spec (x : List ℕ) (σ0 : Env) {B : ℕ} (hB : ∀ v ∈ x, v < B)
    (hlen : x.length < B) (hinp : σ0.inp = x.length :: x)
    (ha : σ0.arrs "a" = List.replicate x.length 0) :
    Spec B (fun σ => σ = σ0) readTape
      (fun _ σ' => σ'.arrs "a" = x ∧ σ'.vars "rt_n" = x.length ∧ σ'.inp = [] ∧
        σ'.out = σ0.out ∧ (∀ y, y ∉ readVars → σ'.vars y = σ0.vars y) ∧
        (∀ b, b ≠ "a" → σ'.arrs b = σ0.arrs b)) (16 * x.length + 7) := by
  have h1 : Spec B (fun σ => σ = σ0) (.read "rt_n")
      (fun σ σ' => σ' = { σ.setVar "rt_n" x.length with inp := x }) 1 :=
    Spec.read (v := fun _ => x.length) (rest := fun _ => x) fun σ h => by rw [h, hinp]
  refine Spec.mono (Spec.seq h1 (readLoop_spec x σ0 hB hlen) ?_ ?_) (by omega)
  · rintro σ σ' rfl rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Env.setVar]
    · simp [Env.setVar]
    · simp [Env.setVar, ha]
    · simp [Env.setVar]
    · simp [Env.setVar]
    · intro y hy
      simp only [readVars, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [Env.setVar, hy.1, hy.2.1]
    · intro b _; simp [Env.setVar]
  · rintro σ σ' σ'' rfl - ⟨⟨hn, -, ha', hinp', hout, hvars, harrs⟩, hi⟩
    rw [hi] at ha' hinp'
    exact ⟨by simpa using ha', hn, by simpa using hinp', hout, hvars, harrs⟩

end Lax496464Proofs.WHierarchy.Machine.ReadTape
