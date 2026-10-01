import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs

/-!
# Σ₁[2] model checking to Clique: tools for the program proofs

Arrays that are filled from the front (`pad l n`: the list `l`, then zeros up to length `n`), the
guarded read `rdV`, and framing (`Keep`).
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs

/-! ### Arrays filled from the front -/

/-- The list `l` followed by zeros up to length `n`. -/
def pad (l : List ℕ) (n : ℕ) : List ℕ := l ++ List.replicate (n - l.length) 0

theorem length_pad {l : List ℕ} {n : ℕ} (h : l.length ≤ n) : (pad l n).length = n := by
  unfold pad; simp; omega

theorem pad_nil (n : ℕ) : pad [] n = List.replicate n 0 := by simp [pad]

theorem pad_set {l : List ℕ} {n : ℕ} (h : l.length < n) (v : ℕ) :
    (pad l n).set l.length v = pad (l ++ [v]) n := by
  unfold pad
  have hrep : n - l.length = (n - (l ++ [v]).length) + 1 := by simp; omega
  rw [hrep, List.replicate_succ, List.set_append_right _ _ (le_refl _), Nat.sub_self]
  simp

theorem getD_pad (l : List ℕ) (n i : ℕ) : (pad l n).getD i 0 = l.getD i 0 := by
  unfold pad
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i l.length with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right h, List.getElem?_eq_none h]
    simp only [List.getElem?_replicate, Option.getD_none]
    split_ifs <;> simp

theorem pad_set' {l : List ℕ} {n i : ℕ} (hi : i = l.length) (h : l.length < n) (v : ℕ) :
    (pad l n).set i v = pad (l ++ [v]) n := by
  subst hi; exact pad_set h v

/-! ### Reading the word -/

theorem rd_of_ge {x : List ℕ} {i : ℕ} (h : x.length ≤ i) : rd x i = 0 := by
  unfold rd; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; rfl

theorem rd_lt {x : List ℕ} {B : ℕ} (hB : ∀ v ∈ x, v < B) (h0 : 0 < B) (i : ℕ) : rd x i < B := by
  unfold rd
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i x.length with h | h
  · rw [List.getElem?_eq_getElem h]; exact hB _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]; exact h0

/-- **The guarded read.** -/
theorem rdV_spec {x : List ℕ} {B : ℕ} (hB : ∀ v ∈ x, v < B) (h0 : 0 < B) (dst b : String)
    (k : ℕ) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars b + k < B ∧
        x.length < B) (rdV dst b k)
      (fun σ σ' => σ' = σ.setVar dst (rd x (σ.vars b + k))) 12 := by
  have hlt : ∀ i, x.getD i 0 < B := fun i => rd_lt hB h0 i
  unfold rdV
  run_vcg
  all_goals simp_all [rd]

/-! ### Framing -/

/-- Nothing but the scalars in `S` changed; arrays and input tape are as before. -/
def Keep (S : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp

/-- Framing a specification of a command that never stores and never reads. -/
theorem Spec.keep {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : c.warrs = []) (hr : ¬ c.reads) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Keep S σ σ') K :=
  Spec.post h.frame fun _ _ _ ⟨hq, hv, ha, hi, _⟩ =>
    ⟨hq, fun y hy => hv y fun hm => hy (hw y hm),
      funext fun a => ha a (by rw [hwa]; simp), hi hr⟩

/-- Framing with stores: the scalars in `S` and the arrays in `T` may change. -/
def KeepA (S T : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ (∀ a, a ∉ T → σ'.arrs a = σ.arrs a) ∧ σ'.inp = σ.inp ∧
    σ'.out = σ.out

theorem Spec.keepA {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S T : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : ∀ a, a ∈ c.warrs → a ∈ T) (hr : ¬ c.reads) (hnw : c.NoWrite) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ KeepA S T σ σ') K :=
  Spec.post h.frame fun _ _ _ ⟨hq, hv, ha, hi, ho⟩ =>
    ⟨hq, fun y hy => hv y fun hm => hy (hw y hm), fun a hy => ha a fun hm => hy (hwa a hm),
      hi hr, ho hnw⟩

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
