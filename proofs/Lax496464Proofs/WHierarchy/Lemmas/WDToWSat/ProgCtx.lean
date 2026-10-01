import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath

/-!
# Frames, the value bound and the context of the program's main part

`Frame S A σ σ'`: only the scalars in `S` and the arrays in `A` changed, the input tape did not.
`BF D x B`: the facts about the value bound `B` the program needs. `Ctx D x σ`: the arrays and
scalars set up before the assignments are enumerated.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath

/-! ### Frames -/

/-- Only the scalars in `S` and the arrays in `A` changed; the input did not. -/
def Frame (S A : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ (∀ b, b ∉ A → σ'.arrs b = σ.arrs b) ∧ σ'.inp = σ.inp

theorem Frame.refl (S A : List String) (σ : Env) : Frame S A σ σ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem Frame.trans {S A : List String} {σ σ' σ'' : Env} (h1 : Frame S A σ σ')
    (h2 : Frame S A σ' σ'') : Frame S A σ σ'' :=
  ⟨fun y hy => (h2.1 y hy).trans (h1.1 y hy), fun b hb => (h2.2.1 b hb).trans (h1.2.1 b hb),
    h2.2.2.trans h1.2.2⟩

theorem Frame.mono {S A S' A' : List String} {σ σ' : Env} (h : Frame S A σ σ')
    (hS : ∀ y ∈ S, y ∈ S') (hA : ∀ b ∈ A, b ∈ A') : Frame S' A' σ σ' :=
  ⟨fun y hy => h.1 y fun hm => hy (hS y hm), fun b hb => h.2.1 b fun hm => hb (hA b hm), h.2.2⟩

theorem Frame.setVar {S A : List String} (σ : Env) {y : String} (h : y ∈ S) (v : ℕ) :
    Frame S A σ (σ.setVar y v) :=
  ⟨fun z hz => by
    have : z ≠ y := fun e => hz (e ▸ h)
    simp [Env.setVar, this], fun _ _ => rfl, rfl⟩

/-- **Framing a specification** by the syntax of its command. -/
theorem Spec.framed {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S A : List String) (hw : ∀ y ∈ c.wvars, y ∈ S)
    (ha : ∀ b ∈ c.warrs, b ∈ A) (hr : ¬ c.reads) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Frame S A σ σ') K :=
  Spec.post h.frame fun _ _ _ ⟨hq, hv, harr, hi, _⟩ =>
    ⟨hq, fun y hy => hv y fun hm => hy (hw y hm), fun b hb => harr b fun hm => hb (ha b hm), hi hr⟩

/-- Framing, with the output unchanged. -/
theorem Spec.framedOut {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S A : List String) (hw : ∀ y ∈ c.wvars, y ∈ S)
    (ha : ∀ b ∈ c.warrs, b ∈ A) (hr : ¬ c.reads) (hnw : c.NoWrite) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Frame S A σ σ' ∧ σ'.out = σ.out) K :=
  Spec.post h.frame fun _ _ _ ⟨hq, hv, harr, hi, ho⟩ =>
    ⟨hq, ⟨fun y hy => hv y fun hm => hy (hw y hm), fun b hb => harr b fun hm => hb (ha b hm),
      hi hr⟩, ho hnw⟩

theorem wvars_seqList : ∀ (cs : List Com) (y : String), y ∈ (seqList cs).wvars → ∃ c ∈ cs, y ∈ c.wvars
  | [], y, h => by simp [seqList] at h
  | c :: cs, y, h => by
    simp only [seqList, Com.wvars, List.mem_append] at h
    rcases h with h | h
    · exact ⟨c, by simp, h⟩
    · obtain ⟨d, hd, h'⟩ := wvars_seqList cs y h; exact ⟨d, by simp [hd], h'⟩

theorem warrs_seqList : ∀ (cs : List Com) (b : String), b ∈ (seqList cs).warrs → ∃ c ∈ cs, b ∈ c.warrs
  | [], b, h => by simp [seqList] at h
  | c :: cs, b, h => by
    simp only [seqList, Com.warrs, List.mem_append] at h
    rcases h with h | h
    · exact ⟨c, by simp, h⟩
    · obtain ⟨d, hd, h'⟩ := warrs_seqList cs b h; exact ⟨d, by simp [hd], h'⟩

theorem reads_seqList : ∀ (cs : List Com), (∀ c ∈ cs, ¬ c.reads) → ¬ (seqList cs).reads
  | [], _ => by simp [seqList]
  | c :: cs, h => by
    simp only [seqList, Com.reads, not_or]
    exact ⟨h c (by simp), reads_seqList cs fun d hd => h d (by simp [hd])⟩

/-! ### The value bound -/

/-- The constants of the program. -/
def cD (D : Data) : ℕ :=
  D.r + D.s + D.cnf.length + (D.cnf.map List.length).sum +
    (D.cnf.map fun C => (C.map fun l => l.atom.idxs.length).sum).sum +
    (D.rels.map fun p => p.1 + p.2 + 1).sum + 4

/-- **The facts about the value bound.** -/
structure BF (D : Data) (x : List ℕ) (B : ℕ) : Prop where
  entries : ∀ v ∈ x, v < B
  len : x.length + cD D + 2 < B
  t0 : x.length + D.s * kW x + D.r < B
  n : nW D x + 1 < B
  pw : (nW D x + 1) ^ (D.r + D.s) * (D.cnf.length + 2) + 2 < B
  ucap : LW D.s D.r x + x.length + 2 < B

theorem BF.getD_lt {D : Data} {x : List ℕ} {B : ℕ} (h : BF D x B) (p : ℕ) : x.getD p 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases hx : x[p]? with _ | v
  · have := h.len; simp; omega
  · exact h.entries v (List.mem_of_getElem? hx)

theorem BF.const {D : Data} {x : List ℕ} {B : ℕ} (h : BF D x B) : cD D + 2 < B := by
  have := h.len; omega

theorem BF.pow_le {D : Data} {x : List ℕ} {B : ℕ} (h : BF D x B) {e : ℕ} (he : e ≤ D.r + D.s) :
    (nW D x + 1) ^ e * (D.cnf.length + 2) < B := by
  have := h.pw
  have : (nW D x + 1) ^ e * (D.cnf.length + 2) ≤ (nW D x + 1) ^ (D.r + D.s) * (D.cnf.length + 2) :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) he)
  omega

theorem BF.npow_lt {D : Data} {x : List ℕ} {B : ℕ} (h : BF D x B) {e : ℕ} (he : e ≤ D.r + D.s) :
    nW D x ^ e < B := by
  have h1 := h.pow_le he
  have h2 : nW D x ^ e ≤ (nW D x + 1) ^ e := Nat.pow_le_pow_left (by omega) e
  nlinarith

/-- The count of the clauses, the codes of the tautologies. -/
theorem BF.count_lt {D : Data} {x : List ℕ} {B : ℕ} (h : BF D x B) :
    nW D x ^ D.r * D.cnf.length + nW D x ^ D.s < B ∧ 2 * nW D x ^ D.s + 1 < B := by
  have h1 := h.pw
  have hr : nW D x ^ D.r ≤ (nW D x + 1) ^ (D.r + D.s) :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hs : nW D x ^ D.s ≤ (nW D x + 1) ^ (D.r + D.s) :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  constructor
  · have : nW D x ^ D.r * D.cnf.length ≤ (nW D x + 1) ^ (D.r + D.s) * D.cnf.length :=
      Nat.mul_le_mul_right _ hr
    nlinarith
  · have : (nW D x + 1) ^ (D.r + D.s) * 2 ≤ (nW D x + 1) ^ (D.r + D.s) * (D.cnf.length + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    omega

/-! ### The context of the enumeration -/

/-- The arrays and scalars set up before the assignments are enumerated. -/
structure Ctx (D : Data) (x : List ℕ) (σ : Env) : Prop where
  a : σ.arrs "a" = x
  bo : σ.arrs "bo" = (List.range (spW x)).map (boW x)
  U : ∀ q < nW D x, (σ.arrs "U").getD q 0 = (U D x).getD q 0
  Ulen : nW D x ≤ (σ.arrs "U").length
  odlen : (σ.arrs "od").length = D.r
  n : σ.vars "w_n" = nW D x

theorem Ctx.frame {D : Data} {x : List ℕ} {σ σ' : Env} {S A : List String} (h : Ctx D x σ)
    (hf : Frame S A σ σ') (hS : "w_n" ∉ S) (hA : "a" ∉ A ∧ "bo" ∉ A ∧ "U" ∉ A ∧ "od" ∉ A) :
    Ctx D x σ' where
  a := by rw [hf.2.1 _ hA.1]; exact h.a
  bo := by rw [hf.2.1 _ hA.2.1]; exact h.bo
  U := by rw [hf.2.1 _ hA.2.2.1]; exact h.U
  Ulen := by rw [hf.2.1 _ hA.2.2.1]; exact h.Ulen
  odlen := by rw [hf.2.1 _ hA.2.2.2]; exact h.odlen
  n := by rw [hf.1 _ hS]; exact h.n

/-- The digits of an assignment, in `od`. -/
structure DsOk (D : Data) (x : List ℕ) (ds : List ℕ) : Prop where
  len : ds.length = D.r
  lt : ∀ d ∈ ds, d < nW D x

theorem DsOk.getD_lt {D : Data} {x ds : List ℕ} (h : DsOk D x ds) {j : ℕ} (hj : j < D.r) :
    ds.getD j 0 < nW D x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [h.len]; exact hj)]
  exact h.lt _ (List.getElem_mem _)

/-- Every element is below `N`, an entry of the word. -/
theorem U_getD_lt {D : Data} {x : List ℕ} {B : ℕ} (hB : BF D x B) (q : ℕ) :
    (U D x).getD q 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : (U D x)[q]? with _ | v
  · have := hB.len; simp; omega
  · have := lt_of_mem_UW (List.mem_of_getElem? h)
    have h2 := hB.getD_lt (1 + spW x)
    unfold NW at this; simp only [Option.getD_some]; omega

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx
