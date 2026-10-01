import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgScan

/-! # Σ₁[2] model checking to Clique: decoding the vertices, and the atom test

Every value the adjacency test reads is small (`Small`, `tok_small`, `elL_le`); `decC_spec`: the
decoding of the two vertices into their valuations, candidates and rows. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj1

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Core Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgScan
open Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-! ### Bounds on the tokenizer's lists -/

/-- The entries of the tokenizer's lists are small. -/
def Small (x : List ℕ) (st : TS) : Prop :=
  (∀ v ∈ st.ab, v ≤ x.length) ∧ (∀ v ∈ st.ar, v ≤ Mmax x) ∧ (∀ v ∈ st.vs, v ≤ Mmax x)

theorem small_step (x : List ℕ) {st : TS} (h : Small x st) : Small x (tokStep x st) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hr : ∀ i, rd x i ≤ Mmax x := fun i => getD_le_Mmax x i
  have hh : ∀ i, hp x i ≤ x.length := hp_le x
  unfold tokStep
  split_ifs
  · exact ⟨h1, h2, h3⟩
  · refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩ <;>
      simp only [relStep, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    · rcases hv with hv | rfl
      · exact h1 v hv
      · split_ifs <;> simp [hh]
    · rcases hv with hv | rfl
      · exact h2 v hv
      · split_ifs <;> simp [hr]
    · rcases hv with hv | rfl | rfl
      · exact h3 v hv
      · split_ifs <;> simp [hr]
      · split_ifs <;> simp [hr]
  · refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩ <;>
      simp only [eqStep, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    · rcases hv with hv | rfl
      · exact h1 v hv
      · simp
    · rcases hv with hv | rfl
      · exact h2 v hv
      · simp
    · rcases hv with hv | rfl | rfl
      · exact h3 v hv
      · exact hr _
      · exact hr _
  · exact ⟨h1, h2, h3⟩
  · exact ⟨h1, h2, h3⟩

theorem small_iter (x : List ℕ) : ∀ n, Small x ((tokStep x)^[n] (tokInit x))
  | 0 => by simp [Small, tokInit]
  | n + 1 => by rw [Function.iterate_succ_apply']; exact small_step x (small_iter x n)

theorem tok_small (x : List ℕ) : Small x (tok x) := small_iter x x.length

theorem getD_le_of {l : List ℕ} {b : ℕ} (h : ∀ v ∈ l, v ≤ b) (i : ℕ) : l.getD i 0 ≤ b := by
  rw [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i l.length with hi | hi
  · rw [List.getElem?_eq_getElem hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none hi]; simp

theorem elL_le (x : List ℕ) : ∀ v ∈ elL x, v ≤ Mmax x := by
  intro v hv
  unfold elL at hv
  rcases List.mem_append.1 hv with h | h
  · exact le_Mmax (List.mem_of_mem_filter h)
  · have h1 := List.mem_range.1 h
    have h2 := ProgElb.limX_le_N x
    have h3 : NsX x ≤ Mmax x := getD_le_Mmax x _
    omega

/-! ### Decoding -/

theorem sub_div_mul (a n : ℕ) : a - a / n * n = a % n := by
  rw [Nat.mod_def, Nat.mul_comm]

set_option maxHeartbeats 1000000 in
theorem decC_spec {B : ℕ} :
    Spec B (fun σ => σ.vars "gs" < B ∧ σ.vars "gt" < B ∧ σ.vars "zk" < B ∧ σ.vars "zne" < B ∧
        σ.vars "gs" / σ.vars "zk" ≤ σ.vars "gs" ∧ σ.vars "gt" / σ.vars "zk" ≤ σ.vars "gt" ∧
        σ.vars "gs" / σ.vars "zk" * σ.vars "zk" ≤ σ.vars "gs" ∧
        σ.vars "gt" / σ.vars "zk" * σ.vars "zk" ≤ σ.vars "gt" ∧
        σ.vars "gs" / σ.vars "zk" / σ.vars "zne" ≤ σ.vars "gs" / σ.vars "zk" ∧
        σ.vars "gt" / σ.vars "zk" / σ.vars "zne" ≤ σ.vars "gt" / σ.vars "zk" ∧
        σ.vars "gs" / σ.vars "zk" / σ.vars "zne" * σ.vars "zne" ≤ σ.vars "gs" / σ.vars "zk" ∧
        σ.vars "gt" / σ.vars "zk" / σ.vars "zne" * σ.vars "zne" ≤ σ.vars "gt" / σ.vars "zk")
      decC
      (fun σ σ' => σ'.vars "r1" = σ.vars "gs" % σ.vars "zk" ∧
        σ'.vars "e1" = σ.vars "gs" / σ.vars "zk" % σ.vars "zne" ∧
        σ'.vars "c1" = σ.vars "gs" / σ.vars "zk" / σ.vars "zne" ∧
        σ'.vars "r2" = σ.vars "gt" % σ.vars "zk" ∧
        σ'.vars "e2" = σ.vars "gt" / σ.vars "zk" % σ.vars "zne" ∧
        σ'.vars "c2" = σ.vars "gt" / σ.vars "zk" / σ.vars "zne") 100 := by
  unfold decC
  run_vcg
  all_goals (simp [sub_div_mul]; try omega)

theorem decC_pre {B : ℕ} {σ : Env} (h1 : σ.vars "gs" < B) (h2 : σ.vars "gt" < B)
    (h3 : σ.vars "zk" < B) (h4 : σ.vars "zne" < B) :
    σ.vars "gs" < B ∧ σ.vars "gt" < B ∧ σ.vars "zk" < B ∧ σ.vars "zne" < B ∧
        σ.vars "gs" / σ.vars "zk" ≤ σ.vars "gs" ∧ σ.vars "gt" / σ.vars "zk" ≤ σ.vars "gt" ∧
        σ.vars "gs" / σ.vars "zk" * σ.vars "zk" ≤ σ.vars "gs" ∧
        σ.vars "gt" / σ.vars "zk" * σ.vars "zk" ≤ σ.vars "gt" ∧
        σ.vars "gs" / σ.vars "zk" / σ.vars "zne" ≤ σ.vars "gs" / σ.vars "zk" ∧
        σ.vars "gt" / σ.vars "zk" / σ.vars "zne" ≤ σ.vars "gt" / σ.vars "zk" ∧
        σ.vars "gs" / σ.vars "zk" / σ.vars "zne" * σ.vars "zne" ≤ σ.vars "gs" / σ.vars "zk" ∧
        σ.vars "gt" / σ.vars "zk" / σ.vars "zne" * σ.vars "zne" ≤ σ.vars "gt" / σ.vars "zk" :=
  ⟨h1, h2, h3, h4, Nat.div_le_self _ _, Nat.div_le_self _ _, Nat.div_mul_le_self _ _,
    Nat.div_mul_le_self _ _, Nat.div_le_self _ _, Nat.div_le_self _ _, Nat.div_mul_le_self _ _,
    Nat.div_mul_le_self _ _⟩

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgAdj1
