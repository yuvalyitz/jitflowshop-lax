import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.ProgDefs

/-! # The adjacency matrix, stage by stage

`matS x U J` is the matrix after the blocks of the vertices below `U` and the entries of the block of
`U` below position `J` have been entered; `matF x` is the finished matrix, entry `u n + v` being `1`
exactly when `v` is listed in the block of `u`. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.FillMath

open Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math Lax496464Proofs.WHierarchy.Reductions.CliqueIS.ProgDefs

/-- Position `p` has been set once the blocks below `U` and the block of `U` below `J` are in. -/
def Stage (x : List ℕ) (U J p : ℕ) : Prop :=
  (∃ u < U, ∃ j, offAt x u ≤ j ∧ j < offAt x (u + 1) ∧ u * nOf x + tgtAt x j = p) ∨
    (∃ j, offAt x U ≤ j ∧ j < J ∧ U * nOf x + tgtAt x j = p)

open Classical in
/-- The matrix at a stage. -/
noncomputable def matS (x : List ℕ) (U J : ℕ) : List ℕ :=
  arrOf (nOf x * nOf x) (fun p => if Stage x U J p then 1 else 0)

/-- The finished matrix. -/
def matF (x : List ℕ) : List ℕ :=
  arrOf (nOf x * nOf x) (fun p => if inBlock x (p / nOf x) (p % nOf x) then 1 else 0)

@[simp] theorem length_matS (x : List ℕ) (U J : ℕ) : (matS x U J).length = nOf x * nOf x := by
  simp [matS]

@[simp] theorem length_matF (x : List ℕ) : (matF x).length = nOf x * nOf x := by
  simp [matF]

theorem matS_zero (x : List ℕ) : matS x 0 (offAt x 0) = List.replicate (nOf x * nOf x) 0 := by
  rw [replicate_eq_arrOf]
  unfold matS
  refine arrOf_congr fun p _ => ?_
  rw [if_neg]
  rintro (⟨u, hu, -⟩ | ⟨j, h1, h2, -⟩)
  · omega
  · omega

theorem matS_step (x : List ℕ) {U J : ℕ} (hJ : offAt x U ≤ J) :
    (matS x U J).set (U * nOf x + tgtAt x J) 1 = matS x U (J + 1) := by
  unfold matS
  rw [set_arrOf]
  refine arrOf_congr fun p _ => ?_
  by_cases hp : p = U * nOf x + tgtAt x J
  · rw [if_pos hp, if_pos]
    exact Or.inr ⟨J, hJ, by omega, hp.symm⟩
  · rw [if_neg hp]
    congr 1
    apply propext
    constructor
    · rintro (h | ⟨j, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j, h1, by omega, h3⟩
    · rintro (h | ⟨j, h1, h2, h3⟩)
      · exact Or.inl h
      · rcases Nat.lt_or_ge j J with hj | hj
        · exact Or.inr ⟨j, h1, hj, h3⟩
        · have : j = J := by omega
          subst this; exact absurd h3.symm hp

theorem matS_next (x : List ℕ) (U : ℕ) :
    matS x U (offAt x (U + 1)) = matS x (U + 1) (offAt x (U + 1)) := by
  unfold matS
  refine arrOf_congr fun p _ => ?_
  congr 1
  apply propext
  constructor
  · rintro (⟨u, hu, h⟩ | ⟨j, h1, h2, h3⟩)
    · exact Or.inl ⟨u, by omega, h⟩
    · exact Or.inl ⟨U, by omega, j, h1, h2, h3⟩
  · rintro (⟨u, hu, h⟩ | ⟨j, h1, h2, h3⟩)
    · rcases Nat.lt_or_ge u U with hu' | hu'
      · exact Or.inl ⟨u, hu', h⟩
      · have : u = U := by omega
        subst this; exact Or.inr h
    · omega

theorem mul_add_div_mod {n u t : ℕ} (ht : t < n) : (u * n + t) / n = u ∧ (u * n + t) % n = t := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt ht, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

theorem matS_final {x : List ℕ} (hd : Dom x) : matS x (nOf x) (offAt x (nOf x)) = matF x := by
  unfold matS matF
  refine arrOf_congr fun p hp => ?_
  have hn : 0 < nOf x := by
    rcases Nat.eq_zero_or_pos (nOf x) with h | h
    · rw [h] at hp; simp at hp
    · exact h
  congr 1
  apply propext
  rw [inBlock_iff]
  constructor
  · rintro (⟨u, hu, j, h1, h2, h3⟩ | ⟨j, h1, h2, -⟩)
    · have hj : j < offAt x (nOf x) := lt_of_lt_of_le h2 (hd.off_le (by omega) le_rfl)
      have ht := hd.tgt_lt j hj
      obtain ⟨hdiv, hmod⟩ := mul_add_div_mod (u := u) ht
      rw [h3] at hdiv hmod
      rw [hdiv]
      exact ⟨j, h1, h2, hmod.symm⟩
    · omega
  · rintro ⟨j, h1, h2, h3⟩
    have hu : p / nOf x < nOf x := by
      rw [Nat.div_lt_iff_lt_mul hn]; exact hp
    refine Or.inl ⟨p / nOf x, hu, j, h1, h2, ?_⟩
    rw [h3, Nat.mul_comm]
    exact Nat.div_add_mod p (nOf x)

theorem matF_getD {x : List ℕ} {s t : ℕ} (hs : s < nOf x) (ht : t < nOf x) :
    (matF x).getD (s * nOf x + t) 0 = if inBlock x s t then 1 else 0 := by
  have hlt : s * nOf x + t < nOf x * nOf x := by
    have : (s + 1) * nOf x ≤ nOf x * nOf x := Nat.mul_le_mul_right _ hs
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  unfold matF
  rw [getD_arrOf _ hlt]
  obtain ⟨h1, h2⟩ := mul_add_div_mod (u := s) ht
  rw [h1, h2]

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.FillMath
