import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics
import Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-!
# Σ₁[2] model checking to Clique: the header phase

`hdr` sets `zs = sX x`, fills `bs` with the block starts `hp x i` (`i < zs`), leaves the formula start
`hp x zs` in `zp` and the size of the universe in `zN`.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
open Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgBasics Lax496464Proofs.WHierarchy.Reductions.CliqueMCC.Bounds

/-- The value bound the header needs. -/
def HB (x : List ℕ) (B : ℕ) : Prop :=
  (∀ v ∈ x, v < B) ∧ (x.length + Mmax x + 4) * (x.length + Mmax x + 4) < B

theorem rd_le_Mmax (x : List ℕ) (i : ℕ) : rd x i ≤ Mmax x := getD_le_Mmax x i

theorem hp_le (x : List ℕ) : ∀ i, hp x i ≤ x.length
  | 0 => by simp only [hp, hp0]; split_ifs <;> omega
  | i + 1 => by simp only [hp, hpStep]; split_ifs <;> omega

theorem hp_succ' (x : List ℕ) (i : ℕ) :
    hp x (i + 1) = if x.length < hp x i + 1 + rd x (hp x i + 0) * rd x (i + 1) then x.length
      else hp x i + 1 + rd x (hp x i + 0) * rd x (i + 1) := by
  simp only [hp, hpStep, Nat.add_zero, Nat.add_comm 1 i]

/-- The block starts found so far. -/
def bsL (x : List ℕ) (i : ℕ) : List ℕ := (List.range i).map (hp x)

theorem length_bsL (x : List ℕ) (i : ℕ) : (bsL x i).length = i := by simp [bsL]

theorem bsL_set (x : List ℕ) {i : ℕ} (hi : i < sX x) :
    (pad (bsL x i) (sX x)).set i (hp x i) = pad (bsL x (i + 1)) (sX x) := by
  rw [pad_set' (length_bsL x i).symm (by rw [length_bsL]; exact hi)]
  simp [bsL, List.range_succ]

/-- The invariant of the header loop. -/
def HI (x : List ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧ σ.vars "zs" = sX x ∧ σ.vars "zhi" ≤ sX x ∧
    σ.vars "zp" = hp x (σ.vars "zhi") ∧ σ.arrs "bs" = pad (bsL x (σ.vars "zhi")) (sX x)

set_option maxHeartbeats 2000000 in
theorem hdrBody_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => HI x σ ∧ σ.vars "zhi" < sX x) hdrBody
      (fun σ σ' => HI x σ' ∧ σ'.vars "zhi" = σ.vars "zhi" + 1) 60 := by
  obtain ⟨hent, hW⟩ := hB
  have hM0 := rd_le_Mmax x 0
  have hsB : sX x + 2 < B := by unfold sX; nlinarith
  have hLB : x.length + 2 < B := by nlinarith
  have hprod : ∀ p i, p ≤ x.length → p + 1 + rd x (p + 0) * rd x (i + 1) < B := by
    intro p i hp
    have h1 := rd_le_Mmax x (p + 0)
    have h2 := rd_le_Mmax x (i + 1)
    have : rd x (p + 0) * rd x (i + 1) ≤ Mmax x * Mmax x := Nat.mul_le_mul h1 h2
    nlinarith
  have hrdB : ∀ i, rd x i < B := rd_lt hent (by omega)
  have hprod2 : ∀ i j, rd x i * rd x j < B := by
    intro i j
    have : rd x i * rd x j ≤ Mmax x * Mmax x :=
      Nat.mul_le_mul (rd_le_Mmax x i) (rd_le_Mmax x j)
    nlinarith
  unfold hdrBody
  refine Spec.pre (P := fun σ => HI x σ ∧ σ.vars "zhi" < sX x ∧
    σ.vars "zhi" < (σ.arrs "bs").length ∧ σ.vars "zp" ≤ x.length ∧ sX x + 2 < B ∧
    x.length + 2 < B ∧
    σ.vars "zp" + 1 + rd x (σ.vars "zp" + 0) * rd x (σ.vars "zhi" + 1) < B ∧
    (σ.arrs "bs").set (σ.vars "zhi") (σ.vars "zp") = pad (bsL x (σ.vars "zhi" + 1)) (sX x) ∧
    hp x (σ.vars "zhi" + 1) = (if x.length < σ.vars "zp" + 1 + rd x (σ.vars "zp" + 0) *
      rd x (σ.vars "zhi" + 1) then x.length
      else σ.vars "zp" + 1 + rd x (σ.vars "zp" + 0) * rd x (σ.vars "zhi" + 1))) ?_ ?_
  · run_vcg [rdV_spec hent (by omega) "zhc" "zp" 0, rdV_spec hent (by omega) "zhw" "zhi" 1]
    all_goals (simp only [HI] at *; simp_all [Env.setVar, Env.setArr]; try omega)
  · rintro σ ⟨⟨ha, hn, hs, hle, hp, hbs⟩, hlt⟩
    refine ⟨⟨ha, hn, hs, hle, hp, hbs⟩, hlt, ?_, ?_, hsB, hLB, ?_, ?_, ?_⟩
    · rw [hbs, length_pad (by rw [length_bsL]; exact hle)]; exact hlt
    · rw [hp]; exact hp_le x _
    · exact hprod _ _ (by rw [hp]; exact hp_le x _)
    · rw [hbs, hp]; exact bsL_set x hlt
    · rw [hp]; exact hp_succ' x _

theorem hdrLoop_spec {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => HI x (σ.setVar "zhi" 0)) hdrLoop
      (fun _ σ' => HI x σ' ∧ σ'.vars "zhi" = sX x) ((60 + 4) * sX x + 6) := by
  have hs : sX x < B := by
    have := rd_le_Mmax x 0; have := hB.2; unfold sX; nlinarith
  exact Spec.forRangeZero "zhi" "zs" (HI x) (sX x) 60 hs (fun _ h => h.2.2.2.1)
    (fun _ h => h.2.2.1) (hdrBody_spec hB)

set_option maxHeartbeats 2000000 in
/-- **The header.** -/
theorem hdr_value {x : List ℕ} {B : ℕ} (hB : HB x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
        σ.arrs "bs" = List.replicate (sX x) 0) hdr
      (fun _ σ' => σ'.arrs "a" = x ∧ σ'.vars "rt_n" = x.length ∧ σ'.vars "zs" = sX x ∧
        σ'.vars "zp" = hp x (sX x) ∧ σ'.arrs "bs" = pad (bsL x (sX x)) (sX x) ∧
        σ'.vars "zN" = NsX x) ((60 + 4) * sX x + 40) := by
  have hent := hB.1
  have hM0 := rd_le_Mmax x 0
  have hW := hB.2
  have hsB : sX x + 3 < B := by unfold sX; nlinarith
  have hLB : x.length + 2 < B := by nlinarith
  have hx0 : 0 < x.length → x.getD 0 0 = sX x := fun _ => rfl
  have hx0' : x.length = 0 → sX x = 0 := fun h => by
    unfold sX; rw [rd_of_ge (by omega)]
  have hxs : x.getD 0 0 < B := by have := hent; exact rd_lt hent (by omega) 0
  unfold hdr
  refine Spec.pre (P := fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
    σ.arrs "bs" = List.replicate (sX x) 0 ∧ sX x + 3 < B ∧ x.length + 2 < B ∧
    x.getD 0 0 < B ∧ (0 < x.length → x.getD 0 0 = sX x) ∧ (x.length = 0 → sX x = 0) ∧
    hp x 0 = (if x.length < sX x + 2 then x.length else sX x + 2)) ?_
    fun σ ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsB, hLB, hxs, hx0, hx0', rfl⟩
  run_vcg [hdrLoop_spec hB, rdV_spec hent (by omega) "zN" "zs" 1]
  all_goals (try simp only [HI] at *)
  all_goals (simp_all [Env.setVar, pad_nil, NsX, bsL]; try omega)

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgHdr
