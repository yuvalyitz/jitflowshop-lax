import Lax496464.Construction
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The Jobs of Section 8, Reached by Counters

`Construction.slot` takes a job number apart with `/` and `%`. A program that walks the jobs
in order never has to: it keeps the segment, the set and the element as counters, and the
job number as one more. This file says what `slot`, `jp`, `jq` and `jd` are at a job number
built the way the counters build it.
-/

namespace Lax496464Proofs.Ram.Values

open Lax496464.HittingSet Lax496464.Construction

variable {P : Lax496464.HittingSet.Instance} {k : ℕ}

/-- The pair at position `u` of the membership list. -/
abbrev ent (P : Lax496464.HittingSet.Instance) (u : ℕ) : ℕ × ℕ :=
  (memberList P).getD u (0, 0)

theorem slot_sel {r u : ℕ} (hu : u < (memberList P).length) (hr : r < R P k) :
    slot P k ((memberList P).length * r + u) =
      (0, r, (ent P u).1, (ent P u).2) := by
  have hL : 0 < (memberList P).length := by omega
  have hlt : (memberList P).length * r + u < selCount P k := by
    calc (memberList P).length * r + u < (memberList P).length * r + (memberList P).length := by omega
      _ = (memberList P).length * (r + 1) := by ring
      _ ≤ (memberList P).length * R P k := Nat.mul_le_mul_left _ hr
      _ = selCount P k := by simp only [selCount]; ring
  have hdiv : ((memberList P).length * r + u) / (memberList P).length = r := by
    rw [Nat.mul_add_div hL, Nat.div_eq_of_lt hu, Nat.add_zero]
  have hmod : ((memberList P).length * r + u) % (memberList P).length = u := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
  rw [slot, if_pos hlt]
  simp only [hdiv, hmod, ent]

theorem dum_lt {r j i : ℕ} (hr : r < R P k) (hj : j < P.m) (hi : i < P.n) :
    i + P.n * (j + P.m * r) < dumCount P k := by
  have h1 : i + P.n * (j + P.m * r) < P.n * (j + P.m * r + 1) := by
    rw [Nat.mul_succ]; omega
  have h2 : j + P.m * r + 1 ≤ P.m * (r + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  calc i + P.n * (j + P.m * r) < P.n * (j + P.m * r + 1) := h1
    _ ≤ P.n * (P.m * (r + 1)) := Nat.mul_le_mul_left _ h2
    _ = P.n * P.m * (r + 1) := by ring
    _ ≤ P.n * P.m * R P k := Nat.mul_le_mul_left _ hr
    _ = dumCount P k := by simp only [dumCount]; ring

theorem slot_dum {a r j i : ℕ} (ha : a = 0 ∨ a = 1) (hr : r < R P k) (hj : j < P.m)
    (hi : i < P.n) :
    slot P k (selCount P k + a * dumCount P k + (i + P.n * (j + P.m * r))) =
      (a + 1, r, j, i) := by
  have hn : 0 < P.n := by omega
  have hm : 0 < P.m := by omega
  have hv : i + P.n * (j + P.m * r) < dumCount P k := by
    have h1 : i + P.n * (j + P.m * r) < P.n * (j + P.m * r + 1) := by
      rw [Nat.mul_succ]; omega
    have h2 : j + P.m * r + 1 ≤ P.m * (r + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    calc i + P.n * (j + P.m * r) < P.n * (j + P.m * r + 1) := h1
      _ ≤ P.n * (P.m * (r + 1)) := Nat.mul_le_mul_left _ h2
      _ = P.n * P.m * (r + 1) := by ring
      _ ≤ P.n * P.m * R P k := Nat.mul_le_mul_left _ hr
      _ = dumCount P k := by simp only [dumCount]; ring
  have hdiv : (i + P.n * (j + P.m * r)) / (P.m * P.n) = r := by
    have : i + P.n * (j + P.m * r) = (j * P.n + i) + (P.m * P.n) * r := by ring
    rw [this, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt, Nat.zero_add]
    calc j * P.n + i < j * P.n + P.n := by omega
      _ = (j + 1) * P.n := by ring
      _ ≤ P.m * P.n := Nat.mul_le_mul_right _ hj
  have hmod1 : (i + P.n * (j + P.m * r)) % (P.m * P.n) = j * P.n + i := by
    have : i + P.n * (j + P.m * r) = (j * P.n + i) + (P.m * P.n) * r := by ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
    calc j * P.n + i < j * P.n + P.n := by omega
      _ = (j + 1) * P.n := by ring
      _ ≤ P.m * P.n := Nat.mul_le_mul_right _ hj
  have hdiv2 : (j * P.n + i) / P.n = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod2 : (i + P.n * (j + P.m * r)) % P.n = i := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have hge : ¬ selCount P k + a * dumCount P k + (i + P.n * (j + P.m * r)) < selCount P k := by omega
  rw [slot, if_neg hge]
  rcases ha with rfl | rfl
  · have hu : selCount P k + 0 * dumCount P k + (i + P.n * (j + P.m * r)) - selCount P k
        = i + P.n * (j + P.m * r) := by omega
    simp only [hu, if_pos hv, hdiv, hmod1, hdiv2, hmod2]
  · have hu : selCount P k + 1 * dumCount P k + (i + P.n * (j + P.m * r)) - selCount P k
        = dumCount P k + (i + P.n * (j + P.m * r)) := by omega
    have hnl : ¬ dumCount P k + (i + P.n * (j + P.m * r)) < dumCount P k := by omega
    have hu2 : dumCount P k + (i + P.n * (j + P.m * r)) - dumCount P k
        = i + P.n * (j + P.m * r) := by omega
    simp only [hu, if_neg hnl, hu2, hdiv, hmod1, hdiv2, hmod2]

theorem ent_lt {u : ℕ} (hu : u < (memberList P).length) :
    (ent P u).1 < P.m ∧ (ent P u).2 < P.n := by
  have hmem : ent P u ∈ memberList P := by
    rw [ent, List.getD_eq_getElem _ _ hu]
    exact List.getElem_mem hu
  rw [memberList, List.mem_flatMap] at hmem
  obtain ⟨j, -, hj⟩ := hmem
  rw [List.mem_map] at hj
  obtain ⟨i, -, hi⟩ := hj
  rw [← hi]
  exact ⟨j.isLt, i.isLt⟩

/-- **The segment, set and element of any job number are in range** — the reverse of
`slot_sel`/`slot_dum`: those show what `slot` computes *given* an already-bounded `r`/`j`/`i`,
this shows the range those come back in for *any* `t < numJobs P k`, straight from `slot`'s own
div/mod definition. Needed so `jp`/`jq`/`jd`'s closed forms (`Values.jp_sel` etc., all built from
`seg`/`setIdx`/`elem`) can be bounded the same way `Q`/`R`/`numJobs` already are
(`Ram/TotalBnd.lean`). -/
theorem seg_setIdx_elem_lt {t : ℕ} (ht : t < numJobs P k) (_hR : 0 < R P k) (hm : 0 < P.m)
    (hn : 0 < P.n) :
    seg P k t < R P k ∧ setIdx P k t < P.m ∧ elem P k t < P.n := by
  unfold seg setIdx elem slot
  have hmnpos : 0 < P.m * P.n := by positivity
  have hnmpos : 0 < P.n * P.m := by positivity
  by_cases hsel : t < selCount P k
  · have hLpos : 0 < (memberList P).length := by
      rcases Nat.eq_zero_or_pos (memberList P).length with h0 | h0
      · exfalso; simp only [selCount, h0, mul_zero] at hsel; omega
      · exact h0
    have hRpos : t / (memberList P).length < R P k :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; simpa only [selCount] using hsel)
    have he := ent_lt (P := P) (u := t % (memberList P).length) (Nat.mod_lt t hLpos)
    simp only [ent] at he
    simp only [if_pos hsel]
    exact ⟨hRpos, he.1, he.2⟩
  · have hsel' : selCount P k ≤ t := by omega
    by_cases hud : t - selCount P k < dumCount P k
    · have hseg : (t - selCount P k) / (P.m * P.n) < R P k := by
        have hlt : t - selCount P k < P.m * P.n * R P k := by
          calc t - selCount P k < dumCount P k := hud
            _ = P.m * P.n * R P k := by simp only [dumCount]; ring
        exact Nat.div_lt_of_lt_mul hlt
      have hsi : (t - selCount P k) % (P.m * P.n) / P.n < P.m := by
        have h1 : (t - selCount P k) % (P.m * P.n) < P.m * P.n := Nat.mod_lt _ hmnpos
        have hlt : (t - selCount P k) % (P.m * P.n) < P.n * P.m :=
          lt_of_lt_of_eq h1 (Nat.mul_comm P.m P.n)
        exact Nat.div_lt_of_lt_mul hlt
      have hel : (t - selCount P k) % P.n < P.n := Nat.mod_lt _ hn
      simp only [if_neg hsel, if_pos hud]
      exact ⟨hseg, hsi, hel⟩
    · have hud' : dumCount P k ≤ t - selCount P k := by omega
      have hnj : t < selCount P k + 2 * dumCount P k := by simpa only [numJobs] using ht
      have hv2 : t - selCount P k - dumCount P k < dumCount P k := by omega
      have hseg : (t - selCount P k - dumCount P k) / (P.m * P.n) < R P k := by
        have hlt : t - selCount P k - dumCount P k < P.m * P.n * R P k := by
          calc t - selCount P k - dumCount P k < dumCount P k := hv2
            _ = P.m * P.n * R P k := by simp only [dumCount]; ring
        exact Nat.div_lt_of_lt_mul hlt
      have hsi : (t - selCount P k - dumCount P k) % (P.m * P.n) / P.n < P.m := by
        have h1 : (t - selCount P k - dumCount P k) % (P.m * P.n) < P.m * P.n :=
          Nat.mod_lt _ hmnpos
        have hlt : (t - selCount P k - dumCount P k) % (P.m * P.n) < P.n * P.m :=
          lt_of_lt_of_eq h1 (Nat.mul_comm P.m P.n)
        exact Nat.div_lt_of_lt_mul hlt
      have hel : (t - selCount P k - dumCount P k) % P.n < P.n := Nat.mod_lt _ hn
      simp only [if_neg hsel, if_neg hud]
      exact ⟨hseg, hsi, hel⟩

/-- **A job number's family is one of the three `slot` ever produces** — the companion to
`seg_setIdx_elem_lt`, needed to pick which of `jp_sel`/`jp_dum` (etc.) applies to a *given*
`t < numJobs P k`, since those take the family as part of their own hypothesis (`slot P k t =
(0, r, j, i)` vs `(a + 1, r, j, i)`), not something they derive themselves. -/
theorem family_cases {t : ℕ} (_ht : t < numJobs P k) :
    family P k t = 0 ∨ family P k t = 1 ∨ family P k t = 2 := by
  unfold family slot
  by_cases hsel : t < selCount P k
  · simp [if_pos hsel]
  · by_cases hud : t - selCount P k < dumCount P k
    · simp [if_neg hsel, if_pos hud]
    · simp [if_neg hsel, if_neg hud]

/-- `slot` reassembled from its own four projections — definitionally true, but stated so a
known `family` (from `family_cases`) can be substituted in to get exactly the `slot P k t =
(0, r, j, i)`/`(a + 1, r, j, i)` shape `jp_sel`/`jp_dum` (etc.) ask for. -/
theorem slot_eq_proj (t : ℕ) :
    slot P k t = (family P k t, seg P k t, setIdx P k t, elem P k t) := rfl

theorem slot_sel_lt {r u : ℕ} (hu : u < (memberList P).length) (hr : r < R P k) :
    (memberList P).length * r + u < numJobs P k := by
  have : (memberList P).length * r + u < selCount P k := by
    calc (memberList P).length * r + u < (memberList P).length * r + (memberList P).length := by omega
      _ = (memberList P).length * (r + 1) := by ring
      _ ≤ (memberList P).length * R P k := Nat.mul_le_mul_left _ hr
      _ = selCount P k := by simp only [selCount]; ring
  simp only [numJobs]; omega

/-! ## The three numbers of a job, given its slot -/

section slotValues

variable {t r j i : ℕ}

theorem jp_sel (h : slot P k t = (0, r, j, i)) : jp P k t = 0 := by
  simp [jp, family, h]

theorem jq_sel (h : slot P k t = (0, r, j, i)) :
    jq P k t = 2 * ((r * P.m + (j + 1)) * Q P k) + Q P k := by
  simp [jq, family, seg, setIdx, g, h]; ring

theorem jd_sel (h : slot P k t = (0, r, j, i)) :
    jd P k t = (r * P.m + (j + 1)) * (r * P.m + (j + 1)) * Q P k +
      (2 * ((r * P.m + (j + 1)) * Q P k) + Q P k) + (i + 1) := by
  simp [jd, family, seg, setIdx, elem, G, g, h]; ring

theorem jp_dum {a : ℕ} (h : slot P k t = (a + 1, r, j, i)) :
    jp P k t = (r * P.m + (j + 1)) * (P.n + 1) := by
  simp [jp, family, seg, setIdx, g, h]

theorem jq_dumA (h : slot P k t = (1, r, j, i)) :
    jq P k t = (r * P.m + (j + 1)) * Q P k := by
  simp [jq, family, seg, setIdx, g, h]

theorem jd_dumA (h : slot P k t = (1, r, j, i)) :
    jd P k t = (r * P.m + (j + 1)) * (r * P.m + (j + 1)) * Q P k +
      (r * P.m + (j + 1)) * Q P k + (i + 1) := by
  simp only [jd, family, seg, setIdx, elem, G, g, h, if_true]
  ring

theorem jq_dumB (h : slot P k t = (2, r, j, i)) :
    jq P k t = (r * P.m + (j + 1)) * Q P k + Q P k := by
  simp [jq, family, seg, setIdx, g, h]; ring

theorem jd_dumB (h : slot P k t = (2, r, j, i)) :
    jd P k t = (r * P.m + (j + 1)) * (r * P.m + (j + 1)) * Q P k +
      (2 * ((r * P.m + (j + 1)) * Q P k) + Q P k) + (i + 1) := by
  simp [jd, family, seg, setIdx, elem, G, g, h]; ring

end slotValues

end Lax496464Proofs.Ram.Values
