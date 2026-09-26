import Lax496464Proofs.Ram.TotalReduction
import Lax496464Proofs.Ram.Program

/-!
# Bounding the fields of `Ram.Gen.Bnd` by a power of two

Given `ExpBd P k e` — the numbers `P.n`, `P.m` and `k` are each below `2 ^ e` — this file bounds
every field of `Gen.Bnd P k` (`Q`, `R`, `numJobs`, the member list, `jp`, `jq`, `jd`, `target`)
by `2 ^ (c · e)` for a fixed `c ≤ 64`, and concludes `Gen.Bnd P k (wordBound M L)` once
`M ≥ 2 ^ (66 · e)` (`bnd_of_expBd`).

The bounds are explicit `calc` chains: `omega` does not see through nonlinear atoms such as
`2 ^ e * 2 ^ e`.
-/

namespace Lax496464Proofs.Ram.TotalBnd

open Lax496464.HittingSet Lax496464.Construction
open Lax496464Proofs.Ram.BitsNat (natBits)
open Lax496464Proofs.Ram.TotalReduction (Admissible encodes_of_admissible)
open Lax496464Proofs.Ram.Program (length_memberList_le)
open Lax496464Proofs.Ram.Values (seg_setIdx_elem_lt family_cases slot_eq_proj jp_sel jq_sel
  jd_sel jp_dum jq_dumA jd_dumA jq_dumB jd_dumB)

/-- The tape-length exponent every `Bnd`-relevant quantity this file handles is dominated by.
Very generous on purpose — no attempt is made to find the tight exponent, only *some* fixed one
that works, since `RamPolytime` doesn't care about the polynomial's degree. -/
abbrev expBound (P : Instance) (k : ℕ) : ℕ := (natBits (encodeInstance P k)).length

/-- The single hypothesis the `Bnd`-domination argument needs about `P`, `k` and an exponent
`e`: each of `P.n`, `P.m`, `k` is below `2 ^ e`. For a canonical encoding this holds with `e :=
expBound P k` (`expBd_canonical`); for a tape the scan merely *validates*, it holds with `e :=
y.length + 3` (see `TotalRun`). -/
structure ExpBd (P : Instance) (k e : ℕ) : Prop where
  n : P.n < 2 ^ e
  m : P.m < 2 ^ e
  k : k < 2 ^ e

variable {P : Instance} {k e : ℕ}

/-- `Admissible`'s own `2 ≤ k` forces the exponent `e` to clear `2`. -/
theorem two_le_e (h : Admissible P k) (hb : ExpBd P k e) : 2 ≤ e := by
  have hk := hb.k
  have h2k := h.1
  rcases Nat.lt_or_ge e 2 with hc | hc
  · exfalso; interval_cases e <;> omega
  · exact hc

theorem sq_two_pow (e : ℕ) :
    (2 : ℕ) ^ e * 2 ^ e = 2 ^ (2 * e) := by
  rw [← pow_add]; ring_nf

theorem Q_lt_two_pow (h : Admissible P k) (hb : ExpBd P k e) :
    Q P k < 2 ^ (8 * e) := by
  have hn : P.n < 2 ^ e := hb.n
  have hk : k < 2 ^ e := hb.k
  have hexp2 := two_le_e h hb
  have hQeq : Q P k = (k - 1) * (P.n + 1) := rfl
  have h1 : (k - 1) * (P.n + 1) ≤ k * (P.n + 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : k * (P.n + 1) ≤ (2 ^ e) * (2 ^ e + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h3 : (2 : ℕ) ^ e * (2 ^ e + 1) ≤
      2 ^ e * (2 * 2 ^ e) := by
    apply Nat.mul_le_mul_left; omega
  have h4 : (2 : ℕ) ^ e * (2 * 2 ^ e) =
      2 * (2 ^ e * 2 ^ e) := by ring
  have h5 := sq_two_pow e
  have h7 : (2 : ℕ) * 2 ^ (2 * e) < 2 ^ (8 * e) := by
    have h6 : (2 : ℕ) * 2 ^ (2 * e) = 2 ^ (2 * e + 1) := by
      rw [pow_succ]; ring
    rw [h6]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  calc Q P k = (k - 1) * (P.n + 1) := hQeq
    _ ≤ k * (P.n + 1) := h1
    _ ≤ 2 ^ e * (2 ^ e + 1) := h2
    _ ≤ 2 ^ e * (2 * 2 ^ e) := h3
    _ = 2 * (2 ^ e * 2 ^ e) := h4
    _ = 2 * 2 ^ (2 * e) := by rw [h5]
    _ < 2 ^ (8 * e) := h7

theorem R_lt_two_pow (h : Admissible P k) (hb : ExpBd P k e) :
    R P k < 2 ^ (8 * e) := by
  have hn : P.n < 2 ^ e := hb.n
  have hk : k < 2 ^ e := hb.k
  have hexp2 := two_le_e h hb
  have hReq : R P k = k * (P.n - 1) + 2 := rfl
  have h1 : k * (P.n - 1) ≤ (2 ^ e) * (2 ^ e) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h5 := sq_two_pow e
  have h7 : (2 : ℕ) ^ (2 * e) + 2 < 2 ^ (8 * e) := by
    have h2le : (2 : ℕ) ≤ 2 ^ (2 * e) := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : (2 : ℕ) ^ (2 * e) + 2 ≤ 2 ^ (2 * e) + 2 ^ (2 * e) :=
      by omega
    have h8 : (2 : ℕ) ^ (2 * e) + 2 ^ (2 * e) =
        2 ^ (2 * e + 1) := by rw [pow_succ]; ring
    have h9 : (2 : ℕ) ^ (2 * e + 1) < 2 ^ (8 * e) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  calc R P k = k * (P.n - 1) + 2 := hReq
    _ ≤ 2 ^ e * 2 ^ e + 2 := by omega
    _ = 2 ^ (2 * e) + 2 := by rw [h5]
    _ < 2 ^ (8 * e) := h7

theorem memberList_length_lt_two_pow (h : Admissible P k) (hb : ExpBd P k e) :
    (memberList P).length < 2 ^ (8 * e) := by
  have hn : P.n < 2 ^ e := hb.n
  have hm : P.m < 2 ^ e := hb.m
  have hle : (memberList P).length ≤ P.n * P.m :=
    length_memberList_le (encodes_of_admissible h)
  have hexp2 := two_le_e h hb
  have h1 : P.n * P.m ≤ (2 ^ e) * (2 ^ e) :=
    Nat.mul_le_mul hn.le hm.le
  have h5 := sq_two_pow e
  have h7 : (2 : ℕ) ^ (2 * e) < 2 ^ (8 * e) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  calc (memberList P).length ≤ P.n * P.m := hle
    _ ≤ 2 ^ e * 2 ^ e := h1
    _ = 2 ^ (2 * e) := h5
    _ < 2 ^ (8 * e) := h7

theorem numJobs_lt_two_pow (h : Admissible P k) (hb : ExpBd P k e) :
    numJobs P k < 2 ^ (32 * e) := by
  have hn : P.n < 2 ^ e := hb.n
  have hm : P.m < 2 ^ e := hb.m
  have hR := (R_lt_two_pow h hb).le
  have hLc := (memberList_length_lt_two_pow h hb).le
  have hexp2 := two_le_e h hb
  have hsc : selCount P k = R P k * (memberList P).length := rfl
  have hdc : dumCount P k = R P k * P.m * P.n := rfl
  have hnj : numJobs P k = selCount P k + 2 * dumCount P k := rfl
  have hscle : selCount P k ≤ 2 ^ (8 * e) * 2 ^ (8 * e) := by
    rw [hsc]; exact Nat.mul_le_mul hR hLc
  have hdcle : dumCount P k ≤
      2 ^ (8 * e) * (2 ^ e * 2 ^ e) := by
    rw [hdc, mul_assoc]
    exact Nat.mul_le_mul hR (Nat.mul_le_mul hm.le hn.le)
  have h5 := sq_two_pow e
  have hdcle' : dumCount P k ≤ 2 ^ (8 * e) * 2 ^ (2 * e) := by
    rw [h5] at hdcle; exact hdcle
  have hpow : (2:ℕ) ^ (8 * e) * 2 ^ (8 * e) +
      2 * (2 ^ (8 * e) * 2 ^ (2 * e)) < 2 ^ (32 * e) := by
    have e1 : (2:ℕ) ^ (8 * e) * 2 ^ (8 * e) =
        2 ^ (16 * e) := by rw [← pow_add]; ring_nf
    have e2 : (2:ℕ) ^ (8 * e) * 2 ^ (2 * e) =
        2 ^ (10 * e) := by rw [← pow_add]; ring_nf
    rw [e1, e2]
    have hle1 : (2:ℕ) ^ (16 * e) ≤ 2 ^ (31 * e) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hle2 : (2:ℕ) * 2 ^ (10 * e) ≤ 2 ^ (31 * e) := by
      have h6 : (2:ℕ) * 2 ^ (10 * e) = 2 ^ (10 * e + 1) := by
        rw [pow_succ]; ring
      rw [h6]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfin : (2:ℕ) ^ (31 * e) + 2 ^ (31 * e) < 2 ^ (32 * e) := by
      have h7 : (2:ℕ) ^ (31 * e) + 2 ^ (31 * e) =
          2 ^ (31 * e + 1) := by rw [pow_succ]; ring
      rw [h7]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  calc numJobs P k = selCount P k + 2 * dumCount P k := hnj
    _ ≤ 2 ^ (8 * e) * 2 ^ (8 * e) +
        2 * (2 ^ (8 * e) * 2 ^ (2 * e)) := by
        have := Nat.mul_le_mul_left 2 hdcle'
        omega
    _ < 2 ^ (32 * e) := hpow

/-! ## `jp`/`jq`/`jd`/`target`

These additionally depend on `g`/`G`/`seg`/`setIdx`/`elem` (`Construction.lean`): `g(r,j) :=
r*P.m+(j+1)`, `G(r,j) := g(r,j)^2 * Q P k`. `Values.seg_setIdx_elem_lt`/`family_cases` (`Ram/
Values.lean`) give the range facts (`seg P k t < R P k`, `setIdx P k t < P.m`, `elem P k t <
P.n`, and which of `jp_sel`/`jp_dum` etc. applies) a general `t < numJobs P k` needs; combined
with the bounds above, the same `calc`-chain technique closes these too. -/

/-- Two power-of-two bounds combine multiplicatively into one, with the exponents adding. -/
theorem pow_mul_le (e c1 c2 : ℕ) {a b : ℕ} (ha : a ≤ 2 ^ (c1 * e)) (hb : b ≤ 2 ^ (c2 * e)) :
    a * b ≤ 2 ^ ((c1 + c2) * e) := by
  calc a * b ≤ 2 ^ (c1 * e) * 2 ^ (c2 * e) := Nat.mul_le_mul ha hb
    _ = 2 ^ ((c1 + c2) * e) := by rw [← pow_add]; ring_nf

/-- `omega` cannot see that a strict inequality between two power-of-two atoms leaves room for
a *constant multiple*: `X < Y` alone does not give `2^d * X < Y` (e.g. `X = Y - 1`). This
packages the extra room explicitly — `2^d * 2^(c*e) < 2^(c'*e)` whenever `c' ≥ c + d` (`d` more
doublings of slack) and `e ≥ 1` — so the finishing `omega` calls below only ever need to combine
already-linear facts (after scaling a handful of individual term bounds by small constants),
never re-derive this. -/
theorem pow_dom (e c c' d : ℕ) (h : c + d < c') (he : 1 ≤ e) :
    2 ^ d * 2 ^ (c * e) < 2 ^ (c' * e) := by
  have h1 : (2 : ℕ) ^ d * 2 ^ (c * e) = 2 ^ (c * e + d) := by
    rw [← pow_add, Nat.add_comm]
  rw [h1]
  have hstep : c * e + d < c' * e := by
    nlinarith [h, he, Nat.mul_le_mul_right e (Nat.succ_le_of_lt h)]
  exact Nat.pow_lt_pow_right (by norm_num) hstep

theorem g_lt_two_pow (h : Admissible P k) (hb : ExpBd P k e) {r j : ℕ} (hr : r < R P k) (hj : j < P.m) :
    g P r j < 2 ^ (16 * e) := by
  have hm : P.m < 2 ^ e := hb.m
  have hR : R P k ≤ 2 ^ (8 * e) := (R_lt_two_pow h hb).le
  have hexp2 := two_le_e h hb
  have hgeq : g P r j = r * P.m + (j + 1) := rfl
  have h1 : r * P.m ≤ 2 ^ (9 * e) :=
    pow_mul_le (e) 8 1 (by omega) (by simpa using hm.le)
  have h2 : (2 : ℕ) ^ (9 * e) + 2 ^ e < 2 ^ (16 * e) := by
    have hle : (2 : ℕ) ^ e ≤ 2 ^ (9 * e) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have heq : (2 : ℕ) * 2 ^ (9 * e) = 2 ^ (9 * e + 1) := by
      rw [pow_succ]; ring
    have hfin : (2 : ℕ) ^ (9 * e + 1) < 2 ^ (16 * e) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  omega

theorem G_lt_two_pow (h : Admissible P k) (hb : ExpBd P k e) {r j : ℕ} (hr : r < R P k) (hj : j < P.m) :
    G P k r j < 2 ^ (41 * e) := by
  have hg := g_lt_two_pow h hb hr hj
  have hQ : Q P k ≤ 2 ^ (8 * e) := (Q_lt_two_pow h hb).le
  have hexp2 := two_le_e h hb
  have hGeq : G P k r j = g P r j ^ 2 * Q P k := rfl
  have hg2 : g P r j ^ 2 ≤ 2 ^ (32 * e) := by
    have : g P r j ^ 2 = g P r j * g P r j := sq (g P r j)
    rw [this]
    exact pow_mul_le (e) 16 16 hg.le hg.le
  have hGle : g P r j ^ 2 * Q P k ≤ 2 ^ (40 * e) :=
    pow_mul_le (e) 32 8 hg2 hQ
  have hlt : (2 : ℕ) ^ (40 * e) < 2 ^ (40 * e) + 1 := by omega
  calc G P k r j = g P r j ^ 2 * Q P k := hGeq
    _ ≤ 2 ^ (40 * e) := hGle
    _ < 2 ^ (40 * e) + 1 := hlt
    _ ≤ 2 ^ (41 * e) := by
        have : (2 : ℕ) ^ (40 * e) + 1 ≤ 2 * 2 ^ (40 * e) := by
          have h1 : (1 : ℕ) ≤ 2 ^ (40 * e) := Nat.one_le_two_pow
          omega
        have h2 : (2 : ℕ) * 2 ^ (40 * e) = 2 ^ (40 * e + 1) := by
          rw [pow_succ]; ring
        calc (2:ℕ) ^ (40 * e) + 1 ≤ 2 * 2 ^ (40 * e) := this
          _ = 2 ^ (40 * e + 1) := h2
          _ ≤ 2 ^ (41 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)

set_option maxHeartbeats 1000000 in
/-- **`jp`/`jq`/`jd` are all bounded by a power of two in the tape's length, for any job number
in range.** Case-splits on which of the three families `t` falls into (`family_cases`), gets
`seg`/`setIdx`/`elem`'s own range facts (`seg_setIdx_elem_lt`), reassembles `slot`'s value
(`slot_eq_proj`) to match `jp_sel`/`jp_dum`/etc.'s own hypothesis shape, then bounds the
resulting closed form via `g_lt_two_pow`/`G_lt_two_pow`/`Q_lt_two_pow`. -/
theorem jp_jq_jd_lt_two_pow (h : Admissible P k) (hb : ExpBd P k e) (hm : 0 < P.m) {t : ℕ} (ht : t < numJobs P k) :
    jp P k t < 2 ^ (64 * e) ∧ jq P k t < 2 ^ (64 * e) ∧
      jd P k t < 2 ^ (64 * e) := by
  have hn : 0 < P.n := by have := h.1; have := h.2.1; omega
  have hR : 0 < R P k := by unfold R; omega
  obtain ⟨hseg, hsi, hel⟩ := seg_setIdx_elem_lt ht hR hm hn
  have hslot := slot_eq_proj (P := P) (k := k) t
  have hfam := family_cases (P := P) (k := k) ht
  have hexp2 := two_le_e h hb
  have hg := g_lt_two_pow h hb hseg hsi
  have hG := (G_lt_two_pow h hb hseg hsi).le
  have hQ0 : Q P k ≤ 2 ^ (8 * e) := (Q_lt_two_pow h hb).le
  have hn2pow : P.n < 2 ^ e := hb.n
  -- every term any of jp/jq/jd reduces to, bounded by the *same* shared atom `U`
  set U : ℕ := 2 ^ (41 * e) with hUdef
  have hgQ : g P (seg P k t) (setIdx P k t) * Q P k ≤ U := by
    have h1 : g P (seg P k t) (setIdx P k t) * Q P k ≤ 2 ^ (24 * e) :=
      pow_mul_le (e) 16 8 hg.le hQ0
    have h2 : (2 : ℕ) ^ (24 * e) ≤ U :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hQ : Q P k ≤ U := by
    have h2 : (2 : ℕ) ^ (8 * e) ≤ U := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have helem1 : elem P k t + 1 ≤ U := by
    have h1 : elem P k t + 1 ≤ 2 ^ e := by omega
    have h2 : (2 : ℕ) ^ e ≤ U := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hnp1 : P.n + 1 ≤ U := by
    have h1 : P.n + 1 ≤ 2 ^ e := by omega
    have h2 : (2 : ℕ) ^ e ≤ U := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hnp1_tight : P.n + 1 ≤ 2 ^ (1 * e) := by
    have heq : (1 : ℕ) * e = e := by ring
    rw [heq]; omega
  have hgnp1 : g P (seg P k t) (setIdx P k t) * (P.n + 1) ≤ U := by
    have h1 : g P (seg P k t) (setIdx P k t) * (P.n + 1) ≤ 2 ^ (17 * e) :=
      pow_mul_le (e) 16 1 hg.le hnp1_tight
    have h2 : (2 : ℕ) ^ (17 * e) ≤ U := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8U : 8 * U < 2 ^ (64 * e) := by
    have := pow_dom (e) 41 64 3 (by omega) (by omega)
    simpa [hUdef] using this
  rcases hfam with hf0 | hf1 | hf2
  · rw [hf0] at hslot
    have hjp := jp_sel hslot
    have hjq := jq_sel hslot
    have hjd := jd_sel hslot
    have heqq : jq P k t = 2 * (g P (seg P k t) (setIdx P k t) * Q P k) + Q P k := by
      rw [hjq]; simp [g]
    have heqd : jd P k t = G P k (seg P k t) (setIdx P k t) +
        (2 * (g P (seg P k t) (setIdx P k t) * Q P k) + Q P k) + (elem P k t + 1) := by
      rw [hjd]; simp only [g, G]; ring
    refine ⟨by omega, by omega, by omega⟩
  · rw [hf1] at hslot
    have hjp0 := jp_dum (a := 0) hslot
    have hjq0 := jq_dumA hslot
    have hjd0 := jd_dumA hslot
    have heqp : jp P k t = g P (seg P k t) (setIdx P k t) * (P.n + 1) := by
      rw [hjp0]; simp [g]
    have heqq : jq P k t = g P (seg P k t) (setIdx P k t) * Q P k := by
      rw [hjq0]; simp [g]
    have heqd : jd P k t = G P k (seg P k t) (setIdx P k t) +
        g P (seg P k t) (setIdx P k t) * Q P k + (elem P k t + 1) := by
      rw [hjd0]; simp only [g, G]; ring
    refine ⟨by omega, by omega, by omega⟩
  · rw [hf2] at hslot
    have hjp0 : jp P k t = g P (seg P k t) (setIdx P k t) * (P.n + 1) :=
      jp_dum (a := 1) (by
        have h12 : (1 : ℕ) + 1 = 2 := by norm_num
        rw [h12]; exact hslot)
    have hjq0 := jq_dumB hslot
    have hjd0 := jd_dumB hslot
    have heqq : jq P k t = g P (seg P k t) (setIdx P k t) * Q P k + Q P k := by
      rw [hjq0]; simp [g]
    have heqd : jd P k t = G P k (seg P k t) (setIdx P k t) +
        (2 * (g P (seg P k t) (setIdx P k t) * Q P k) + Q P k) + (elem P k t + 1) := by
      rw [hjd0]; simp only [g, G]; ring
    refine ⟨by omega, by omega, by omega⟩

/-! ## `target`, and the payoff: `Bnd P k (wordBound M y.length)` -/

theorem target_lt_two_pow (h : Admissible P k) (hb : ExpBd P k e) : target P k < 2 ^ (24 * e) := by
  have hR := (R_lt_two_pow h hb).le
  have hm : P.m < 2 ^ e := hb.m
  have hk : k < 2 ^ e := hb.k
  have hexp2 := two_le_e h hb
  have htgeq : target P k = R P k * P.m * (2 * k - 1) := rfl
  have hRm : R P k * P.m ≤ 2 ^ (9 * e) :=
    pow_mul_le (e) 8 1 hR (by simpa using hm.le)
  have h2k1 : 2 * k - 1 ≤ 2 ^ (2 * e) := by
    have h1 : (2 : ℕ) * 2 ^ e ≤ 2 ^ (2 * e) := by
      have heq : (2 : ℕ) * 2 ^ e = 2 ^ (e + 1) := by
        rw [pow_succ]; ring
      rw [heq]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hfin : R P k * P.m * (2 * k - 1) ≤ 2 ^ (11 * e) :=
    pow_mul_le (e) 9 2 hRm h2k1
  have hpad : (2 : ℕ) ^ (11 * e) < 2 ^ (24 * e) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-- `Bnd P k (wordBound M L)` once `M ≥ 2 ^ (66 · e)`: every field is below `2 ^ (64 · e)`, and
`wordBound M L` is at least `M`. -/
theorem bnd_of_expBd (h : Admissible P k) (hb : ExpBd P k e) {M L : ℕ}
    (hMge : 2 ^ (66 * e) ≤ M) :
    Lax496464Proofs.Ram.Gen.Bnd P k (Lax496464Proofs.Ram.ScanModel.wordBound M L) := by
  have hexp2 := two_le_e h hb
  set B : ℕ := Lax496464Proofs.Ram.ScanModel.wordBound M L with hBdef
  have hpowL : 1 ≤ (2 : ℕ) ^ L := Nat.one_le_two_pow
  have hBge0 : M * 2 ^ L ≤ B := by
    rw [hBdef]; unfold Lax496464Proofs.Ram.ScanModel.wordBound; omega
  have hMle : M ≤ M * 2 ^ L := by
    calc M = M * 1 := (mul_one M).symm
      _ ≤ M * 2 ^ L := Nat.mul_le_mul_left M hpowL
  have hBge' : (2 : ℕ) ^ (66 * e) ≤ B := by omega
  have hall64 : (2 : ℕ) ^ (64 * e) < B := by
    have : (2 : ℕ) ^ (64 * e) < 2 ^ (66 * e) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hQ := (Q_lt_two_pow h hb).le
  have hR := (R_lt_two_pow h hb).le
  have hnj := (numJobs_lt_two_pow h hb).le
  have hLc := (memberList_length_lt_two_pow h hb).le
  have htg := (target_lt_two_pow h hb).le
  have hn := hb.n.le
  have hn : P.n ≤ 2 ^ e := hn
  have hm := hb.m.le
  have hm : P.m ≤ 2 ^ e := hm
  have hk := hb.k.le
  have hk : k ≤ 2 ^ e := hk
  have hpad32 : (2 : ℕ) ^ (32 * e) ≤ 2 ^ (64 * e) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpad24 : (2 : ℕ) ^ (24 * e) ≤ 2 ^ (64 * e) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpad8 : (2 : ℕ) ^ (8 * e) ≤ 2 ^ (64 * e) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpad1 : (2 : ℕ) ^ e ≤ 2 ^ (64 * e) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hbig9 : (9 : ℕ) ≤ 2 ^ (64 * e) := by
    calc (9 : ℕ) ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (64 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2pad : 2 * 2 ^ (64 * e) < 2 ^ (66 * e) := by
    have heq : (2 : ℕ) * 2 ^ (64 * e) = 2 ^ (64 * e + 1) := by
      rw [pow_succ]; ring
    rw [heq]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, ?_⟩
  intro s hs
  have hmpos : 0 < P.m := by
    by_contra hm0
    push Not at hm0
    have hm0' : P.m = 0 := by omega
    have hdc0 : dumCount P k = 0 := by simp [dumCount, hm0']
    have hsc0 : selCount P k = 0 := by
      have hlen0 : (List.finRange P.m).length = 0 := by rw [List.length_finRange, hm0']
      have hfr : List.finRange P.m = [] := List.eq_nil_of_length_eq_zero hlen0
      have hml0 : (memberList P).length = 0 := by
        unfold memberList
        rw [hfr]
        rfl
      simp only [selCount, hml0]; ring
    have hnj0 : numJobs P k = 0 := by simp only [numJobs, hsc0, hdc0]
    omega
  obtain ⟨hp, hq, hd⟩ := jp_jq_jd_lt_two_pow h hb hmpos hs
  exact ⟨by omega, by omega, by omega⟩


end Lax496464Proofs.Ram.TotalBnd
