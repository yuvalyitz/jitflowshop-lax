import Lax496464Proofs.Ram.W3Bits
import Lax496464Proofs.Section4
import Lax496464.Normalization

/-!
# The Width Sweep's Table, as the Paper's Recursion Computes It

`Section4.reachable_start`/`reachable_due` are the paper's equations (3) and (4), on the scaled
instance `scale J` (whose endpoints are distinct). This file turns them into statements about a
*table of numbers indexed by masks*:

* `Ge` — the table entry with the weight relaxed to "at least `c`", so that the weight step of the
  recursion is `c ↦ c − w_j` and costs nothing;
* `Rel sl t W INF T` — the table `T` (mask ↦ weight ↦ least *unscaled* load, `INF` for none) is the
  true table at the instant `t`, when the jobs running at `t` sit in the slots `sl`;
* `due_rel`, `start_rel` — one event, applied to the table by `dueT`/`startT`, keeps `Rel`.
-/

namespace Lax496464Proofs.Ram.W3Tab

open Lax496464.FlowShop Lax496464.FlowShop.Instance Lax496464.EstOrder Lax496464.Sweep
open Lax496464Proofs.Ram.W3Bits

variable (J : Instance)

/-- The scale factor of the rescaling. -/
def Nsc : ℕ := J.jobs + 1

theorem sc_p (j : J.Job) : (scale J).p j = Nsc J * J.p j := rfl
theorem sc_q (j : J.Job) : (scale J).q j = Nsc J * J.q j := by unfold scale; try rfl
theorem sc_d (j : J.Job) : (scale J).d j = Nsc J * J.d j + (j : ℕ) := rfl
/-- The scaled start time: `N · s j + j`. -/
theorem sc_s (j : J.Job) : s (I := scale J) j = (Nsc J : ℤ) * s (I := J) j + (j : ℕ) := by
  simp only [s, sc_d, sc_q]; push_cast; ring

/-- **The guard, scaled and unscaled.** A load `N · u` plus `p'_j` fits before `s'_j` exactly
when `u + p_j ≤ s_j`. -/
theorem guard_iff (j : J.Job) (u : ℕ) :
    (((Nsc J * u : ℕ) : ℤ) + (scale J).p j ≤ s (I := scale J) j) ↔ ((u : ℤ) + J.p j ≤ s (I := J) j) := by
  rw [sc_s, sc_p]
  have hj : (j : ℕ) < Nsc J := j.isLt.trans_le (Nat.le_succ _)
  have hN : (1 : ℤ) ≤ Nsc J := by exact_mod_cast Nat.succ_pos _
  have hj' : ((j : ℕ) : ℤ) < Nsc J := by exact_mod_cast hj
  push_cast
  constructor
  · intro h
    by_contra hn
    have hn := not_le.mp hn
    have h1 : (u : ℤ) + J.p j - s (I := J) j ≥ 1 := by omega
    nlinarith
  · intro h
    have : (Nsc J : ℤ) * ((u : ℤ) + J.p j) ≤ (Nsc J : ℤ) * s (I := J) j := mul_le_mul_of_nonneg_left h (by omega)
    nlinarith

/-! ## The weight-relaxed table entry -/

/-- The table entry with the weight relaxed to *at least* `c`. -/
def Ge (I : Instance) (t : ℤ) (X : Finset I.Job) (c : ℕ) (P : ℤ) : Prop :=
  ∃ W' : ℕ, c ≤ W' ∧ Reachable I t X W' P

/-- **Equation (4), for `Ge`.** -/
theorem ge_due (I : Instance) (hq : ∀ i : I.Job, 0 < I.q i) {t' t : ℤ} {j : I.Job}
    {X : Finset I.Job} {c : ℕ} {P : ℤ}
    (htt : t' < t) (hdj : (I.d j : ℤ) = t)
    (hnos : ∀ k : I.Job, ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : I.Job, k ≠ j → ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    Ge I t X c P ↔ j ∉ X ∧ (Ge I t' X c P ∨ Ge I t' (insert j X) c P) := by
  constructor
  · rintro ⟨W', hW, hR⟩
    obtain ⟨hj, h⟩ := (Lax496464Proofs.Section4.reachable_due I hq htt hdj hnos hnod).mp hR
    refine ⟨hj, ?_⟩
    rcases h with h | h
    · exact Or.inl ⟨W', hW, h⟩
    · exact Or.inr ⟨W', hW, h⟩
  · rintro ⟨hj, h⟩
    rcases h with ⟨W', hW, h⟩ | ⟨W', hW, h⟩
    · exact ⟨W', hW, (Lax496464Proofs.Section4.reachable_due I hq htt hdj hnos hnod).mpr
        ⟨hj, Or.inl h⟩⟩
    · exact ⟨W', hW, (Lax496464Proofs.Section4.reachable_due I hq htt hdj hnos hnod).mpr
        ⟨hj, Or.inr h⟩⟩

/-- **Equation (3), for `Ge`.** -/
theorem ge_start (I : Instance) (hq : ∀ i : I.Job, 0 < I.q i) {t' t : ℤ} {j : I.Job}
    {X : Finset I.Job} {c : ℕ} {P : ℤ}
    (htt : t' < t) (hsj : s j = t)
    (hnos : ∀ k : I.Job, k ≠ j → ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : I.Job, ¬ (t' < (I.d k : ℤ) ∧ (I.d k : ℤ) ≤ t)) :
    Ge I t X c P ↔
      (j ∉ X ∧ Ge I t' X c P) ∨
      (j ∈ X ∧ (X.erase j).card < I.machines ∧
        ∃ P'' : ℤ, Ge I t' (X.erase j) (c - I.w j) P'' ∧ P'' + I.p j ≤ s j ∧
          P'' + I.p j ≤ P) := by
  constructor
  · rintro ⟨W', hW, hR⟩
    rcases (Lax496464Proofs.Section4.reachable_start I hq htt hsj hnos hnod).mp hR with
      ⟨hj, h⟩ | ⟨hj, hcard, W'', P'', hWW, h, h1, h2⟩
    · exact Or.inl ⟨hj, W', hW, h⟩
    · refine Or.inr ⟨hj, hcard, P'', ⟨W'', by omega, h⟩, h1, h2⟩
  · rintro (⟨hj, W', hW, h⟩ | ⟨hj, hcard, P'', ⟨W'', hW, h⟩, h1, h2⟩)
    · exact ⟨W', hW, (Lax496464Proofs.Section4.reachable_start I hq htt hsj hnos hnod).mpr
        (Or.inl ⟨hj, h⟩)⟩
    · refine ⟨W'' + I.w j, by omega, (Lax496464Proofs.Section4.reachable_start I hq htt hsj hnos
        hnod).mpr (Or.inr ⟨hj, hcard, W'', P'', rfl, h, h1, h2⟩)⟩

/-! ## Who is running, and where -/

/-- The jobs of the scaled instance running at `t`. -/
def alive (t : ℤ) : Finset (scale J).Job :=
  Finset.univ.filter fun k => s (I := scale J) k ≤ t ∧ t < ((scale J).d k : ℤ)

variable {J}

theorem mem_alive {t : ℤ} {k : (scale J).Job} :
    k ∈ alive J t ↔ s (I := scale J) k ≤ t ∧ t < ((scale J).d k : ℤ) := by
  simp [alive]

/-- When a job's due date passes and nothing else happens, only that job leaves. -/
theorem alive_due {t' t : ℤ} {j : (scale J).Job} (htt : t' < t) (hdj : ((scale J).d j : ℤ) = t)
    (hnos : ∀ k : (scale J).Job, ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : (scale J).Job, k ≠ j → ¬ (t' < ((scale J).d k : ℤ) ∧ ((scale J).d k : ℤ) ≤ t)) :
    alive J t = (alive J t').erase j := by
  ext k
  rw [Finset.mem_erase, mem_alive, mem_alive]
  constructor
  · rintro ⟨h1, h2⟩
    have := hnos k
    refine ⟨fun hk => by subst hk; omega, by omega, by omega⟩
  · rintro ⟨hkj, h1, h2⟩
    refine ⟨by have := hnos k; omega, ?_⟩
    by_contra hn
    have hn' : ((scale J).d k : ℤ) ≤ t := by omega
    exact hnod k hkj ⟨h2, hn'⟩

/-- When a job starts and nothing else happens, only that job joins. -/
theorem alive_start {t' t : ℤ} {j : (scale J).Job} (hq : 0 < (scale J).q j)
    (hsj : s (I := scale J) j = t) (htt : t' < t)
    (hnos : ∀ k : (scale J).Job, k ≠ j → ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : (scale J).Job, ¬ (t' < ((scale J).d k : ℤ) ∧ ((scale J).d k : ℤ) ≤ t)) :
    alive J t = insert j (alive J t') := by
  ext k
  rw [Finset.mem_insert, mem_alive, mem_alive]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hk : k = j
    · exact Or.inl hk
    · right
      have := hnos k hk
      refine ⟨by omega, by omega⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · refine ⟨by omega, ?_⟩
      have : s (I := scale J) k = ((scale J).d k : ℤ) - (scale J).q k := rfl
      omega
    · refine ⟨by omega, ?_⟩
      by_contra hn
      have hn' : ((scale J).d k : ℤ) ≤ t := by omega
      exact hnod k ⟨h2, hn'⟩

theorem j_not_mem_alive_start {t' t : ℤ} {j : (scale J).Job} (hsj : s (I := scale J) j = t)
    (htt : t' < t) : j ∉ alive J t' := by
  rw [mem_alive]; omega

/-! ## The table, and what it says -/

/-- The mask of the slots a set of jobs occupies. -/
def mk (sl : (scale J).Job → ℕ) (X : Finset (scale J).Job) : ℕ := maskOf (X.image sl)

/-- The slots are distinct among the jobs running at `t`. -/
def SlotInj (J : Instance) (sl : (scale J).Job → ℕ) (t : ℤ) : Prop :=
  ∀ i ∈ alive J t, ∀ k ∈ alive J t, sl i = sl k → i = k

/-- **`T` is the true table at the instant `t`.** Its entry at a mask that is the slot set of a
set `X` of running jobs, and at a weight `c ≤ W`, is the least *unscaled* load of a partial
solution running exactly `X` and of weight at least `c` (`INF` if there is none); at every other
mask it is `INF`. -/
structure Rel (J : Instance) (sl : (scale J).Job → ℕ) (t : ℤ) (W INF : ℕ)
    (T : ℕ → ℕ → ℕ) : Prop where
  ge_iff : ∀ X : Finset (scale J).Job, X ⊆ alive J t → ∀ c, c ≤ W → ∀ P : ℤ,
    Ge (scale J) t X c P ↔
      (T (mk sl X) c < INF ∧ ((Nsc J * T (mk sl X) c : ℕ) : ℤ) ≤ P)
  junk : ∀ mask c, c ≤ W → (∀ X ⊆ alive J t, mk sl X ≠ mask) → T mask c = INF

/-- The table after job `j`'s due date: states that still held `j` merge into the state without
it, and the slot is cleared. -/
def dueT (b INF : ℕ) (T : ℕ → ℕ → ℕ) (X c : ℕ) : ℕ :=
  if X / 2 ^ b % 2 = 1 then INF else min (T X c) (T (X + 2 ^ b) c)

/-- The table after job `j` starts in slot `b`: the states holding `j` come from the states
without it, if the load still fits before `s_j` and a machine is free. -/
def startT (b w p q d m INF : ℕ) (T : ℕ → ℕ → ℕ) (X c : ℕ) : ℕ :=
  if X / 2 ^ b % 2 = 1 then
    (if pcnt (X - 2 ^ b) < m ∧ T (X - 2 ^ b) (c - w) + p + q ≤ d then
      T (X - 2 ^ b) (c - w) + p else INF)
  else T X c

theorem div_bit_mk {sl : (scale J).Job → ℕ} {X : Finset (scale J).Job} {b : ℕ} :
    mk sl X / 2 ^ b % 2 = 1 ↔ b ∈ X.image sl := by
  rw [← testBit_iff_div]; exact testBit_maskOf

theorem mk_insert {sl : (scale J).Job → ℕ} {X : Finset (scale J).Job} {j : (scale J).Job}
    (h : sl j ∉ X.image sl) : mk sl (insert j X) = mk sl X + 2 ^ sl j := by
  unfold mk
  rw [Finset.image_insert, maskOf_insert h]

theorem mem_image_iff_of_inj {A X : Finset (scale J).Job} {sl : (scale J).Job → ℕ}
    (hinj : ∀ i ∈ A, ∀ k ∈ A, sl i = sl k → i = k) (hX : X ⊆ A) {j : (scale J).Job} (hj : j ∈ A) :
    sl j ∈ X.image sl ↔ j ∈ X := by
  constructor
  · intro h
    obtain ⟨k', hk', hkk⟩ := Finset.mem_image.mp h
    exact (hinj k' (hX hk') j hj hkk) ▸ hk'
  · intro h; exact Finset.mem_image_of_mem sl h

end Lax496464Proofs.Ram.W3Tab
