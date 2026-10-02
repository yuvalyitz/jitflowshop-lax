import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMain
import Lax496464Proofs.WHierarchy.Machine.SizeFacts

/-!
# The Value Bound and the Cost Bound

`BF_Bv`: the value bound `Bv D x` has the properties `BF` the program needs. `Kprog_le`: the cost
is at most `400 · T^e` for `T = Cc · (|x| + 1) · (k + 1)` and `e = r + s + 2`, so fixed-parameter
in `k` for the fixed formula.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds

open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgClause
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgZ Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgLoop
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgFill Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMain

/-! ### The largest entry -/

/-- The largest entry of a word. -/
def mx (x : List ℕ) : ℕ := x.foldr max 0

theorem le_mx {x : List ℕ} {v : ℕ} (h : v ∈ x) : v ≤ mx x := by
  induction x with
  | nil => simp at h
  | cons a t ih =>
    simp only [mx, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem getD_le_mx (x : List ℕ) (i : ℕ) : x.getD i 0 ≤ mx x := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : x[i]? with _ | v
  · simp
  · exact le_mx (List.mem_of_getElem? h)

theorem mx_lt (x : List ℕ) : mx x < 2 ^ Lax759944.BinaryWordEncoding.bitSize x := by
  induction x with
  | nil => simp [mx]
  | cons a t ih =>
    simp only [mx, List.foldr_cons] at ih ⊢
    have h1 := Lax496464Proofs.WHierarchy.Machine.SizeFacts.lt_two_pow_bitSize (x := a :: t) (v := a) (by simp)
    have h2 : 2 ^ Lax759944.BinaryWordEncoding.bitSize t ≤
        2 ^ Lax759944.BinaryWordEncoding.bitSize (a :: t) := Nat.pow_le_pow_right (by norm_num)
      (by rw [Lax496464Proofs.WHierarchy.Machine.SizeFacts.bitSize_cons]; omega)
    exact max_lt h1 (by omega)

/-! ### The value bound -/

/-- A linear bound on everything linear in the word. -/
def Wv (D : Data) (x : List ℕ) : ℕ := 2 * x.length + (D.s + 1) * mx x + cD D + 3

/-- **The value bound.** -/
def Bv (D : Data) (x : List ℕ) : ℕ := (Wv D x + 1) ^ (D.r + D.s) * (D.cnf.length + 2) + Wv D x + 3

theorem LW_le' (D : Data) (x : List ℕ) : LW D.s D.r x ≤ x.length + D.s * kW x + D.r :=
  min_le_right _ _

theorem nW_le (D : Data) (x : List ℕ) : nW D x ≤ 2 * x.length + D.s * kW x + D.r := by
  have := length_UW_le D.s D.r x
  have := LW_le' D x
  unfold nW U; omega

theorem r_le_cD (D : Data) : D.r + D.s ≤ cD D := by unfold cD; omega

theorem BF_Bv (D : Data) (x : List ℕ) : BF D x (Bv D x) := by
  have hk : kW x ≤ mx x := getD_le_mx _ _
  have hsk : D.s * kW x ≤ D.s * mx x := Nat.mul_le_mul_left _ hk
  have hn := nW_le D x
  have hL := LW_le' D x
  have hr := r_le_cD D
  have hmx : (D.s + 1) * mx x = D.s * mx x + mx x := by ring
  have hW : 2 * x.length + D.s * kW x + D.r + 2 < Wv D x := by
    unfold Wv; rw [hmx]; omega
  have hB1 : Wv D x + 3 ≤ Bv D x := by unfold Bv; omega
  refine ⟨fun v hv => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := le_mx hv
    have : mx x ≤ Wv D x := by unfold Wv; nlinarith
    omega
  · unfold Wv at hB1; omega
  · omega
  · omega
  · have : (nW D x + 1) ^ (D.r + D.s) * (D.cnf.length + 2) ≤
        (Wv D x + 1) ^ (D.r + D.s) * (D.cnf.length + 2) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
    unfold Bv; omega
  · omega

/-! ### The cost -/

theorem sum_le_sum {l : List Lit} {f g : Lit → ℕ} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem sum_le_sum' {l : List (List Lit)} {f g : List Lit → ℕ} (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem sum_map_mul {α : Type} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map fun a => f a * c).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_mul]

/-- The constant of a clause. -/
def cC (C : List Lit) : ℕ := (C.map fun l => 27 * l.atom.idxs.length + 100).sum + 31

/-- The constant of an assignment. -/
def cz (D : Data) : ℕ := 20 * D.r + 10 + (D.cnf.map cC).sum

theorem KC_le (x : List ℕ) (C : List Lit) : KC x C ≤ cC C * (x.length + 1) := by
  unfold KC cC
  have h1 : (C.map (Klit x)).sum + (C.map fun l => 7 * l.atom.idxs.length + 8).sum =
      (C.map fun l => Klit x l + (7 * l.atom.idxs.length + 8)).sum :=
    (List.sum_map_add (l := C) (f := Klit x) (g := fun l => 7 * l.atom.idxs.length + 8)).symm
  have h2 : (C.map fun l => Klit x l + (7 * l.atom.idxs.length + 8)).sum ≤
      (C.map fun l => (27 * l.atom.idxs.length + 100) * (x.length + 1)).sum :=
    sum_le_sum fun l _ => by
      unfold Klit Krel
      have : (20 * l.atom.idxs.length + 19) * x.length ≤
          (27 * l.atom.idxs.length + 100) * x.length := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.mul_add]; omega
  rw [sum_map_mul] at h2
  rw [Nat.add_mul]; omega

theorem Kz_le (D : Data) (x : List ℕ) : Kz D x ≤ cz D * (x.length + 1) := by
  unfold Kz Kcls cz
  have h1 : (D.cnf.map (KC x)).sum ≤ (D.cnf.map fun C => cC C * (x.length + 1)).sum :=
    sum_le_sum' fun C _ => KC_le x C
  rw [sum_map_mul] at h1
  have h2 : (20 * D.r + 10) ≤ (20 * D.r + 10) * (x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rw [Nat.add_mul]; omega

/-- The constant of the program. -/
def Cc (D : Data) : ℕ := D.s + D.r + 2 + cz D + cD D + 12 * D.rels.length + 200

/-- The exponent. -/
def ee (D : Data) : ℕ := D.r + D.s + 2

/-- The size-and-parameter quantity. -/
def Tq (D : Data) (x : List ℕ) : ℕ := Cc D * ((x.length + 1) * (kW x + 1))

theorem pow_le_pow_ee {T a e : ℕ} (hT : 1 ≤ T) (h : a ≤ e) : T ^ a ≤ T ^ e :=
  Nat.pow_le_pow_right hT h

set_option maxHeartbeats 2000000 in
/-- **The cost bound.** -/
theorem Kprog_le (D : Data) (x : List ℕ) (hg : Good x) :
    Kprog D x ≤ 400 * Tq D x ^ ee D := by
  set T := Tq D x with hT
  set e := ee D with he
  set X := x.length + 1 with hX
  set K := kW x + 1 with hK
  have hXK : X ≤ X * K := Nat.le_mul_of_pos_right _ (by omega)
  have hG : 2 * x.length + D.s * kW x + D.r + 1 ≤ (D.s + D.r + 2) * (X * K) := by
    have : D.s * kW x ≤ D.s * (X * K) := Nat.mul_le_mul_left _ (by
      have : kW x ≤ K := by omega
      exact this.trans (Nat.le_mul_of_pos_left _ (by omega)))
    have h2 : D.r + 1 ≤ D.r * (X * K) + (X * K) := by nlinarith
    nlinarith
  have hCc : D.s + D.r + 2 ≤ Cc D := by unfold Cc; omega
  have hT1 : (D.s + D.r + 2) * (X * K) ≤ T := by rw [hT, Tq]; exact Nat.mul_le_mul_right _ hCc
  have hTX : Cc D * X ≤ T := by rw [hT, Tq]; exact Nat.mul_le_mul_left _ hXK
  have hCcX : Cc D ≤ Cc D * X := Nat.le_mul_of_pos_right _ (by omega)
  have hCT : Cc D ≤ T := hCcX.trans hTX
  have hXT : X ≤ T := by
    have : X ≤ Cc D * X := Nat.le_mul_of_pos_left _ (by unfold Cc; omega)
    omega
  have hn := nW_le D x
  have hL := LW_le' D x
  have hsp := hg.head
  -- the linear quantities are below `T`
  have hnT : nW D x ≤ T := by omega
  have hcapT : capW D x ≤ T := by unfold capW; omega
  have hLT : LW D.s D.r x ≤ T := by omega
  have hspT : spW x ≤ T := by omega
  have hcz : cz D ≤ Cc D := by unfold Cc; omega
  have hKz : Kz D x ≤ T * T := (Kz_le D x).trans (Nat.mul_le_mul (hcz.trans hCT) hXT)
  have hrels : 12 * D.rels.length + 200 ≤ T := by unfold Cc at hCT; omega
  have hrs : D.r + D.s + 1 ≤ T := by unfold Cc at hCT; omega
  have hT2 : 2 ≤ T := by unfold Cc at hCT; omega
  -- powers
  have hpr : nW D x ^ D.r ≤ T ^ D.r := Nat.pow_le_pow_left hnT _
  have hps : nW D x ^ D.s ≤ T ^ D.s := Nat.pow_le_pow_left hnT _
  have e1 : T ≤ T ^ e := by
    have := pow_le_pow_ee (T := T) (a := 1) (e := e) (by omega) (by rw [he, ee]; omega)
    simpa using this
  have e2 : T ^ 2 ≤ T ^ e := pow_le_pow_ee (by omega) (by rw [he, ee]; omega)
  have e3 : T ^ (D.r + 2) ≤ T ^ e := pow_le_pow_ee (by omega) (by rw [he, ee]; omega)
  have e4 : T ^ D.s ≤ T ^ e := pow_le_pow_ee (by omega) (by rw [he, ee]; omega)
  have e5 : T ^ D.r ≤ T ^ e := pow_le_pow_ee (by omega) (by rw [he, ee]; omega)
  have hsq : T * T = T ^ 2 := by ring
  have hr2 : T * T * T ^ D.r = T ^ (D.r + 2) := by ring
  -- the products
  have p1 : (Kz D x + 4) * nW D x ^ D.r ≤ 5 * T ^ (D.r + 2) := by
    have h1 : (Kz D x + 4) * nW D x ^ D.r ≤ (T * T + 4) * T ^ D.r :=
      Nat.mul_le_mul (by omega) hpr
    have h2 : 4 * T ^ D.r ≤ 4 * (T * T * T ^ D.r) := by
      have : T ^ D.r ≤ T * T * T ^ D.r := Nat.le_mul_of_pos_left _ (by nlinarith)
      omega
    nlinarith
  have p2 : (16 * capW D x + 70 + 4) * x.length ≤ 90 * T ^ 2 := by
    have h1 : (16 * capW D x + 70 + 4) * x.length ≤ (16 * T + 74) * T :=
      Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have p3 : (10 + 4) * LW D.s D.r x ≤ 14 * T := by omega
  have p4 : (20 + 4) * nW D x ^ D.s ≤ 24 * T ^ D.s := by omega
  unfold Kprog Kmain
  omega

theorem Tq_le (D : Data) (x : List ℕ) :
    Tq D x ^ ee D ≤ Cc D ^ ee D * (kW x + 1) ^ ee D *
      (Lax759944.BinaryWordEncoding.bitSize x + 1) ^ ee D := by
  unfold Tq
  have hl := Lax496464Proofs.WHierarchy.Machine.SizeFacts.length_le_bitSize x
  rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm ((x.length + 1) ^ ee D)]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Bounds
