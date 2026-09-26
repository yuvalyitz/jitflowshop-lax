import Lax496464Proofs.Ram.W3Rel

/-!
# The width sweep as a table over masks: the pure model

Final statements (`J : Instance`; `hE : EstOrdered J`; `hq : ∀ i, 0 < J.q i`;
`hINF : ∀ j, J.d j ≤ INF`, `0 < INF`; for the concrete choice `INF = maxd J + 2`):

* `evs J : List (Ev J)` — the merge of the starts `0, …, n-1` (index order) and the dues
  (sorted by `(d, index)`), taking a start `i` before a due `j` exactly when
  `startFirst J i j` (`J.d i < J.d j + J.q i ∨ (J.d i = J.d j + J.q i ∧ i < j)`);
  `startFirst_iff : startFirst J i j = true ↔ (scale J).s i < (scale J).d j`;
  `evs_length : (evs J).length = 2 * J.jobs`; `evs_pairwise : (evs J).Pairwise (evTime < evTime)`.
* `tab J INF l : St J` — the free stack `free`, the fresh counter `next`, the slot
  assignment `sl` and the table `T`, after processing the events `l`, by a `List.foldl` of `step`.
* `sweep_correct : (tab J INF (evs J)).T 0 W < INF ↔ J.HasWeight W` (for every `W`), and
  `sweep_correct_maxd` for `INF = maxd J + 2`.
* `sweep_slot_lt : ∀ j, (tab J INF (evs J)).sl j < peakS J` (peak of scaled-alive counts at
  starts), `sweep_slot_lt_width : … < widthJ J`, `sweep_next_le : (tab …).next ≤ widthJ J`,
  `peakS_le_width`, and `aliveScaled_card_le : (alive J (scaled s i)).card ≤
  #{k | s k ≤ s i ∧ s i < d k}` (unscaled, `widthJ J` = the max over `i`).
* the invariant `Inv` and one-event step `inv_step`, and `final_inv` (invariant after all events).
-/

namespace Lax496464Proofs.Ram.W3Model

open Lax496464.FlowShop Lax496464.EstOrder Lax496464.Sweep
open Lax496464.FlowShop.Instance (s Feasible weight HasWeight)
open Lax496464Proofs.Ram.W3Bits Lax496464Proofs.Ram.W3Tab Lax496464Proofs.Ram.W3Rel

/-! ## Events, and the merge -/

/-- An event of the sweep: a job starts, or a job becomes due. -/
inductive Ev (J : Instance) : Type
  | start (j : (scale J).Job)
  | due (j : (scale J).Job)
  deriving DecidableEq

/-- The (scaled) time of an event. -/
def evTime (J : Instance) : Ev J → ℤ
  | .start j => s (I := scale J) j
  | .due j => ((scale J).d j : ℤ)

/-- The merge of two lists, taking the left head `x` before the right head `y` when `f x y`. -/
def mergeBy {α β γ : Type} (f : α → β → Bool) (l : α → γ) (r : β → γ) :
    List α → List β → List γ
  | [], ys => ys.map r
  | x :: xs, [] => (x :: xs).map l
  | x :: xs, y :: ys =>
    if f x y then l x :: mergeBy f l r xs (y :: ys) else r y :: mergeBy f l r (x :: xs) ys

section merge

variable {α β γ : Type} (f : α → β → Bool) (l : α → γ) (r : β → γ)

theorem mergeBy_perm : ∀ (xs : List α) (ys : List β),
    (mergeBy f l r xs ys).Perm (xs.map l ++ ys.map r)
  | [], ys => by simp [mergeBy]
  | x :: xs, [] => by simp [mergeBy]
  | x :: xs, y :: ys => by
    unfold mergeBy
    split_ifs
    · simpa using (mergeBy_perm xs (y :: ys)).cons (l x)
    · have := (mergeBy_perm (x :: xs) ys).cons (r y)
      refine this.trans ?_
      rw [List.map_cons]
      exact List.perm_middle.symm

theorem mergeBy_pairwise (tm : γ → ℤ)
    (hf : ∀ x y, f x y = true ↔ tm (l x) < tm (r y))
    (hne : ∀ x y, tm (l x) ≠ tm (r y)) :
    ∀ (xs : List α) (ys : List β),
      xs.Pairwise (fun a b => tm (l a) < tm (l b)) →
      ys.Pairwise (fun a b => tm (r a) < tm (r b)) →
      (mergeBy f l r xs ys).Pairwise (fun a b => tm a < tm b)
  | [], ys, _, hy => by
    unfold mergeBy
    rw [List.pairwise_map]; exact hy
  | x :: xs, [], hx, _ => by
    unfold mergeBy
    rw [List.pairwise_map]; exact hx
  | x :: xs, y :: ys, hx, hy => by
    unfold mergeBy
    have hx' := List.pairwise_cons.mp hx
    have hy' := List.pairwise_cons.mp hy
    split_ifs with hxy
    · rw [List.pairwise_cons]
      refine ⟨?_, mergeBy_pairwise tm hf hne xs (y :: ys) hx'.2 hy⟩
      intro z hz
      rw [(mergeBy_perm f l r xs (y :: ys)).mem_iff] at hz
      simp only [List.mem_append, List.mem_map, List.mem_cons] at hz
      rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact hx'.1 a ha
      · rcases hb with rfl | hb
        · exact (hf x b).mp hxy
        · exact lt_trans ((hf x y).mp hxy) (hy'.1 b hb)
    · rw [List.pairwise_cons]
      refine ⟨?_, mergeBy_pairwise tm hf hne (x :: xs) ys hx hy'.2⟩
      intro z hz
      rw [(mergeBy_perm f l r (x :: xs) ys).mem_iff] at hz
      simp only [List.mem_append, List.mem_map, List.mem_cons] at hz
      have hyx : tm (r y) < tm (l x) := by
        have h1 : ¬ tm (l x) < tm (r y) := fun h => hxy ((hf x y).mpr h)
        exact lt_of_le_of_ne (not_lt.mp h1) (hne x y).symm
      rcases hz with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · rcases ha with rfl | ha
        · exact hyx
        · exact lt_trans hyx (hx'.1 a ha)
      · exact hy'.1 b hb

end merge

/-! ## The merge rule and the two sorted lists -/

/-- The arithmetic behind the merge rule: with `0 ≤ i, j < N`, `N·x + i < j` iff `x < 0`,
or `x = 0` and `i < j`. -/
theorem lin_lt (N x i j : ℤ) (hi0 : 0 ≤ i) (hiN : i < N) (hj0 : 0 ≤ j) (hjN : j < N) :
    N * x + i < j ↔ x < 0 ∨ (x = 0 ∧ i < j) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : N * x ≤ -N := by nlinarith
    constructor
    · intro _; exact Or.inl hx
    · intro _; linarith
  · subst hx; simp
  · have : N ≤ N * x := by nlinarith
    constructor
    · intro h; linarith
    · rintro (h | ⟨h, _⟩) <;> omega

theorem lin_le (N x i j : ℤ) (hi0 : 0 ≤ i) (hiN : i < N) (hj0 : 0 ≤ j) (hjN : j < N) :
    N * x + i ≤ j ↔ x < 0 ∨ (x = 0 ∧ i ≤ j) := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : N * x ≤ -N := by nlinarith
    constructor
    · intro _; exact Or.inl hx
    · intro _; linarith
  · subst hx; simp
  · have : N ≤ N * x := by nlinarith
    constructor
    · intro h; linarith
    · rintro (h | ⟨h, _⟩) <;> omega

/-- **The merge rule**, in unscaled naturals: a start `i` comes before a due `j` iff
`d i < d j + q i`, or they are equal and `i < j`. -/
def startFirst (J : Instance) (i j : (scale J).Job) : Bool :=
  decide (J.d i < J.d j + J.q i ∨ (J.d i = J.d j + J.q i ∧ i < j))

theorem startFirst_iff (J : Instance) (i j : (scale J).Job) :
    startFirst J i j = true ↔ s (I := scale J) i < ((scale J).d j : ℤ) := by
  unfold startFirst
  rw [decide_eq_true_iff, sc_s J i, sc_d J j]
  have hi : (i : ℕ) < J.jobs := i.isLt
  have hj : (j : ℕ) < J.jobs := j.isLt
  have hN : (Nsc J : ℤ) = (J.jobs : ℤ) + 1 := by unfold Nsc; push_cast; ring
  have hsi : s (I := J) i = (J.d i : ℤ) - J.q i := rfl
  have key := lin_lt (Nsc J) ((J.d i : ℤ) - J.q i - J.d j) (i : ℕ) (j : ℕ) (by positivity)
    (by rw [hN]; exact_mod_cast Nat.lt_succ_of_lt hi) (by positivity)
    (by rw [hN]; exact_mod_cast Nat.lt_succ_of_lt hj)
  rw [hsi]
  push_cast
  have e : (Nsc J : ℤ) * ((J.d i : ℤ) - J.q i) + (i : ℕ) < (Nsc J : ℤ) * J.d j + (j : ℕ) ↔
      (Nsc J : ℤ) * ((J.d i : ℤ) - J.q i - J.d j) + (i : ℕ) < (j : ℕ) := by
    constructor <;> intro h <;> linarith
  rw [e, key]
  have : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) ↔ i < j := by
    rw [Int.ofNat_lt]; rfl
  constructor
  · rintro (h | ⟨h, h'⟩)
    · left; omega
    · right; exact ⟨by omega, this.mpr h'⟩
  · rintro (h | ⟨h, h'⟩)
    · left; omega
    · right; exact ⟨by omega, this.mp h'⟩

/-- The order on due dates: `(d, index)` lexicographically. -/
def dueLE (J : Instance) (i j : (scale J).Job) : Bool :=
  decide (J.d i < J.d j ∨ (J.d i = J.d j ∧ i ≤ j))

theorem dueLE_iff (J : Instance) (i j : (scale J).Job) :
    dueLE J i j = true ↔ ((scale J).d i : ℤ) ≤ ((scale J).d j : ℤ) := by
  unfold dueLE
  rw [decide_eq_true_iff, sc_d J i, sc_d J j]
  have hi : (i : ℕ) < J.jobs := i.isLt
  have hj : (j : ℕ) < J.jobs := j.isLt
  have hN : (Nsc J : ℤ) = (J.jobs : ℤ) + 1 := by unfold Nsc; push_cast; ring
  have key := lin_le (Nsc J) ((J.d i : ℤ) - J.d j) (i : ℕ) (j : ℕ) (by positivity)
    (by rw [hN]; exact_mod_cast Nat.lt_succ_of_lt hi) (by positivity)
    (by rw [hN]; exact_mod_cast Nat.lt_succ_of_lt hj)
  push_cast
  have e : (Nsc J : ℤ) * J.d i + (i : ℕ) ≤ (Nsc J : ℤ) * J.d j + (j : ℕ) ↔
      (Nsc J : ℤ) * ((J.d i : ℤ) - J.d j) + (i : ℕ) ≤ (j : ℕ) := by
    constructor <;> intro h <;> linarith
  rw [e, key]
  have : ((i : ℕ) : ℤ) ≤ ((j : ℕ) : ℤ) ↔ i ≤ j := by
    rw [Int.ofNat_le]; rfl
  constructor
  · rintro (h | ⟨h, h'⟩)
    · left; omega
    · right; exact ⟨by omega, this.mpr h'⟩
  · rintro (h | ⟨h, h'⟩)
    · left; omega
    · right; exact ⟨by omega, this.mp h'⟩

/-- The jobs in order of their (scaled) due dates: `(d, index)` lexicographically. -/
def dueOrder (J : Instance) : List (scale J).Job :=
  (List.finRange (scale J).jobs).mergeSort (dueLE J)

/-- **The event list**: the merge of the starts, in index order, with the dues, in due order. -/
def evs (J : Instance) : List (Ev J) :=
  mergeBy (startFirst J) Ev.start Ev.due (List.finRange (scale J).jobs) (dueOrder J)

theorem dueOrder_perm (J : Instance) : (dueOrder J).Perm (List.finRange (scale J).jobs) :=
  List.mergeSort_perm _ _

theorem dueOrder_pairwise (J : Instance) :
    (dueOrder J).Pairwise (fun a b => ((scale J).d a : ℤ) < ((scale J).d b : ℤ)) := by
  have h1 : (dueOrder J).Pairwise (fun a b => dueLE J a b = true) := by
    unfold dueOrder
    refine List.pairwise_mergeSort ?_ ?_ _
    · intro a b c hab hbc
      rw [dueLE_iff] at *
      exact le_trans hab hbc
    · intro a b
      simp only [Bool.or_eq_true, dueLE_iff]
      exact le_total _ _
  have h2 : (dueOrder J).Pairwise (fun a b => a ≠ b) :=
    List.nodup_iff_pairwise_ne.mp ((dueOrder_perm J).nodup_iff.mpr (List.nodup_finRange _))
  refine (h1.and h2).imp ?_
  rintro a b ⟨hab, hne⟩
  rw [dueLE_iff] at hab
  refine lt_of_le_of_ne hab fun h => hne ?_
  -- equal scaled due dates: the indices agree
  have hlt : dueLE J a b = true := (dueLE_iff J a b).mpr hab
  have hgt : dueLE J b a = true := (dueLE_iff J b a).mpr h.symm.le
  unfold dueLE at hlt hgt
  rw [decide_eq_true_iff] at hlt hgt
  rcases hlt with h1 | ⟨h1e, h1⟩ <;> rcases hgt with h2 | ⟨h2e, h2⟩
  · omega
  · omega
  · omega
  · exact le_antisymm h1 h2

theorem startOrder_pairwise (J : Instance) (hE : EstOrdered J) :
    (List.finRange (scale J).jobs).Pairwise
      (fun a b => s (I := scale J) a < s (I := scale J) b) := by
  refine (List.pairwise_lt_finRange J.jobs).imp ?_
  intro a b hab
  rw [sc_s J a, sc_s J b]
  have h1 : s (I := J) a ≤ s (I := J) b := hE a b hab.le
  have h2 : (Nsc J : ℤ) * s (I := J) a ≤ (Nsc J : ℤ) * s (I := J) b :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
  linarith

/-- The event list is strictly increasing in (scaled) time. -/
theorem evs_pairwise (J : Instance) (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) :
    (evs J).Pairwise (fun a b => evTime J a < evTime J b) := by
  refine mergeBy_pairwise (startFirst J) Ev.start Ev.due (evTime J)
    (fun x y => startFirst_iff J x y)
    (fun x y => (Section4.scale_distinctEndpoints J hE hq).1.start_ne_due x y) _ _
    (startOrder_pairwise J hE) (dueOrder_pairwise J)

/-- Every event occurs. -/
theorem mem_evs (J : Instance) (e : Ev J) : e ∈ evs J := by
  unfold evs
  rw [(mergeBy_perm _ _ _ _ _).mem_iff]
  cases e with
  | start j => simp
  | due j =>
    simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and]
    right
    exact ⟨j, (dueOrder_perm J).mem_iff.mpr (List.mem_finRange j), rfl⟩

/-! ## The sweep: slots and table, event by event -/

/-- The state of the sweep: the LIFO stack `free` of freed slots, the counter `next` of the
slots ever handed out fresh, the slot `sl j` of each job (meaningful from its start), and the
table `T` (mask ↦ weight ↦ least unscaled load, `INF` for none). -/
structure St (J : Instance) where
  free : List ℕ
  next : ℕ
  sl : (scale J).Job → ℕ
  T : ℕ → ℕ → ℕ

/-- The state before any event: no slot handed out, the table holds the empty selection. -/
def St.init (J : Instance) (INF : ℕ) : St J :=
  { free := [], next := 0, sl := fun _ => 0, T := fun X c => if X = 0 ∧ c = 0 then 0 else INF }

/-- One event. A start pops the free stack (or takes the next fresh slot), records the slot in
`sl`, and applies `startT`; a due pushes the job's slot back and applies `dueT`. -/
def step (J : Instance) (INF : ℕ) (st : St J) : Ev J → St J
  | .start j =>
    match st.free with
    | [] => { free := [], next := st.next + 1, sl := Function.update st.sl j st.next,
              T := startT st.next (J.w j) (J.p j) (J.q j) (J.d j) J.machines INF st.T }
    | b :: r => { free := r, next := st.next, sl := Function.update st.sl j b,
                  T := startT b (J.w j) (J.p j) (J.q j) (J.d j) J.machines INF st.T }
  | .due j => { free := st.sl j :: st.free, next := st.next, sl := st.sl,
                T := dueT (st.sl j) INF st.T }

/-- The state after a list of events. -/
def tab (J : Instance) (INF : ℕ) (l : List (Ev J)) : St J :=
  l.foldl (step J INF) (St.init J INF)

/-- **The invariant**, at the time `t`, after the events `pre`. -/
structure Inv (J : Instance) (INF W ω : ℕ) (pre : List (Ev J)) (st : St J) (t : ℤ) :
    Prop where
  rel : Rel J st.sl t W INF st.T
  inj : SlotInj J st.sl t
  cover : (alive J t).image st.sl ∪ st.free.toFinset = Finset.range st.next
  disj : Disjoint ((alive J t).image st.sl) st.free.toFinset
  nodup : st.free.Nodup
  peak : st.next ≤ ω
  bnd : ∀ k, Ev.start k ∈ pre → st.sl k < st.next

variable {J : Instance}

theorem inv_due (hq : ∀ i : J.Job, 0 < J.q i) {INF W ω : ℕ} {pre : List (Ev J)}
    {st : St J} {t' t : ℤ} {j : (scale J).Job}
    (hI : Inv J INF W ω pre st t') (htt : t' < t) (hdj : ((scale J).d j : ℤ) = t)
    (hnos : ∀ k : (scale J).Job, ¬ (t' < s (I := scale J) k ∧ s (I := scale J) k ≤ t))
    (hnod : ∀ k : (scale J).Job, k ≠ j →
      ¬ (t' < ((scale J).d k : ℤ) ∧ ((scale J).d k : ℤ) ≤ t)) :
    Inv J INF W ω (pre ++ [Ev.due j]) (step J INF st (Ev.due j)) t := by
  obtain ⟨hrel, hinj, hcov, hdis, hnd, hpk, hbnd⟩ := hI
  have hj : j ∈ alive J t' := due_mem_alive hq htt hdj hnos
  have halive := alive_due htt hdj hnos hnod
  have hbimg : st.sl j ∈ (alive J t').image st.sl := Finset.mem_image_of_mem _ hj
  have himg : (alive J t).image st.sl = ((alive J t').image st.sl).erase (st.sl j) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase, halive]
    constructor
    · rintro ⟨a, ⟨hne, ha⟩, rfl⟩
      exact ⟨fun h => hne (hinj a ha j hj h), a, ha, rfl⟩
    · rintro ⟨hne, a, ha, rfl⟩
      exact ⟨a, ⟨fun h => hne (by rw [h]), ha⟩, rfl⟩
  have hstep : step J INF st (Ev.due j) =
      { free := st.sl j :: st.free, next := st.next, sl := st.sl, T := dueT (st.sl j) INF st.T } :=
    rfl
  rw [hstep]
  refine ⟨due_rel hq hrel hinj htt hdj hnos hnod, slotInj_due hinj htt hdj hnos hnod, ?_, ?_, ?_, hpk, ?_⟩
  · show (alive J t).image st.sl ∪ (st.sl j :: st.free).toFinset = Finset.range st.next
    rw [himg, ← hcov]
    ext x
    simp only [Finset.mem_union, Finset.mem_erase, List.toFinset_cons, Finset.mem_insert,
      List.mem_toFinset]
    by_cases hx : x = st.sl j
    · subst hx
      have : st.sl j ∈ (alive J t').image st.sl := hbimg
      simp [this]
    · simp [hx]
  · show Disjoint ((alive J t).image st.sl) (st.sl j :: st.free).toFinset
    rw [himg, Finset.disjoint_left]
    intro x hx hx'
    have hx1 := Finset.mem_erase.mp hx
    simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at hx'
    rcases hx' with h | h
    · exact hx1.1 h
    · exact Finset.disjoint_left.mp hdis hx1.2 (List.mem_toFinset.mpr h)
  · show (st.sl j :: st.free).Nodup
    refine List.nodup_cons.mpr ⟨fun h => ?_, hnd⟩
    exact Finset.disjoint_left.mp hdis hbimg (List.mem_toFinset.mpr h)
  · intro k hk
    rw [List.mem_append] at hk
    rcases hk with hk | hk
    · exact hbnd k hk
    · simp at hk

theorem inv_start (hq : ∀ i : J.Job, 0 < J.q i) {INF W ω : ℕ} (hINF : ∀ j : J.Job, J.d j ≤ INF)
    {pre : List (Ev J)} {st : St J} {t' t : ℤ} {j : (scale J).Job}
    (hI : Inv J INF W ω pre st t') (hω : (alive J t).card ≤ ω)
    (htt : t' < t) (hsj : s (I := scale J) j = t)
    (hnos : ∀ k : (scale J).Job, k ≠ j → ¬ (t' < s (I := scale J) k ∧ s (I := scale J) k ≤ t))
    (hnod : ∀ k : (scale J).Job, ¬ (t' < ((scale J).d k : ℤ) ∧ ((scale J).d k : ℤ) ≤ t)) :
    Inv J INF W ω (pre ++ [Ev.start j]) (step J INF st (Ev.start j)) t := by
  obtain ⟨hrel, hinj, hcov, hdis, hnd, hpk, hbnd⟩ := hI
  have hjn : j ∉ alive J t' := j_not_mem_alive_start hsj htt
  have halive := alive_start (hqs hq j) hsj htt hnos hnod
  have hag : ∀ b, ∀ k ∈ alive J t', st.sl k = Function.update st.sl j b k := fun b k hk =>
    (Function.update_of_ne (fun h => hjn (by rw [← h]; exact hk)) b st.sl).symm
  have key : ∀ b, b ∉ (alive J t').image st.sl →
      Rel J (Function.update st.sl j b) t W INF
        (startT b (J.w j) (J.p j) (J.q j) (J.d j) J.machines INF st.T) ∧
      SlotInj J (Function.update st.sl j b) t := by
    intro b hb
    have hrel' := rel_congr (hag b) hrel
    have hinj' := (slotInj_congr (hag b)).mp hinj
    have hfree : ∀ k ∈ alive J t', Function.update st.sl j b k ≠ Function.update st.sl j b j := by
      intro k hk h
      rw [Function.update_self, ← hag b k hk] at h
      exact hb (by rw [← h]; exact Finset.mem_image_of_mem _ hk)
    have h1 := start_rel hq hrel' hinj' hfree (hINF j) htt hsj hnos hnod
    rw [Function.update_self] at h1
    exact ⟨h1, slotInj_start (hqs hq j) hinj' hfree hsj htt hnos hnod⟩
  have himg : ∀ b, (alive J t).image (Function.update st.sl j b) =
      insert b ((alive J t').image st.sl) := by
    intro b
    rw [halive, Finset.image_insert, Function.update_self]
    congr 1
    exact Finset.image_congr fun k hk => (hag b k hk).symm
  have hcard : (alive J t).card = (alive J t').card + 1 := by
    rw [halive, Finset.card_insert_of_notMem hjn]
  have hcard' : ((alive J t').image st.sl).card = (alive J t').card :=
    Finset.card_image_of_injOn fun a ha b hb hab => hinj a ha b hb hab
  rcases hf : st.free with _ | ⟨b, r⟩
  · -- nothing freed: the next fresh slot
    rw [hf] at hcov hdis hnd
    have himg0 : (alive J t').image st.sl = Finset.range st.next := by simpa using hcov
    have hb : st.next ∉ (alive J t').image st.sl := by rw [himg0]; simp
    obtain ⟨h1, h2⟩ := key st.next hb
    have hstep : step J INF st (Ev.start j) =
        { free := [], next := st.next + 1, sl := Function.update st.sl j st.next,
          T := startT st.next (J.w j) (J.p j) (J.q j) (J.d j) J.machines INF st.T } := by
      simp [step, hf]
    rw [hstep]
    refine ⟨h1, h2, ?_, ?_, List.nodup_nil, ?_, ?_⟩
    · show (alive J t).image (Function.update st.sl j st.next) ∪ ([] : List ℕ).toFinset =
        Finset.range (st.next + 1)
      rw [himg, himg0, Finset.range_add_one]; simp
    · show Disjoint ((alive J t).image (Function.update st.sl j st.next)) ([] : List ℕ).toFinset
      simp
    · show st.next + 1 ≤ ω
      have : (alive J t').card = st.next := by rw [← hcard', himg0]; simp
      omega
    · intro k hk
      rw [List.mem_append] at hk
      show Function.update st.sl j st.next k < st.next + 1
      rcases hk with hk | hk
      · by_cases hkj : k = j
        · subst hkj; simp [Function.update_self]
        · rw [Function.update_of_ne hkj]
          have := hbnd k hk
          omega
      · have : k = j := by simpa using hk
        subst this
        simp [Function.update_self]
  · rw [hf] at hcov hdis hnd
    have hbr : b ∉ (alive J t').image st.sl := fun h =>
      Finset.disjoint_left.mp hdis h (by simp)
    have hbn : b < st.next := by
      have : b ∈ Finset.range st.next := by rw [← hcov]; simp
      exact Finset.mem_range.mp this
    have hbr' : b ∉ r := (List.nodup_cons.mp hnd).1
    obtain ⟨h1, h2⟩ := key b hbr
    have hstep : step J INF st (Ev.start j) =
        { free := r, next := st.next, sl := Function.update st.sl j b,
          T := startT b (J.w j) (J.p j) (J.q j) (J.d j) J.machines INF st.T } := by
      simp [step, hf]
    rw [hstep]
    refine ⟨h1, h2, ?_, ?_, (List.nodup_cons.mp hnd).2, hpk, ?_⟩
    · show (alive J t).image (Function.update st.sl j b) ∪ r.toFinset = Finset.range st.next
      rw [himg, ← hcov]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons, List.mem_toFinset]
      tauto
    · show Disjoint ((alive J t).image (Function.update st.sl j b)) r.toFinset
      rw [himg, Finset.disjoint_left]
      intro x hx hx'
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hbr' (List.mem_toFinset.mp hx')
      · exact Finset.disjoint_left.mp hdis hx (by simp [List.mem_toFinset.mp hx'])
    · intro k hk
      rw [List.mem_append] at hk
      show Function.update st.sl j b k < st.next
      rcases hk with hk | hk
      · by_cases hkj : k = j
        · subst hkj; simp [Function.update_self, hbn]
        · rw [Function.update_of_ne hkj]
          exact hbnd k hk
      · have : k = j := by simpa using hk
        subst this
        simp [Function.update_self, hbn]

/-! ## The whole sweep -/

/-- One event, in the invariant's terms: whichever event `e` comes next, if it is the only one
in `(t', t]` the invariant passes from `t'` to `t`. -/
theorem inv_step (hq : ∀ i : J.Job, 0 < J.q i) {INF W ω : ℕ} (hINF : ∀ j : J.Job, J.d j ≤ INF)
    (hω : ∀ i : (scale J).Job, (alive J (s (I := scale J) i)).card ≤ ω)
    {pre : List (Ev J)} {st : St J} {t' t : ℤ} {e : Ev J}
    (hI : Inv J INF W ω pre st t') (htt : t' < t) (het : evTime J e = t)
    (hsep : ∀ f : Ev J, f ≠ e → ¬ (t' < evTime J f ∧ evTime J f ≤ t)) :
    Inv J INF W ω (pre ++ [e]) (step J INF st e) t := by
  cases e with
  | start j =>
    have hsj : s (I := scale J) j = t := het
    refine inv_start hq hINF hI (by rw [← hsj]; exact hω j) htt hsj ?_ ?_
    · intro k hk
      exact hsep (Ev.start k) (fun h => hk (Ev.start.inj h))
    · intro k
      exact hsep (Ev.due k) (fun h => by cases h)
  | due j =>
    have hdj : ((scale J).d j : ℤ) = t := het
    refine inv_due hq hI htt hdj ?_ ?_
    · intro k
      exact hsep (Ev.start k) (fun h => by cases h)
    · intro k hk
      exact hsep (Ev.due k) (fun h => hk (Ev.due.inj h))

theorem run_inv (hq : ∀ i : J.Job, 0 < J.q i) {INF W ω : ℕ} (hINF : ∀ j : J.Job, J.d j ≤ INF)
    (hω : ∀ i : (scale J).Job, (alive J (s (I := scale J) i)).card ≤ ω)
    (E : List (Ev J)) (hsorted : E.Pairwise (fun a b => evTime J a < evTime J b))
    (hall : ∀ e, e ∈ E) :
    ∀ (L pre : List (Ev J)) (st : St J) (t' : ℤ), E = pre ++ L → Inv J INF W ω pre st t' →
      (∀ f ∈ pre, evTime J f ≤ t') → (∀ f ∈ L, t' < evTime J f) →
      ∃ t'', Inv J INF W ω E (L.foldl (step J INF) st) t'' ∧ ∀ f ∈ E, evTime J f ≤ t'' := by
  intro L
  induction L with
  | nil =>
    intro pre st t' hEq hI hpre _
    rw [List.append_nil] at hEq
    subst hEq
    exact ⟨t', hI, hpre⟩
  | cons e L' ih =>
    intro pre st t' hEq hI hpre hL
    have hsorted' := hsorted
    rw [hEq] at hsorted'
    obtain ⟨-, hcons, hcross⟩ := List.pairwise_append.mp hsorted'
    have hcons' := List.pairwise_cons.mp hcons
    have htt : t' < evTime J e := hL e (List.mem_cons_self)
    have hLt : ∀ f ∈ L', evTime J e < evTime J f := hcons'.1
    have hsep : ∀ f : Ev J, f ≠ e → ¬ (t' < evTime J f ∧ evTime J f ≤ evTime J e) := by
      intro f hfe
      have hf := hall f
      rw [hEq, List.mem_append, List.mem_cons] at hf
      rcases hf with hf | hf | hf
      · have := hpre f hf
        omega
      · exact absurd hf hfe
      · have := hLt f hf
        omega
    have hI' := inv_step hq hINF hω hI htt rfl hsep
    obtain ⟨t'', h1, h2⟩ := ih (pre ++ [e]) (step J INF st e) (evTime J e)
      (by rw [hEq]; simp) hI'
      (by
        intro f hf
        rw [List.mem_append, List.mem_singleton] at hf
        rcases hf with hf | rfl
        · have := hpre f hf; omega
        · exact le_rfl)
      (fun f hf => hLt f hf)
    exact ⟨t'', h1, h2⟩

/-- The largest number of scaled-alive jobs at a scaled start. -/
noncomputable def peakS (J : Instance) : ℕ :=
  Finset.univ.sup fun i : (scale J).Job => (alive J (s (I := scale J) i)).card

open Classical in
/-- The width: the largest number of jobs running at a start, unscaled:
`max_i #{k | s k ≤ s i ∧ s i < d k}` (the concept's `widthOf`; jobs are `Fin J.jobs`, written
`(scale J).Job` because `scale` keeps the job type). -/
noncomputable def widthJ (J : Instance) : ℕ :=
  Finset.univ.sup fun i : (scale J).Job =>
    ((Finset.univ : Finset (scale J).Job).filter fun k : (scale J).Job =>
      s (I := J) k ≤ s (I := J) i ∧ s (I := J) i < (J.d k : ℤ)).card

theorem le_peakS (i : (scale J).Job) : (alive J (s (I := scale J) i)).card ≤ peakS J :=
  Finset.le_sup (f := fun i : (scale J).Job => (alive J (s (I := scale J) i)).card)
    (Finset.mem_univ i)

open Classical in
/-- **(a)** Scaling does not create width: a job running at a scaled start also runs, unscaled,
at the unscaled start. -/
theorem aliveScaled_sub (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) (i : (scale J).Job) :
    alive J (s (I := scale J) i) ⊆
      (Finset.univ : Finset (scale J).Job).filter fun k : (scale J).Job =>
        s (I := J) k ≤ s (I := J) i ∧ s (I := J) i < (J.d k : ℤ) := by
  intro k hk
  rw [mem_alive] at hk
  obtain ⟨h1, h2⟩ := hk
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  have hk' : (k : ℕ) < J.jobs := k.isLt
  have hi' : (i : ℕ) < J.jobs := i.isLt
  have hN : (Nsc J : ℤ) = (J.jobs : ℤ) + 1 := by unfold Nsc; push_cast; ring
  have hski : s (I := J) k ≤ s (I := J) i := by
    rw [sc_s J k, sc_s J i] at h1
    by_contra hn
    have hn := not_le.mp hn
    have : (Nsc J : ℤ) * (s (I := J) k - s (I := J) i) ≥ Nsc J := by
      have : s (I := J) k - s (I := J) i ≥ 1 := by omega
      nlinarith [(by positivity : (0 : ℤ) ≤ Nsc J)]
    have hi'' : ((i : ℕ) : ℤ) < Nsc J := by rw [hN]; exact_mod_cast Nat.lt_succ_of_lt hi'
    have hk'' : (0 : ℤ) ≤ ((k : ℕ) : ℤ) := by positivity
    nlinarith
  refine ⟨hski, ?_⟩
  by_contra hn
  have hn := not_lt.mp hn
  -- `d k ≤ s i`
  have hik : (i : ℕ) < k := by
    by_contra hc
    have hc := not_lt.mp hc
    rw [sc_s J i, sc_d J k] at h2
    push_cast at h2
    have : (Nsc J : ℤ) * (s (I := J) i - J.d k) ≥ 0 :=
      mul_nonneg (by positivity) (by omega)
    have hc' : ((k : ℕ) : ℤ) ≤ ((i : ℕ) : ℤ) := by exact_mod_cast hc
    nlinarith
  have hsik : s (I := J) i ≤ s (I := J) k := hE i k (by exact_mod_cast hik.le)
  have hsk : s (I := J) k = (J.d k : ℤ) - J.q k := rfl
  have := hq k
  omega

open Classical in
theorem aliveScaled_card_le (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i)
    (i : (scale J).Job) :
    (alive J (s (I := scale J) i)).card ≤
      ((Finset.univ : Finset (scale J).Job).filter fun k : (scale J).Job =>
        s (I := J) k ≤ s (I := J) i ∧ s (I := J) i < (J.d k : ℤ)).card :=
  Finset.card_le_card (aliveScaled_sub hE hq i)

theorem peakS_le_width (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) :
    peakS J ≤ widthJ J := by
  classical
  unfold peakS widthJ
  refine Finset.sup_le fun i _ => ?_
  refine le_trans (aliveScaled_card_le hE hq i) ?_
  exact Finset.le_sup (f := fun i : (scale J).Job =>
    ((Finset.univ : Finset (scale J).Job).filter fun k : (scale J).Job =>
      s (I := J) k ≤ s (I := J) i ∧ s (I := J) i < (J.d k : ℤ)).card) (Finset.mem_univ i)

theorem exists_before_all (J : Instance) : ∃ t₀ : ℤ, ∀ k : (scale J).Job, t₀ < s (I := scale J) k := by
  refine ⟨-(∑ k : (scale J).Job, (((scale J).q k : ℕ) : ℤ)) - 1, fun k => ?_⟩
  have h := Finset.single_le_sum (f := fun k : (scale J).Job => (((scale J).q k : ℕ) : ℤ))
    (fun k _ => Int.natCast_nonneg _) (Finset.mem_univ k)
  have hs : s (I := scale J) k = ((scale J).d k : ℤ) - (scale J).q k := rfl
  have := Int.natCast_nonneg ((scale J).d k)
  omega

/-- **The sweep, in full.** After all events the invariant holds at some time past every event,
with the peak width. -/
theorem final_inv (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) {INF : ℕ}
    (hINF : ∀ j : J.Job, J.d j ≤ INF) (hpos : 0 < INF) (W : ℕ) :
    ∃ t'', Inv J INF W (peakS J) (evs J) (tab J INF (evs J)) t'' ∧
      ∀ f ∈ evs J, evTime J f ≤ t'' := by
  obtain ⟨t₀, ht⟩ := exists_before_all J
  have hbase : Inv J INF W (peakS J) [] (St.init J INF) t₀ := by
    have hal := alive_of_lt_all (J := J) ht
    refine ⟨base_rel W INF hpos ht, ?_, ?_, ?_, List.nodup_nil, Nat.zero_le _, ?_⟩
    · intro i hi
      rw [hal] at hi; simp at hi
    · show (alive J t₀).image (St.init J INF).sl ∪ ([] : List ℕ).toFinset = Finset.range 0
      rw [hal]; simp
    · show Disjoint ((alive J t₀).image (St.init J INF).sl) ([] : List ℕ).toFinset
      simp
    · intro k hk; simp at hk
  have := run_inv hq hINF (fun i => le_peakS i) (evs J) (evs_pairwise J hE hq) (mem_evs J)
    (evs J) [] (St.init J INF) t₀ (by simp) hbase (by simp) (by
      intro f hf
      cases f with
      | start k => exact ht k
      | due k =>
        have := ht k
        have := sc_s_lt hq k
        show t₀ < ((scale J).d k : ℤ)
        omega)
  exact this

/-- **Correctness of the sweep**, for every weight: the table's `(0, W)` entry is finite exactly
when some feasible set weighs at least `W`. -/
theorem sweep_correct (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) {INF : ℕ}
    (hINF : ∀ j : J.Job, J.d j ≤ INF) (hpos : 0 < INF) (W : ℕ) :
    (tab J INF (evs J)).T 0 W < INF ↔ HasWeight J W := by
  obtain ⟨t'', hI, hall⟩ := final_inv hE hq hINF hpos W
  exact readoff hE hq hI.rel fun k => hall (Ev.due k) (mem_evs J _)

/-- The number of slots ever used is at most the width. -/
theorem sweep_next_le (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) {INF : ℕ}
    (hINF : ∀ j : J.Job, J.d j ≤ INF) (hpos : 0 < INF) :
    (tab J INF (evs J)).next ≤ widthJ J := by
  obtain ⟨t'', hI, -⟩ := final_inv hE hq hINF hpos 0
  exact hI.peak.trans (peakS_le_width hE hq)

/-! ## The concrete `INF` -/

/-- The largest due date. -/
def maxd (J : Instance) : ℕ := ((List.finRange J.jobs).map J.d).foldr max 0

theorem le_foldr_max : ∀ (l : List ℕ) (x : ℕ), x ∈ l → x ≤ l.foldr max 0
  | [], x, h => by simp at h
  | a :: l, x, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max l x h) (le_max_right _ _)

theorem d_le_maxd (j : Fin J.jobs) : J.d j ≤ maxd J :=
  le_foldr_max _ _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)

/-- The table's infinity: the largest due date plus two. -/
def infOf (J : Instance) : ℕ := maxd J + 2

theorem sweep_correct_maxd (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) (W : ℕ) :
    (tab J (infOf J) (evs J)).T 0 W < infOf J ↔ HasWeight J W :=
  sweep_correct hE hq (fun j => le_trans (d_le_maxd j) (by unfold infOf; omega))
    (by unfold infOf; omega) W

end Lax496464Proofs.Ram.W3Model
