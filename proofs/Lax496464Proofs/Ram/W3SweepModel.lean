import Lax496464Proofs.Ram.W3Model
import Lax496464Proofs.Ram.Dp1

/-!
# The sweep loop, model side: which event comes next, and what the state satisfies

The machine's loop keeps two counters `i` (starts done) and `k` (dues done); the events done
so far are the list `pre`.  `Pos J i k pre` says that `pre` is what the merge of `W3Model.evs`
has produced after `i` starts and `k` dues, where the choice between the two is the natural-number
test `spOf` the machine performs on its arrays.  Everything the machine needs of the model is a
consequence: the events not yet done are `mergeBy … (drop i) (drop k)` (`pos_evs`), a due event's
job has been started (`due_started`), and the state `tab J INF pre` satisfies `Good`
(`pos_good`).
-/

namespace Lax496464Proofs.Ram.W3SweepModel

open Lax496464.FlowShop Lax496464.EstOrder Lax496464.Sweep
open Lax496464.FlowShop.Instance (s HasWeight)
open Lax496464Proofs.Ram.W3Bits Lax496464Proofs.Ram.W3Tab Lax496464Proofs.Ram.W3Rel
open Lax496464Proofs.Ram.W3Model
open Lax496464Proofs.Ram.Dp1 (pv qv dv)

variable {J : Instance}

/-- `SA[k]`: the `k`-th job in due order, as a number. -/
def dueAt (J : Instance) (k : ℕ) : ℕ := ((dueOrder J).map Fin.val).getD k 0

@[simp] theorem scale_jobs_eq (J : Instance) : (scale J).jobs = J.jobs := rfl

theorem length_dueOrder (J : Instance) : (dueOrder J).length = J.jobs := by
  rw [(dueOrder_perm J).length_eq, List.length_finRange]; rfl

theorem dueAt_eq (k : ℕ) (hk : k < (dueOrder J).length) : dueAt J k = ((dueOrder J)[k]).val := by
  unfold dueAt
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map]

theorem dv_eq (j : Fin J.jobs) : dv J j.val = J.d j := by simp [dv]
theorem qv_eq (j : Fin J.jobs) : qv J j.val = J.q j := by simp [qv]

/-- The machine's test: the next event is the start of job `i`. -/
def spOf (J : Instance) (i k : ℕ) : Prop :=
  i < J.jobs ∧ (J.jobs ≤ k ∨ dv J i < dv J (dueAt J k) + qv J i ∨
    (dv J i = dv J (dueAt J k) + qv J i ∧ i < dueAt J k))

/-- The events done after `i` starts and `k` dues. -/
inductive Pos (J : Instance) : ℕ → ℕ → List (Ev J) → Prop
  | zero : Pos J 0 0 []
  | start {i k : ℕ} {pre : List (Ev J)} (h : Pos J i k pre) (hs : spOf J i k)
      (hi : i < (scale J).jobs) : Pos J (i + 1) k (pre ++ [Ev.start ⟨i, hi⟩])
  | due {i k : ℕ} {pre : List (Ev J)} (h : Pos J i k pre) (hs : ¬ spOf J i k)
      (hk : k < (dueOrder J).length) : Pos J i (k + 1) (pre ++ [Ev.due ((dueOrder J)[k])])

/-- The events still to come. -/
def rest (J : Instance) (i k : ℕ) : List (Ev J) :=
  mergeBy (startFirst J) Ev.start Ev.due ((List.finRange (scale J).jobs).drop i)
    ((dueOrder J).drop k)

section merge

variable {α β γ : Type} (f : α → β → Bool) (l : α → γ) (r : β → γ)

theorem mergeBy_nil_right : ∀ xs : List α, mergeBy f l r xs [] = xs.map l
  | [] => by simp [mergeBy]
  | x :: xs => by simp [mergeBy]

theorem mergeBy_nil_left (ys : List β) : mergeBy f l r [] ys = ys.map r := by
  simp [mergeBy]

theorem mergeBy_true {x : α} {y : β} {xs : List α} {ys : List β} (h : f x y = true) :
    mergeBy f l r (x :: xs) (y :: ys) = l x :: mergeBy f l r xs (y :: ys) := by
  simp [mergeBy, h]

theorem mergeBy_false {x : α} {y : β} {xs : List α} {ys : List β} (h : f x y = false) :
    mergeBy f l r (x :: xs) (y :: ys) = r y :: mergeBy f l r (x :: xs) ys := by
  simp [mergeBy, h]

end merge

theorem startFirst_eq (i k : ℕ) (hi : i < J.jobs) (hk : k < (dueOrder J).length) :
    startFirst J ⟨i, hi⟩ ((dueOrder J)[k]) = true ↔
      (dv J i < dv J (dueAt J k) + qv J i ∨
        (dv J i = dv J (dueAt J k) + qv J i ∧ i < dueAt J k)) := by
  rw [dueAt_eq k hk]
  have h1 : dv J i = J.d ⟨i, hi⟩ := dv_eq ⟨i, hi⟩
  have h2 : qv J i = J.q ⟨i, hi⟩ := qv_eq ⟨i, hi⟩
  have h3 : dv J ((dueOrder J)[k]).val = J.d ((dueOrder J)[k]) := dv_eq _
  rw [h1, h2, h3]
  unfold startFirst
  simp only [decide_eq_true_eq]
  rfl

theorem rest_start {i k : ℕ} (hs : spOf J i k) (hi : i < (scale J).jobs) :
    rest J i k = Ev.start ⟨i, hi⟩ :: rest J (i + 1) k := by
  have hn : (scale J).jobs = J.jobs := rfl
  have hx : (List.finRange (scale J).jobs).drop i =
      ⟨i, hi⟩ :: (List.finRange (scale J).jobs).drop (i + 1) := by
    rw [List.drop_eq_getElem_cons (by simpa using hi)]; simp
  unfold rest
  rw [hx]
  by_cases hk : J.jobs ≤ k
  · have : (dueOrder J).drop k = [] := List.drop_of_length_le (by rw [length_dueOrder]; exact hk)
    rw [this, mergeBy_nil_right, mergeBy_nil_right]
    simp only [List.map_cons]
  · have hk' : k < (dueOrder J).length := by rw [length_dueOrder]; omega
    rw [List.drop_eq_getElem_cons hk']
    rw [mergeBy_true]
    have := (startFirst_eq i k (by simpa using hi) hk').mpr (by
      rcases hs with ⟨_, h | h⟩
      · exact absurd h hk
      · exact h)
    exact this

theorem rest_due {i k : ℕ} (hs : ¬ spOf J i k) (hk : k < (dueOrder J).length) :
    rest J i k = Ev.due ((dueOrder J)[k]) :: rest J i (k + 1) := by
  unfold rest
  rw [List.drop_eq_getElem_cons hk]
  by_cases hi : J.jobs ≤ i
  · have : (List.finRange (scale J).jobs).drop i = [] :=
      List.drop_of_length_le (by simpa using hi)
    rw [this, mergeBy_nil_left, mergeBy_nil_left]
    simp only [List.map_cons]
  · have hi' : i < (scale J).jobs := by simpa using (by omega : i < J.jobs)
    have hx : (List.finRange (scale J).jobs).drop i =
        ⟨i, hi'⟩ :: (List.finRange (scale J).jobs).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi')]; simp
    rw [hx]
    have hf : startFirst J ⟨i, hi'⟩ ((dueOrder J)[k]) = false := by
      by_contra hne
      have hne' : startFirst J ⟨i, hi'⟩ ((dueOrder J)[k]) = true := by simpa using hne
      have := (startFirst_eq i k (by simpa using hi') hk).mp hne'
      exact hs ⟨by omega, Or.inr this⟩
    rw [mergeBy_false _ _ _ hf]

/-- **The decomposition**: what the loop has done, and what it has still to do. -/
theorem pos_evs {i k : ℕ} {pre : List (Ev J)} (h : Pos J i k pre) :
    evs J = pre ++ rest J i k ∧ i ≤ J.jobs ∧ k ≤ J.jobs := by
  induction h with
  | zero => exact ⟨by unfold evs rest; rfl, by omega, by omega⟩
  | start h hs hi ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, h3⟩
    · rw [h1, rest_start hs hi]; simp
    · exact hi
  | due h hs hk ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, h2, ?_⟩
    · rw [h1, rest_due hs hk]; simp
    · rw [length_dueOrder] at hk; omega

theorem pos_final {i k : ℕ} {pre : List (Ev J)} (h : Pos J i k pre) (hik : i + k = 2 * J.jobs) :
    pre = evs J := by
  obtain ⟨h1, h2, h3⟩ := pos_evs h
  have hi : i = J.jobs := by omega
  have hk : k = J.jobs := by omega
  have hn : (scale J).jobs = J.jobs := rfl
  have : rest J i k = [] := by
    unfold rest
    rw [List.drop_of_length_le (by rw [List.length_finRange]; omega),
      List.drop_of_length_le
      (by rw [length_dueOrder]; omega)]
    simp [mergeBy]
  rw [h1, this]; simp

/-! ## The table's state -/

theorem tab_append (INF : ℕ) (l : List (Ev J)) (e : Ev J) :
    tab J INF (l ++ [e]) = step J INF (tab J INF l) e := by
  simp [tab, List.foldl_append]

theorem step_start_nil (INF : ℕ) (S : St J) (y : (scale J).Job) (hf : S.free = []) :
    step J INF S (Ev.start y) = (St.mk [] (S.next + 1) (Function.update S.sl y S.next)
      (startT S.next (J.w y) (J.p y) (J.q y) (J.d y) J.machines INF S.T) : St J) := by
  simp [step, hf]

theorem step_start_cons (INF : ℕ) (S : St J) (y : (scale J).Job) (b : ℕ) (r : List ℕ)
    (hf : S.free = b :: r) :
    step J INF S (Ev.start y) = (St.mk r S.next (Function.update S.sl y b)
      (startT b (J.w y) (J.p y) (J.q y) (J.d y) J.machines INF S.T) : St J) := by
  simp [step, hf]

theorem step_due (INF : ℕ) (S : St J) (y : (scale J).Job) :
    step J INF S (Ev.due y) = (St.mk (S.sl y :: S.free) S.next S.sl
      (dueT (S.sl y) INF S.T) : St J) := rfl

theorem step_next_ge (INF : ℕ) (S : St J) (e : Ev J) : S.next ≤ (step J INF S e).next := by
  cases e with
  | start j =>
    cases hf : S.free <;> simp [step, hf]
  | due j => simp [step]

theorem next_foldl_le (INF : ℕ) : ∀ (M : List (Ev J)) (S : St J),
    S.next ≤ (M.foldl (step J INF) S).next
  | [], _S => le_rfl
  | e :: M, S => le_trans (step_next_ge INF S e) (next_foldl_le INF M _)

/-- Along the run, `next` never exceeds its final value. -/
theorem pos_next_le (INF : ℕ) {i k : ℕ} {pre : List (Ev J)} (h : Pos J i k pre) :
    (tab J INF pre).next ≤ (tab J INF (evs J)).next := by
  obtain ⟨h1, -, -⟩ := pos_evs h
  rw [h1]
  unfold tab
  rw [List.foldl_append]
  exact next_foldl_le INF _ _

/-- What the machine's bookkeeping needs of the model's state. -/
structure Good (J : Instance) (S : St J) (i k : ℕ) : Prop where
  sl : ∀ j : (scale J).Job, j.val < i → S.sl j < S.next
  free : ∀ b ∈ S.free, b < S.next
  len : S.free.length ≤ k

theorem good_init {INF : ℕ} : Good J (St.init J INF) 0 0 :=
  ⟨fun j hj => absurd hj (by omega), fun b hb => by simp [St.init] at hb, by simp [St.init]⟩

theorem good_start {S : St J} {i k : ℕ} (hg : Good J S i k) (INF : ℕ) (hi : i < (scale J).jobs) :
    Good J (step J INF S (Ev.start ⟨i, hi⟩)) (i + 1) k := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hold : ∀ j : (scale J).Job, j ≠ ⟨i, hi⟩ → j.val < i + 1 → j.val < i := fun j hji hj => by
    have : j.val ≠ i := fun h => hji (Fin.ext h)
    omega
  cases hf : S.free with
  | nil =>
    rw [step_start_nil INF S _ hf]
    refine ⟨fun j hj => ?_, fun b hb => ?_, ?_⟩
    · show Function.update S.sl ⟨i, hi⟩ S.next j < S.next + 1
      by_cases hji : j = ⟨i, hi⟩
      · subst hji; rw [Function.update_self]; omega
      · rw [Function.update_of_ne hji]
        have := h1 j (hold j hji hj)
        omega
    · simp at hb
    · simp
  | cons b r =>
    have hbn : b < S.next := h2 b (by simp [hf])
    rw [step_start_cons INF S _ b r hf]
    refine ⟨fun j hj => ?_, fun b' hb' => ?_, ?_⟩
    · show Function.update S.sl ⟨i, hi⟩ b j < S.next
      by_cases hji : j = ⟨i, hi⟩
      · subst hji; rw [Function.update_self]; exact hbn
      · rw [Function.update_of_ne hji]
        exact h1 j (hold j hji hj)
    · exact h2 b' (by simp [hf, hb'])
    · simp [hf] at h3; show r.length ≤ k; omega

theorem good_due {S : St J} {i k : ℕ} (hg : Good J S i k) (INF : ℕ) (y : (scale J).Job)
    (hy : y.val < i) : Good J (step J INF S (Ev.due y)) i (k + 1) := by
  obtain ⟨h1, h2, h3⟩ := hg
  rw [step_due]
  refine ⟨fun j hj => h1 j hj, fun b hb => ?_, ?_⟩
  · simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact h1 y hy
    · exact h2 b hb
  · show (S.sl y :: S.free).length ≤ k + 1
    simp; omega

/-! ## A due event's job has been started -/

theorem sc_s_lt_of_lt (hE : EstOrdered J) (a b : (scale J).Job) (hab : a < b) :
    s (I := scale J) a < s (I := scale J) b := by
  rw [sc_s J a, sc_s J b]
  have h1 : s (I := J) a ≤ s (I := J) b := hE a b hab.le
  have h2 : (Nsc J : ℤ) * s (I := J) a ≤ (Nsc J : ℤ) * s (I := J) b :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
  linarith

theorem due_started (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) {i k : ℕ}
    (hi : i ≤ J.jobs) (hs : ¬ spOf J i k) (hk : k < (dueOrder J).length) :
    ((dueOrder J)[k]).val < i := by
  set y := (dueOrder J)[k] with hy
  by_cases hin : J.jobs ≤ i
  · have := y.isLt
    have hn : (scale J).jobs = J.jobs := rfl
    omega
  · have hi' : i < (scale J).jobs := by simpa using (by omega : i < J.jobs)
    have hf : startFirst J ⟨i, hi'⟩ y = false := by
      by_contra hne
      have hne' : startFirst J ⟨i, hi'⟩ y = true := by simpa using hne
      have := (startFirst_eq i k (by simpa using hi') hk).mp hne'
      exact hs ⟨by omega, Or.inr this⟩
    by_contra hcon
    have hle : (⟨i, hi'⟩ : (scale J).Job) ≤ y := by
      show i ≤ y.val
      omega
    have h1 : s (I := scale J) ⟨i, hi'⟩ ≤ s (I := scale J) y := by
      rcases hle.lt_or_eq with hlt | heq
      · exact (sc_s_lt_of_lt hE _ _ hlt).le
      · rw [heq]
    have h2 := sc_s_lt hq y
    have h3 : ¬ (startFirst J ⟨i, hi'⟩ y = true) := by
      intro h; rw [hf] at h; exact absurd h (by simp)
    rw [startFirst_iff] at h3
    omega

/-- **The state along the run satisfies `Good`.** -/
theorem pos_good (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) (INF : ℕ) {i k : ℕ}
    {pre : List (Ev J)} (h : Pos J i k pre) : Good J (tab J INF pre) i k := by
  induction h with
  | zero => exact good_init
  | start h hs hi ih =>
    rw [tab_append]; exact good_start ih INF hi
  | due h hs hk ih =>
    rw [tab_append]
    exact good_due ih INF _ (due_started hE hq (pos_evs h).2.1 hs hk)

end Lax496464Proofs.Ram.W3SweepModel
