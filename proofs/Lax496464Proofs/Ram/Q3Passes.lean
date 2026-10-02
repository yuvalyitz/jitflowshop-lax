import Lax496464Proofs.Ram.Imp
import Lax496464Proofs.Ram.ListUtil
import Lax496464Proofs.Ram.Q3Defs

/-!
# Q3: the Three Flat Passes of One Sweep Event, as IMP+ Commands

Each command is one flat loop `i := 0; while i < N do ..` over the `N = bt * w1` cells.  Scalars
and arrays follow the shared naming convention of `Q3Defs` (live scalars are only read; every
temporary comes from the pool `"i" "u1" .. "u6"`).

* `fillCom a` (`fillCom_spec`): every cell of the array `a` becomes `cinf`.
  Scalars mentioned: `"i" "N" "cinf"`.  Arrays: `a` (write).  Cost `14 * N + 6`.
* `margCom` (`margCom_spec`): pass 1, `S[(i/w1/pwd)*w1 + i%w1] := min(S[..], T[i])` for every
  cell; the post is `MargOK`.
  Scalars mentioned: `"i" "N" "w1" "pwd" "u1" "u2" "u3" "u4" "u5" "u6"`.
  Arrays: `"T"` (read), `"S"` (read/write).  Cost `64 * (bt * w1) + 6`.
* `takeCom` (`takeCom_spec`): pass 2, the `TakeOK` update of `T` from `S` and the digit sums `G`.
  Scalars mentioned: `"i" "N" "w1" "bb" "m" "pwq" "pj" "qj" "dj" "wj" "u1" "u2" "u3" "u4" "u5" "u6"`.
  Arrays: `"G"` (read), `"S"` (read), `"T"` (write).  Cost `204 * (bt * w1) + 6`.

All numeric side conditions are of the form "quantity (plus a small constant) `< B`".
-/

namespace Lax496464Proofs.Ram.Q3Passes

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.Ram.ListUtil
open Lax496464Proofs.Ram.Q3Defs

abbrev V (s : String) : Expr := .var s

/-! ## Fill -/

def fillBody (a : String) : Com :=
  .seq (.store a (V "i") (V "cinf")) (.assign "i" (.bin .add (V "i") (.lit 1)))

def fillCom (a : String) : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) (fillBody a))

theorem fillBody_spec {B : ℕ} (a : String) (INF i : ℕ) (A : List ℕ) (hi : i < A.length)
    (hiB : i + 1 < B) (hINF : INF < B) :
    Spec B (fun σ => σ.vars "cinf" = INF ∧ σ.vars "i" = i ∧ σ.arrs a = A) (fillBody a)
      (fun σ σ' => σ'.arrs a = A.set i INF ∧ σ'.vars "i" = i + 1 ∧
        σ'.vars "cinf" = INF ∧ σ'.vars "N" = σ.vars "N") 10 := by
  run_vcg
  all_goals simp_all

def FillInv (a : String) (N INF : ℕ) (A0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "N" = N ∧ σ.vars "cinf" = INF ∧ σ.vars "i" ≤ N ∧ (σ.arrs a).length = A0.length ∧
  ∀ j, (σ.arrs a).getD j 0 = if j < σ.vars "i" then INF else A0.getD j 0

/-- **Fill**: every cell of `a` becomes `cinf`. -/
theorem fillCom_spec {B N INF : ℕ} (a : String) (A0 : List ℕ) (_hB : 1 < B)
    (hlen : A0.length = N) (hNB : N < B) (hINF : INF < B) :
    Spec B (fun σ => σ.vars "N" = N ∧ σ.vars "cinf" = INF ∧ σ.arrs a = A0) (fillCom a)
      (fun _ σ' => σ'.arrs a = List.replicate N INF) (14 * N + 6) := by
  have hbody : Spec B (fun σ => FillInv a N INF A0 σ ∧ σ.vars "i" < N) (fillBody a)
      (fun σ σ' => FillInv a N INF A0 σ' ∧ σ'.vars "i" = σ.vars "i" + 1) 10 := by
    intro σ ⟨⟨h1, h2, h3, h4, h5⟩, hlt⟩
    obtain ⟨σ', hrun, hA, hi', hc, hN⟩ := fillBody_spec (B := B) a INF (σ.vars "i") (σ.arrs a)
      (by omega) (by omega) hINF σ ⟨h2, rfl, rfl⟩
    refine ⟨σ', hrun, ⟨?_, ?_, ?_, ?_, ?_⟩, hi'⟩
    · rw [hN]; exact h1
    · exact hc
    · rw [hi']; omega
    · rw [hA, List.length_set]; exact h4
    · intro j
      rw [hA, hi']
      by_cases hj : j = σ.vars "i"
      · subst hj
        rw [getD_set_self _ _ _ (by omega), if_pos (by omega)]
      · rw [getD_set_ne _ _ _ _ hj, h5 j]
        by_cases hjl : j < σ.vars "i"
        · rw [if_pos hjl, if_pos (by omega)]
        · rw [if_neg hjl, if_neg (by omega)]
  have hloop := Spec.forRangeZero (B := B) "i" "N" (FillInv a N INF A0) N 10
    hNB (fun σ h => h.2.2.1) (fun σ h => h.1) hbody
  refine (hloop.conseq ?_ ?_ (by omega))
  · rintro σ ⟨h1, h2, h3⟩
    exact ⟨by simpa [Env.setVar] using h1, by simpa [Env.setVar] using h2, by simp [Env.setVar],
      by simp [Env.setVar, h3], by intro j; simp [Env.setVar, h3]⟩
  · rintro σ σ' - ⟨⟨_, _, hi, hlen', hget⟩, hiN⟩
    apply List.ext_getElem
    · simp [hlen', hlen]
    · intro j h1 h2
      have := hget j
      rw [hiN] at this
      simp only [List.length_replicate] at h2
      rw [List.getD_eq_getElem _ _ h1, if_pos h2] at this
      simpa using this


/-! ## Pass 1: marginalisation -/

/-- The flat target index of source cell `i`: `(i / w1 / pwd) * w1 + i % w1`. -/
def mtgt (w1 pwd i : ℕ) : ℕ := i / w1 / pwd * w1 + (i - i / w1 * w1)

theorem mtgt_eq (w1 pwd i : ℕ) : mtgt w1 pwd i = i / w1 / pwd * w1 + i % w1 := by
  unfold mtgt; rw [Nat.mod_def, Nat.mul_comm w1 (i / w1)]

theorem mtgt_le {w1 pwd i : ℕ} : mtgt w1 pwd i ≤ i := by
  rw [mtgt_eq]
  have h1 : i / w1 / pwd ≤ i / w1 := Nat.div_le_self _ _
  have h2 : i / w1 / pwd * w1 ≤ i / w1 * w1 := Nat.mul_le_mul_right _ h1
  have h3 := Nat.div_add_mod i w1
  rw [Nat.mul_comm w1 (i / w1)] at h3
  omega

def margBody : Com :=
  .seq (.assign "u1" (.bin .div (V "i") (V "w1")))
    (.seq (.assign "u2" (.bin .sub (V "i") (.bin .mul (V "u1") (V "w1"))))
      (.seq (.assign "u3" (.bin .div (V "u1") (V "pwd")))
        (.seq (.assign "u4" (.bin .add (.bin .mul (V "u3") (V "w1")) (V "u2")))
          (.seq (.assign "u5" (.get "T" (V "i")))
            (.seq (.assign "u6" (.get "S" (V "u4")))
              (.seq (.ite (.lt (V "u5") (V "u6")) (.store "S" (V "u4") (V "u5")) .skip)
                (.assign "i" (.bin .add (V "i") (.lit 1)))))))))

def margCom : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) margBody)

theorem margBody_spec {B N w1 pwd INF i : ℕ} (T S : List ℕ) (hB : 1 < B) (hw1 : 0 < w1)
    (hi : i < N) (hNB : N < B) (hw1B : w1 < B) (hpwdB : pwd < B) (hINF : INF < B)
    (hTl : N ≤ T.length) (hSl : N ≤ S.length)
    (hTle : ∀ j, T.getD j 0 ≤ INF) (hSle : ∀ j, S.getD j 0 ≤ INF) :
    Spec B (fun σ => σ.vars "N" = N ∧ σ.vars "w1" = w1 ∧ σ.vars "pwd" = pwd ∧
        σ.vars "i" = i ∧ σ.arrs "T" = T ∧ σ.arrs "S" = S) margBody
      (fun _σ σ' => σ'.arrs "S" = S.set (mtgt w1 pwd i) (min (S.getD (mtgt w1 pwd i) 0) (T.getD i 0)) ∧
        σ'.vars "i" = i + 1 ∧ σ'.vars "N" = N ∧ σ'.vars "w1" = w1 ∧ σ'.vars "pwd" = pwd ∧
        σ'.arrs "T" = T) 60 := by
  have hi1 : i / w1 ≤ i := Nat.div_le_self _ _
  have h2 : i / w1 * w1 ≤ i := Nat.div_mul_le_self i w1
  have h3 : i / w1 / pwd ≤ i / w1 := Nat.div_le_self _ _
  have h4 : i / w1 / pwd * w1 ≤ i / w1 * w1 := Nat.mul_le_mul_right _ h3
  have ht := mtgt_le (w1 := w1) (pwd := pwd) (i := i)
  have hT : T.getD i 0 ≤ INF := hTle i
  have hS : S.getD (mtgt w1 pwd i) 0 ≤ INF := hSle _
  have hTB : ∀ (h : i < T.length), T[i] < B := fun h => by
    have := hTle i; rw [List.getD_eq_getElem _ _ h] at this; omega
  have hSB : ∀ (h : mtgt w1 pwd i < S.length), S[mtgt w1 pwd i] < B := fun h => by
    have := hSle (mtgt w1 pwd i); rw [List.getD_eq_getElem _ _ h] at this; omega
  have hSi : mtgt w1 pwd i < S.length := by omega
  have hTi : i < T.length := by omega
  run_vcg
  all_goals simp_all [mtgt]
  all_goals first | omega | (rw [min_eq_right (by omega)])

theorem mtgt_div {w1 : ℕ} (pwd i : ℕ) (hw1 : 0 < w1) : mtgt w1 pwd i / w1 = i / w1 / pwd := by
  rw [mtgt_eq, Nat.add_comm, Nat.add_mul_div_right _ _ hw1, Nat.div_eq_of_lt (Nat.mod_lt _ hw1),
    Nat.zero_add]

theorem mtgt_mod {w1 : ℕ} (pwd i : ℕ) (_hw1 : 0 < w1) : mtgt w1 pwd i % w1 = i % w1 := by
  rw [mtgt_eq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]

/-- The source cell `i` feeds the target cell `k` iff `k` is `mtgt i`. -/
theorem feeds_iff {w1 : ℕ} (pwd i k : ℕ) (hw1 : 0 < w1) :
    (i / w1 / pwd = k / w1 ∧ i % w1 = k % w1) ↔ k = mtgt w1 pwd i := by
  constructor
  · rintro ⟨h1, h2⟩
    rw [mtgt_eq, h1, h2, Nat.mul_comm]
    exact (Nat.div_add_mod k w1).symm
  · rintro rfl
    exact ⟨(mtgt_div pwd i hw1).symm, (mtgt_mod pwd i hw1).symm⟩

/-- The invariant of pass 1: after the first `i` flat cells. -/
def MargInv (N w1 pwd INF : ℕ) (T S0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "N" = N ∧ σ.vars "w1" = w1 ∧ σ.vars "pwd" = pwd ∧ σ.vars "i" ≤ N ∧
  σ.arrs "T" = T ∧ (σ.arrs "S").length = S0.length ∧
  ∀ k < N, (σ.arrs "S").getD k 0 ≤ INF ∧ ∀ P,
    ((σ.arrs "S").getD k 0 ≤ P ↔ INF ≤ P ∨
      ∃ i' < σ.vars "i", i' / w1 / pwd = k / w1 ∧ i' % w1 = k % w1 ∧ T.getD i' 0 ≤ P)

theorem getD_replicate_lt {n k v : ℕ} (h : k < n) : (List.replicate n v).getD k 0 = v := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_le_of_forall {S : List ℕ} {N INF : ℕ} (hl : S.length = N)
    (h : ∀ k < N, S.getD k 0 ≤ INF) (j : ℕ) : S.getD j 0 ≤ INF := by
  by_cases hj : j < N
  · exact h j hj
  · rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _

theorem margCom_loop {B N w1 pwd INF : ℕ} (T : List ℕ) (hB : 1 < B) (hw1 : 0 < w1)
    (hNB : N < B) (hw1B : w1 < B) (hpwdB : pwd < B) (hINF : INF < B)
    (hTl : N ≤ T.length) (hTle : ∀ i, T.getD i 0 ≤ INF) :
    Spec B (fun σ => σ.vars "N" = N ∧ σ.vars "w1" = w1 ∧ σ.vars "pwd" = pwd ∧ σ.arrs "T" = T ∧
      σ.arrs "S" = List.replicate N INF) margCom
      (fun _ σ' => (σ'.arrs "S").length = N ∧
        ∀ k < N, (σ'.arrs "S").getD k 0 ≤ INF ∧ ∀ P,
          ((σ'.arrs "S").getD k 0 ≤ P ↔ INF ≤ P ∨
            ∃ i' < N, i' / w1 / pwd = k / w1 ∧ i' % w1 = k % w1 ∧ T.getD i' 0 ≤ P))
      (64 * N + 6) := by
  have hbody : Spec B (fun σ => MargInv N w1 pwd INF T (List.replicate N INF) σ ∧ σ.vars "i" < N)
      margBody (fun σ σ' => MargInv N w1 pwd INF T (List.replicate N INF) σ' ∧
        σ'.vars "i" = σ.vars "i" + 1) 60 := by
    intro σ ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hlt⟩
    simp only [List.length_replicate] at h6
    have hSle := getD_le_of_forall h6 (fun k hk => (h7 k hk).1)
    obtain ⟨σ', hrun, hS, hi', hN', hw', hp', hT'⟩ := margBody_spec (B := B) (N := N) (w1 := w1)
      (pwd := pwd) (INF := INF) (i := σ.vars "i") T (σ.arrs "S") hB hw1 hlt hNB hw1B hpwdB hINF
      hTl (by omega) hTle hSle σ ⟨h1, h2, h3, rfl, h5, rfl⟩
    have hti : mtgt w1 pwd (σ.vars "i") < N :=
      lt_of_le_of_lt mtgt_le hlt
    refine ⟨σ', hrun, ⟨hN', hw', hp', by rw [hi']; omega, hT', ?_, ?_⟩, hi'⟩
    · rw [hS, List.length_set]; simpa using h6
    · intro k hk
      rw [hS, hi']
      obtain ⟨hk1, hk2⟩ := h7 (mtgt w1 pwd (σ.vars "i")) hti
      by_cases hkt : k = mtgt w1 pwd (σ.vars "i")
      · subst hkt
        rw [getD_set_self _ _ _ (by omega)]
        refine ⟨le_trans (min_le_left _ _) hk1, fun P => ?_⟩
        rw [min_le_iff, (hk2 P)]
        constructor
        · rintro ((h | ⟨i', hi'', hc⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨i', by omega, hc⟩
          · exact Or.inr ⟨σ.vars "i", by omega,
              (feeds_iff pwd (σ.vars "i") _ hw1).mpr rfl |>.1, (feeds_iff pwd _ _ hw1).mpr rfl |>.2, h⟩
        · rintro (h | ⟨i', hi'', hc⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hii : i' = σ.vars "i"
            · subst hii; exact Or.inr hc.2.2
            · exact Or.inl (Or.inr ⟨i', by omega, hc⟩)
      · rw [getD_set_ne _ _ _ _ hkt]
        obtain ⟨hk3, hk4⟩ := h7 k hk
        refine ⟨hk3, fun P => ?_⟩
        rw [hk4 P]
        constructor
        · rintro (h | ⟨i', hi'', hc⟩)
          · exact Or.inl h
          · exact Or.inr ⟨i', by omega, hc⟩
        · rintro (h | ⟨i', hi'', hc⟩)
          · exact Or.inl h
          · by_cases hii : i' = σ.vars "i"
            · subst hii
              exact absurd ((feeds_iff pwd _ k hw1).mp ⟨hc.1, hc.2.1⟩) hkt
            · exact Or.inr ⟨i', by omega, hc⟩
  have hloop := Spec.forRangeZero (B := B) "i" "N" (MargInv N w1 pwd INF T (List.replicate N INF)) N 60
    hNB (fun σ h => h.2.2.2.1) (fun σ h => h.1) hbody
  refine (hloop.conseq ?_ ?_ (by omega))
  · rintro σ ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by simpa [Env.setVar] using h1, by simpa [Env.setVar] using h2,
      by simpa [Env.setVar] using h3, by simp [Env.setVar], by simpa [Env.setVar] using h4,
      by simp [Env.setVar, h5], ?_⟩
    intro k hk
    have e : ((σ.setVar "i" 0).arrs "S").getD k 0 = INF := by
      show (σ.arrs "S").getD k 0 = INF
      rw [h5]; exact getD_replicate_lt hk
    rw [e]
    refine ⟨le_rfl, fun P => ?_⟩
    simp [Env.setVar]
  · rintro σ σ' - ⟨⟨_, _, _, _, _, hl, hget⟩, hiN⟩
    simp only [List.length_replicate] at hl
    refine ⟨hl, fun k hk => ?_⟩
    rw [hiN] at hget
    exact hget k hk

theorem lt_flat {bt w1 b c : ℕ} (hb : b < bt) (hc : c < w1) : b * w1 + c < bt * w1 := by
  have : (b + 1) * w1 ≤ bt * w1 := Nat.mul_le_mul_right _ hb
  nlinarith

theorem flat_div {w1 b c : ℕ} (hc : c < w1) : (b * w1 + c) / w1 = b := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, Nat.zero_add]

theorem flat_mod {w1 b c : ℕ} (hc : c < w1) : (b * w1 + c) % w1 = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-- **Pass 1 (marginalisation)**, as a cell-by-cell statement.  Mentions the scalars `"N" "w1"
"pwd" "i" "u1" .. "u6"` and the arrays `"T"` (read) and `"S"` (read/write). -/
theorem margCom_spec {B bt w1 pwd INF : ℕ} (T : List ℕ) (hB : 1 < B) (hw1 : 0 < w1)
    (_hpwd : 0 < pwd) (hTl : T.length = bt * w1) (hTle : ∀ i, T.getD i 0 ≤ INF)
    (hNB : bt * w1 < B) (hw1B : w1 < B) (hpwdB : pwd < B) (hINF : INF < B) :
    Spec B (fun σ => σ.vars "N" = bt * w1 ∧ σ.vars "w1" = w1 ∧ σ.vars "pwd" = pwd ∧
        σ.arrs "T" = T ∧ σ.arrs "S" = List.replicate (bt * w1) INF) margCom
      (fun _ σ' => MargOK bt w1 pwd INF T (σ'.arrs "S") ∧ (σ'.arrs "S").length = bt * w1)
      (64 * (bt * w1) + 6) := by
  refine (margCom_loop (N := bt * w1) T hB hw1 hNB hw1B hpwdB hINF hTl.ge hTle).post ?_
  rintro σ σ' - ⟨hlen, h⟩
  refine ⟨fun b hb c hc => ?_, hlen⟩
  have hk := lt_flat hb hc
  obtain ⟨h1, h2⟩ := h _ hk
  refine ⟨h1, fun P => ?_⟩
  change (σ'.arrs "S").getD (b * w1 + c) 0 ≤ INF at h1
  change (σ'.arrs "S").getD (b * w1 + c) 0 ≤ P ↔ _
  rw [h2 P, flat_div hc, flat_mod hc]
  constructor
  · rintro (h | ⟨i', hi', hd, hm, hT⟩)
    · exact Or.inl h
    · refine Or.inr ⟨i' / w1, ?_, hd, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hw1]; exact hi'
      · change T.getD (i' / w1 * w1 + c) 0 ≤ P
        rw [← hm]
        have := Nat.div_add_mod i' w1
        rw [Nat.mul_comm w1] at this
        rwa [this]
  · rintro (h | ⟨y, hy, hd, hT⟩)
    · exact Or.inl h
    · refine Or.inr ⟨y * w1 + c, lt_flat hy hc, ?_, ?_, hT⟩
      · rw [flat_div hc]; exact hd
      · rw [flat_mod hc]

/-! ## Pass 2: take job `k` -/

theorem set_self_of_getD (T : List ℕ) (i v0 : ℕ) (h : i < T.length) (hT0 : T.getD i 0 = v0) :
    T.set i v0 = T := by
  subst hT0
  simp [List.getElem?_eq_getElem h]

/-- The guarded overwrite of cell `i` (the last four lines of `takeBody`): `u3 = v0`, `u4` the
digit, `u5` the digit sum, `u6 = v`. -/
def takeCond : Com :=
  .ite (.lt (.lit 0) (V "u4"))
    (.ite (.lt (V "u5") (.bin .add (V "m") (.lit 1)))
      (.ite (.lt (.bin .add (V "u6") (V "qj")) (.bin .add (V "dj") (.lit 1)))
        (.ite (.lt (V "u6") (V "u3")) (.store "T" (V "i") (V "u6")) .skip)
        .skip)
      .skip)
    .skip

theorem takeCond_spec {B m qj dj i dg g v v0 : ℕ} (T : List ℕ) (hiT : i < T.length)
    (hT0 : T.getD i 0 = v0) (hmB : m + 1 < B) (hdB : dj + 1 < B) (hvB : v + qj < B)
    (hqB : qj < B) (hvB' : v < B) (hgB : g < B) (hdgB : dg < B) (hv0B : v0 < B) (hiB : i < B) :
    Spec B (fun σ => σ.vars "u3" = v0 ∧ σ.vars "u4" = dg ∧ σ.vars "u5" = g ∧ σ.vars "u6" = v ∧
        σ.vars "i" = i ∧ σ.vars "m" = m ∧ σ.vars "qj" = qj ∧ σ.vars "dj" = dj ∧
        σ.arrs "T" = T) takeCond
      (fun _ σ' => σ'.arrs "T" =
        T.set i (if 0 < dg ∧ g ≤ m ∧ v + qj ≤ dj ∧ v < v0 then v else v0) ∧
        σ'.vars "i" = i) 60 := by
  run_vcg
  all_goals simp_all
  all_goals first | omega | ((try rw [if_neg (by omega)]); exact (set_self_of_getD T i v0 hiT (by simp_all)).symm)

def takeP1 : Com :=
  .seq (.assign "u1" (.bin .div (V "i") (V "w1")))
    (.seq (.assign "u2" (.bin .sub (V "i") (.bin .mul (V "u1") (V "w1"))))
      (.assign "u3" (.get "S" (V "i"))))

def takeP2 : Com :=
  .seq (.assign "u4" (.bin .div (V "u1") (V "pwq")))
    (.seq (.assign "u4" (.bin .sub (V "u4") (.bin .mul (.bin .div (V "u4") (V "bb")) (V "bb"))))
      (.assign "u5" (.get "G" (V "u1"))))

def takeP3 : Com :=
  .seq (.assign "u6" (.bin .sub (V "u1") (V "pwq")))
    (.seq (.assign "u2" (.bin .sub (V "u2") (V "wj")))
      (.seq (.assign "u6" (.bin .add (.bin .mul (V "u6") (V "w1")) (V "u2")))
        (.assign "u6" (.bin .add (.get "S" (V "u6")) (V "pj")))))

theorem takeP1_spec {B w1 i : ℕ} (S : List ℕ) (hw1 : 0 < w1) (hw1B : w1 < B) (hiS : i < S.length)
    (hiB : i < B) (hSB : ∀ (h : i < S.length), S[i] < B) :
    Spec B (fun σ => σ.vars "w1" = w1 ∧ σ.vars "i" = i ∧ σ.arrs "S" = S) takeP1
      (fun σ σ' => σ'.vars "u1" = i / w1 ∧ σ'.vars "u2" = i - i / w1 * w1 ∧
        σ'.vars "u3" = S.getD i 0 ∧
        (∀ y, y ≠ "u1" → y ≠ "u2" → y ≠ "u3" → σ'.vars y = σ.vars y) ∧
        (∀ a, σ'.arrs a = σ.arrs a)) 30 := by
  have hxi : i / w1 ≤ i := Nat.div_le_self _ _
  have hxw : i / w1 * w1 ≤ i := Nat.div_mul_le_self i w1
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem takeP2_spec {B bb pwq x : ℕ} (G : List ℕ) (hx : x < G.length) (hxB : x < B)
    (hpwqB : pwq < B) (hbbB : bb < B)
    (hGB : ∀ (h : x < G.length), G[x] < B) :
    Spec B (fun σ => σ.vars "bb" = bb ∧ σ.vars "pwq" = pwq ∧ σ.vars "u1" = x ∧
        σ.arrs "G" = G) takeP2
      (fun σ σ' => σ'.vars "u4" = x / pwq - x / pwq / bb * bb ∧ σ'.vars "u5" = G.getD x 0 ∧
        (∀ y, y ≠ "u4" → y ≠ "u5" → σ'.vars y = σ.vars y) ∧
        (∀ a, σ'.arrs a = σ.arrs a)) 40 := by
  have hq1 : x / pwq ≤ x := Nat.div_le_self _ _
  have hq2 : x / pwq / bb * bb ≤ x / pwq := Nat.div_mul_le_self _ _
  have hq3 : x / pwq / bb ≤ x / pwq := Nat.div_le_self _ _
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

theorem takeP3_spec {B w1 pwq wj pj x c : ℕ} (S : List ℕ)
    (hidx : (x - pwq) * w1 + (c - wj) < S.length) (hxB0 : x < B) (hcB0 : c < B)
    (hw1B : w1 < B) (hpwqB : pwq < B) (hwjB : wj < B) (hpjB : pj < B) (_hxB : x - pwq < B) (_hcB : c - wj < B)
    (hmB : (x - pwq) * w1 < B) (hiB : (x - pwq) * w1 + (c - wj) < B)
    (hvB : S.getD ((x - pwq) * w1 + (c - wj)) 0 + pj < B) :
    Spec B (fun σ => σ.vars "w1" = w1 ∧ σ.vars "pwq" = pwq ∧ σ.vars "wj" = wj ∧
        σ.vars "pj" = pj ∧ σ.vars "u1" = x ∧ σ.vars "u2" = c ∧ σ.arrs "S" = S) takeP3
      (fun σ σ' => σ'.vars "u6" = S.getD ((x - pwq) * w1 + (c - wj)) 0 + pj ∧
        σ'.vars "u2" = c - wj ∧
        (∀ y, y ≠ "u2" → y ≠ "u6" → σ'.vars y = σ.vars y) ∧
        (∀ a, σ'.arrs a = σ.arrs a)) 60 := by
  run_vcg
  all_goals simp_all [Env.setVar]
  all_goals omega

/-- One cell of pass 2. -/
def takeBody : Com :=
  .seq takeP1 (.seq takeP2 (.seq takeP3 (.seq (.store "T" (V "i") (V "u3"))
    (.seq takeCond (.assign "i" (.bin .add (V "i") (.lit 1)))))))

def takeCom : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (V "i") (V "N")) takeBody)

/-- The source index of the `take` read for cell `i`. -/
def tsrc (w1 pwq wj i : ℕ) : ℕ := (i / w1 - pwq) * w1 + (i - i / w1 * w1 - wj)

/-- The value pass 2 leaves in cell `i`. -/
def takeStep (w1 bb m pwq pj qj dj wj : ℕ) (G S : List ℕ) (i : ℕ) : ℕ :=
  if 0 < i / w1 / pwq % bb ∧ G.getD (i / w1) 0 ≤ m ∧ S.getD (tsrc w1 pwq wj i) 0 + pj + qj ≤ dj ∧
      S.getD (tsrc w1 pwq wj i) 0 + pj < S.getD i 0
  then S.getD (tsrc w1 pwq wj i) 0 + pj else S.getD i 0

theorem tsrc_le (w1 pwq wj i : ℕ) : tsrc w1 pwq wj i ≤ i := by
  unfold tsrc
  have h1 : i / w1 - pwq ≤ i / w1 := Nat.sub_le _ _
  have h2 : (i / w1 - pwq) * w1 ≤ i / w1 * w1 := Nat.mul_le_mul_right _ h1
  have h3 : i / w1 * w1 ≤ i := Nat.div_mul_le_self i w1
  omega

theorem mod_eq_sub (a b : ℕ) : a % b = a - a / b * b := by
  rw [Nat.mod_def, Nat.mul_comm]


theorem takeBody_spec {B N w1 bb m pwq pj qj dj wj INF i : ℕ} (G S T : List ℕ) (hB : 1 < B)
    (hw1 : 0 < w1) (hi : i < N) (hNB : N < B) (hw1B : w1 < B) (hbbB : bb < B) (hmB : m + 1 < B)
    (hpwqB : pwq < B) (hpjB : pj < B) (hdjB : dj + 1 < B) (hwjB : wj < B) (hqjB : qj < B)
    (hINF : INF + pj + qj < B) (hGl : N ≤ G.length * w1) (hGB : ∀ x, G.getD x 0 < B)
    (hSl : N ≤ S.length) (hTl : N ≤ T.length) (hSle : ∀ j, S.getD j 0 ≤ INF) :
    Spec B (fun σ => σ.vars "N" = N ∧ σ.vars "w1" = w1 ∧ σ.vars "bb" = bb ∧ σ.vars "m" = m ∧
        σ.vars "pwq" = pwq ∧ σ.vars "pj" = pj ∧ σ.vars "qj" = qj ∧ σ.vars "dj" = dj ∧
        σ.vars "wj" = wj ∧ σ.vars "i" = i ∧
        σ.arrs "G" = G ∧ σ.arrs "S" = S ∧ σ.arrs "T" = T) takeBody
      (fun _ σ' => σ'.arrs "T" = T.set i (takeStep w1 bb m pwq pj qj dj wj G S i) ∧
        σ'.vars "i" = i + 1) 200 := by
  have hx : i / w1 < G.length := by
    have : i < G.length * w1 := by omega
    rw [Nat.div_lt_iff_lt_mul hw1]; omega
  have hxi : i / w1 ≤ i := Nat.div_le_self _ _
  have hxw : i / w1 * w1 ≤ i := Nat.div_mul_le_self i w1
  have hq1 : i / w1 / pwq ≤ i / w1 := Nat.div_le_self _ _
  have hq2 : i / w1 / pwq / bb * bb ≤ i / w1 / pwq := Nat.div_mul_le_self _ _
  have hts := tsrc_le w1 pwq wj i
  have hSi : i < S.length := by omega
  have hSt : tsrc w1 pwq wj i < S.length := by omega
  have hStB : S.getD (tsrc w1 pwq wj i) 0 ≤ INF := hSle _
  have hSiB : S.getD i 0 ≤ INF := hSle i
  have hts' : (i / w1 - pwq) * w1 + (i - i / w1 * w1 - wj) ≤ i := hts
  have hSt' : (i / w1 - pwq) * w1 + (i - i / w1 * w1 - wj) < S.length := hSt
  have hStB' : S.getD ((i / w1 - pwq) * w1 + (i - i / w1 * w1 - wj)) 0 ≤ INF := hStB
  have hSB : ∀ (h : i < S.length), S[i] < B := fun h => by
    have := hSle i; rw [List.getD_eq_getElem _ _ h] at this; omega
  have hGB' : ∀ (h : i / w1 < G.length), G[i / w1] < B := fun h => by
    have := hGB (i / w1); rwa [List.getD_eq_getElem _ _ h] at this
  have h5 : (i / w1 - pwq) * w1 ≤ i / w1 * w1 := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hp1 := takeP1_spec (B := B) (w1 := w1) (i := i) S hw1 hw1B hSi (by omega) hSB
  have hp2 := takeP2_spec (B := B) (bb := bb) (pwq := pwq) (x := i / w1) G hx (by omega) hpwqB hbbB hGB'
  have hp3 := takeP3_spec (B := B) (w1 := w1) (pwq := pwq) (wj := wj) (pj := pj) (x := i / w1)
    (c := i - i / w1 * w1) S hSt' (by omega) (by omega) hw1B hpwqB
    hwjB hpjB (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have hcond := takeCond_spec (B := B) (m := m) (qj := qj) (dj := dj) (i := i)
    (dg := i / w1 / pwq - i / w1 / pwq / bb * bb) (g := G.getD (i / w1) 0)
    (v := S.getD (tsrc w1 pwq wj i) 0 + pj)
    (v0 := S.getD i 0) (T.set i (S.getD i 0)) (by rw [List.length_set]; omega) (by
      rw [getD_set_self T i (S.getD i 0) (by omega)]) hmB hdjB (by omega) (by omega) (by omega)
      (hGB _) (by omega) (by omega) (by omega)
  run_vcg [hp1, hp2, hp3, hcond]
  all_goals clear hp1 hp2 hp3 hcond
  all_goals simp_all [Env.setVar]
  all_goals first
    | omega
    | rfl
    | (congr 1
       unfold takeStep
       have hmod : 0 < i / w1 / pwq % bb ↔ i / w1 / pwq / bb * bb < i / w1 / pwq := by
         rw [mod_eq_sub]; omega
       simp only [hmod, List.getD_eq_getElem _ _ hSt, List.getD_eq_getElem _ _ hSi,
         List.getD_eq_getElem _ _ hx]
       try rfl)

/-- The invariant of pass 2: the cells below `i` are new, the others old. -/
def TakeInv (N w1 bb m pwq pj qj dj wj : ℕ) (G S T0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "N" = N ∧ σ.vars "w1" = w1 ∧ σ.vars "bb" = bb ∧ σ.vars "m" = m ∧
  σ.vars "pwq" = pwq ∧ σ.vars "pj" = pj ∧ σ.vars "qj" = qj ∧ σ.vars "dj" = dj ∧
  σ.vars "wj" = wj ∧ σ.vars "i" ≤ N ∧ σ.arrs "G" = G ∧ σ.arrs "S" = S ∧
  (σ.arrs "T").length = T0.length ∧
  ∀ j, (σ.arrs "T").getD j 0 =
    if j < σ.vars "i" then takeStep w1 bb m pwq pj qj dj wj G S j else T0.getD j 0

theorem takeCom_loop {B N w1 bb m pwq pj qj dj wj INF : ℕ} (G S T0 : List ℕ) (hB : 1 < B)
    (hw1 : 0 < w1) (hNB : N < B) (hw1B : w1 < B) (hbbB : bb < B) (hmB : m + 1 < B)
    (hpwqB : pwq < B) (hpjB : pj < B) (hdjB : dj + 1 < B) (hwjB : wj < B) (hqjB : qj < B)
    (hINF : INF + pj + qj < B) (hGl : N ≤ G.length * w1) (hGB : ∀ x, G.getD x 0 < B)
    (hSl : N ≤ S.length) (hTl : N ≤ T0.length) (hSle : ∀ j, S.getD j 0 ≤ INF) :
    Spec B (fun σ => σ.vars "N" = N ∧ σ.vars "w1" = w1 ∧ σ.vars "bb" = bb ∧ σ.vars "m" = m ∧
        σ.vars "pwq" = pwq ∧ σ.vars "pj" = pj ∧ σ.vars "qj" = qj ∧ σ.vars "dj" = dj ∧
        σ.vars "wj" = wj ∧ σ.arrs "G" = G ∧ σ.arrs "S" = S ∧ σ.arrs "T" = T0) takeCom
      (fun _ σ' => (σ'.arrs "T").length = T0.length ∧
        ∀ j, (σ'.arrs "T").getD j 0 =
          if j < N then takeStep w1 bb m pwq pj qj dj wj G S j else T0.getD j 0)
      (204 * N + 6) := by
  have hbody : Spec B (fun σ => TakeInv N w1 bb m pwq pj qj dj wj G S T0 σ ∧ σ.vars "i" < N)
      takeBody (fun σ σ' => TakeInv N w1 bb m pwq pj qj dj wj G S T0 σ' ∧
        σ'.vars "i" = σ.vars "i" + 1) 200 := by
    intro σ ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩, hlt⟩
    obtain ⟨σ', hrun, ⟨hT, hi'⟩, hfv, hfa, -, -⟩ := (takeBody_spec (B := B) (N := N) (w1 := w1) (bb := bb) (m := m)
      (pwq := pwq) (pj := pj) (qj := qj) (dj := dj) (wj := wj) (INF := INF) (i := σ.vars "i")
      G S (σ.arrs "T") hB hw1 hlt hNB hw1B hbbB hmB hpwqB hpjB hdjB hwjB hqjB hINF hGl hGB hSl
      (by omega) hSle).frame σ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl, h11, h12, rfl⟩
    have hi0 : σ.vars "i" < (σ.arrs "T").length := by omega
    refine ⟨σ', hrun, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hi'⟩
    · rw [hfv "N" (by decide)]; exact h1
    · rw [hfv "w1" (by decide)]; exact h2
    · rw [hfv "bb" (by decide)]; exact h3
    · rw [hfv "m" (by decide)]; exact h4
    · rw [hfv "pwq" (by decide)]; exact h5
    · rw [hfv "pj" (by decide)]; exact h6
    · rw [hfv "qj" (by decide)]; exact h7
    · rw [hfv "dj" (by decide)]; exact h8
    · rw [hfv "wj" (by decide)]; exact h9
    · rw [hi']; omega
    · rw [hfa "G" (by decide)]; exact h11
    · rw [hfa "S" (by decide)]; exact h12
    · rw [hT, List.length_set]; exact h13
    · intro j
      rw [hT, hi']
      by_cases hj : j = σ.vars "i"
      · subst hj
        rw [getD_set_self _ _ _ hi0, if_pos (by omega)]
      · rw [getD_set_ne _ _ _ _ hj, h14 j]
        by_cases hjl : j < σ.vars "i"
        · rw [if_pos hjl, if_pos (by omega)]
        · rw [if_neg hjl, if_neg (by omega)]
  have hloop := Spec.forRangeZero (B := B) "i" "N" (TakeInv N w1 bb m pwq pj qj dj wj G S T0) N 200
    hNB (fun σ h => h.2.2.2.2.2.2.2.2.2.1) (fun σ h => h.1) hbody
  refine (hloop.conseq ?_ ?_ (by omega))
  · rintro σ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
    refine ⟨by simpa [Env.setVar] using h1, by simpa [Env.setVar] using h2,
      by simpa [Env.setVar] using h3, by simpa [Env.setVar] using h4,
      by simpa [Env.setVar] using h5, by simpa [Env.setVar] using h6,
      by simpa [Env.setVar] using h7, by simpa [Env.setVar] using h8,
      by simpa [Env.setVar] using h9, by simp [Env.setVar], by simpa [Env.setVar] using h10,
      by simpa [Env.setVar] using h11, by simp [Env.setVar, h12], ?_⟩
    intro j
    simp [Env.setVar, h12]
  · rintro σ σ' - ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, hl, hget⟩, hiN⟩
    refine ⟨hl, fun j => ?_⟩
    rw [hget j, hiN]

/-- **Pass 2 (take job `k`)**, cell by cell.  Mentions the scalars `"N" "w1" "bb" "m" "pwq"
"pj" "qj" "dj" "wj" "i" "u1" .. "u6"` and the arrays `"G"` (read), `"S"` (read), `"T"` (write). -/
theorem takeCom_spec {B bt w1 bb m INF pwq pj qj dj wj : ℕ} (G S T0 : List ℕ) (hB : 1 < B)
    (hw1 : 0 < w1) (_hbb : 0 < bb) (_hpwq : 0 < pwq) (hGl : G.length = bt)
    (hSl : S.length = bt * w1) (hSle : ∀ i, S.getD i 0 ≤ INF) (hT0 : T0.length = bt * w1)
    (hNB : bt * w1 < B) (hw1B : w1 < B) (hbbB : bb < B) (hmB : m + 1 < B) (hpwqB : pwq < B)
    (hpjB : pj < B) (hdjB : dj + 1 < B) (hwjB : wj < B) (hqjB : qj < B)
    (hINF : INF + pj + qj < B) (hGB : ∀ x, G.getD x 0 < B) :
    Spec B (fun σ => σ.vars "N" = bt * w1 ∧ σ.vars "w1" = w1 ∧ σ.vars "bb" = bb ∧
        σ.vars "m" = m ∧ σ.vars "pwq" = pwq ∧ σ.vars "pj" = pj ∧ σ.vars "qj" = qj ∧
        σ.vars "dj" = dj ∧ σ.vars "wj" = wj ∧
        σ.arrs "G" = G ∧ σ.arrs "S" = S ∧ σ.arrs "T" = T0) takeCom
      (fun _ σ' => TakeOK bt w1 bb m INF pwq pj qj dj wj G S (σ'.arrs "T") ∧
        (σ'.arrs "T").length = bt * w1)
      (204 * (bt * w1) + 6) := by
  refine (takeCom_loop (N := bt * w1) G S T0 hB hw1 hNB hw1B hbbB hmB hpwqB hpjB hdjB hwjB hqjB
    hINF (by rw [hGl]) hGB hSl.ge hT0.ge hSle).post ?_
  rintro σ σ' - ⟨hlen, hget⟩
  refine ⟨fun x hx c hc => ?_, hlen.trans hT0⟩
  have hk := lt_flat hx hc
  have hdiv := flat_div (w1 := w1) (b := x) hc
  have hmod := flat_mod (w1 := w1) (b := x) hc
  have e : (σ'.arrs "T").getD (x * w1 + c) 0 = takeStep w1 bb m pwq pj qj dj wj G S (x * w1 + c) := by
    rw [hget, if_pos hk]
  have hcc : x * w1 + c - x * w1 = c := by omega
  have hts : tsrc w1 pwq wj (x * w1 + c) = (x - pwq) * w1 + (c - wj) := by
    unfold tsrc; rw [hdiv, hcc]
  change (σ'.arrs "T").getD (x * w1 + c) 0 ≤ INF ∧ ∀ P, (σ'.arrs "T").getD (x * w1 + c) 0 ≤ P ↔ _
  rw [e]
  unfold takeStep
  rw [hts, hdiv]
  change _ ≤ INF ∧ ∀ P, _ ≤ P ↔ S.getD (x * w1 + c) 0 ≤ P ∨ (_ ∧ _ ∧ S.getD ((x - pwq) * w1 + (c - wj)) 0 + pj + qj ≤ dj ∧ _)
  have hSi := hSle (x * w1 + c)
  have hSt := hSle ((x - pwq) * w1 + (c - wj))
  split_ifs with hcond
  · refine ⟨by omega, fun P => ?_⟩
    obtain ⟨h1, h2, h3, h4⟩ := hcond
    constructor
    · intro h; exact Or.inr ⟨h1, h2, h3, h⟩
    · rintro (h | ⟨_, _, _, h⟩)
      · omega
      · exact h
  · refine ⟨hSi, fun P => ?_⟩
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨h1, h2, h3, h4⟩)
      · exact h
      · by_cases hlt : S.getD ((x - pwq) * w1 + (c - wj)) 0 + pj < S.getD (x * w1 + c) 0
        · exact absurd ⟨h1, h2, h3, hlt⟩ hcond
        · have h4' : S.getD ((x - pwq) * w1 + (c - wj)) 0 + pj ≤ P := h4
          omega

end Lax496464Proofs.Ram.Q3Passes
