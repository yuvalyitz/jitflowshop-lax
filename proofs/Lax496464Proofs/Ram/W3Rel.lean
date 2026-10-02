import Lax496464Proofs.Ram.W3Tab

/-!
# The Width Sweep's Table: One Event, and the Two Ends

Final statements (all over `scale J`; `hq : ∀ i, 0 < J.q i`; slots `sl : (scale J).Job → ℕ`):

* `due_rel` : `Rel J sl t' W INF T → SlotInj J sl t' → [j is the only event in (t', t], a due date]
    → Rel J sl t W INF (dueT (sl j) INF T)`;  `slotInj_due`.
* `start_rel` : `Rel J sl t' W INF T → SlotInj J sl t' → (∀ k ∈ alive J t', sl k ≠ sl j)
    → J.d j ≤ INF → [j is the only event in (t', t], a start]
    → Rel J sl t W INF (startT (sl j) (J.w j) (J.p j) (J.q j) (J.d j) J.machines INF T)`;
  `slotInj_start`.
* `rel_congr`, `slotInj_congr` : `Rel`/`SlotInj` only look at `sl` on the running jobs.
* `base_rel` : below every start, `fun X c => if X = 0 ∧ c = 0 then 0 else INF` is `Rel`.
* `readoff` : when every scaled due date is `≤ t`, `T 0 W < INF ↔ J.HasWeight W`.
-/

namespace Lax496464Proofs.Ram.W3Rel

open Lax496464.FlowShop Lax496464.EstOrder Lax496464.Sweep
open Lax496464.FlowShop.Instance (s Feasible weight HasWeight)
open Lax496464Proofs.Ram.W3Bits Lax496464Proofs.Ram.W3Tab

variable {J : Instance}

theorem hqs (hq : ∀ i : J.Job, 0 < J.q i) (i : (scale J).Job) : 0 < (scale J).q i :=
  Nat.mul_pos (Nat.succ_pos _) (hq i)

/-- The scaled start is below the scaled due date. -/
theorem sc_s_lt (hq : ∀ i : J.Job, 0 < J.q i) (j : (scale J).Job) :
    s (I := scale J) j < ((scale J).d j : ℤ) := by
  have := hqs hq j
  have h : s (I := scale J) j = ((scale J).d j : ℤ) - (scale J).q j := rfl
  omega

/-! ## `Rel` and `SlotInj` only depend on the slots of the running jobs -/

theorem mk_congr {sl sl' : (scale J).Job → ℕ} {X : Finset (scale J).Job}
    (h : ∀ k ∈ X, sl k = sl' k) : mk sl X = mk sl' X := by
  unfold mk
  rw [Finset.image_congr h]

theorem slotInj_congr {sl sl' : (scale J).Job → ℕ} {t : ℤ}
    (h : ∀ k ∈ alive J t, sl k = sl' k) : SlotInj J sl t ↔ SlotInj J sl' t := by
  unfold SlotInj
  constructor
  · intro H i hi k hk hik
    exact H i hi k hk (by rw [h i hi, h k hk]; exact hik)
  · intro H i hi k hk hik
    exact H i hi k hk (by rw [← h i hi, ← h k hk]; exact hik)

theorem rel_congr {sl sl' : (scale J).Job → ℕ} {t : ℤ} {W INF : ℕ} {T : ℕ → ℕ → ℕ}
    (h : ∀ k ∈ alive J t, sl k = sl' k) (hrel : Rel J sl t W INF T) : Rel J sl' t W INF T := by
  have hmk : ∀ X : Finset (scale J).Job, X ⊆ alive J t → mk sl X = mk sl' X :=
    fun X hX => mk_congr fun k hk => h k (hX hk)
  refine ⟨fun X hX c hc P => ?_, fun mask c hc hno => ?_⟩
  · rw [← hmk X hX]; exact hrel.ge_iff X hX c hc P
  · exact hrel.junk mask c hc fun X hX => by rw [hmk X hX]; exact hno X hX

/-! ## Slot injectivity across an event -/

theorem slotInj_due {sl : (scale J).Job → ℕ} {t' t : ℤ} {j : (scale J).Job}
    (hinj : SlotInj J sl t') (htt : t' < t) (hdj : ((scale J).d j : ℤ) = t)
    (hnos : ∀ k : (scale J).Job, ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : (scale J).Job, k ≠ j → ¬ (t' < ((scale J).d k : ℤ) ∧ ((scale J).d k : ℤ) ≤ t)) :
    SlotInj J sl t := by
  rw [SlotInj, alive_due htt hdj hnos hnod]
  intro i hi k hk hik
  exact hinj i (Finset.mem_of_mem_erase hi) k (Finset.mem_of_mem_erase hk) hik

theorem slotInj_start {sl : (scale J).Job → ℕ} {t' t : ℤ} {j : (scale J).Job}
    (hq : 0 < (scale J).q j) (hinj : SlotInj J sl t') (hfree : ∀ k ∈ alive J t', sl k ≠ sl j)
    (hsj : s (I := scale J) j = t) (htt : t' < t)
    (hnos : ∀ k : (scale J).Job, k ≠ j → ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : (scale J).Job, ¬ (t' < ((scale J).d k : ℤ) ∧ ((scale J).d k : ℤ) ≤ t)) :
    SlotInj J sl t := by
  rw [SlotInj, alive_start hq hsj htt hnos hnod]
  intro i hi k hk hik
  rw [Finset.mem_insert] at hi hk
  rcases hi with rfl | hi <;> rcases hk with rfl | hk
  · rfl
  · exact absurd hik.symm (hfree k hk)
  · exact absurd hik (hfree i hi)
  · exact hinj i hi k hk hik

/-! ## The due step -/

theorem due_rel (hq : ∀ i : J.Job, 0 < J.q i) {sl : (scale J).Job → ℕ} {t' t : ℤ} {W INF : ℕ}
    {T : ℕ → ℕ → ℕ} {j : (scale J).Job}
    (hrel : Rel J sl t' W INF T) (hinj : SlotInj J sl t')
    (htt : t' < t) (hdj : ((scale J).d j : ℤ) = t)
    (hnos : ∀ k : (scale J).Job, ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : (scale J).Job, k ≠ j → ¬ (t' < ((scale J).d k : ℤ) ∧ ((scale J).d k : ℤ) ≤ t)) :
    Rel J sl t W INF (dueT (sl j) INF T) := by
  have hj : j ∈ alive J t' := by
    rw [mem_alive]
    have h1 := sc_s_lt hq j
    have h2 := hnos j
    refine ⟨?_, by omega⟩
    by_contra hn
    exact h2 ⟨by omega, by omega⟩
  have halive := alive_due htt hdj hnos hnod
  have hsub : ∀ X : Finset (scale J).Job, X ⊆ alive J t → X ⊆ alive J t' ∧ j ∉ X := by
    intro X hX
    rw [halive] at hX
    refine ⟨fun k hk => Finset.mem_of_mem_erase (hX hk), fun hjX => ?_⟩
    exact (Finset.notMem_erase j _) (hX hjX)
  have hins : ∀ X : Finset (scale J).Job, X ⊆ alive J t' → j ∉ X →
      mk sl (insert j X) = mk sl X + 2 ^ sl j ∧ ¬ (mk sl X / 2 ^ sl j % 2 = 1) := by
    intro X hX hjX
    have hnm : sl j ∉ X.image sl := fun h => hjX ((mem_image_iff_of_inj hinj hX hj).mp h)
    exact ⟨mk_insert hnm, fun h => hnm (div_bit_mk.mp h)⟩
  refine ⟨fun X hX c hc P => ?_, fun mask c hc hno => ?_⟩
  · obtain ⟨hX', hjX⟩ := hsub X hX
    obtain ⟨hmk, hbit⟩ := hins X hX' hjX
    have hins' : insert j X ⊆ alive J t' := Finset.insert_subset hj hX'
    have h := ge_due (scale J) (hqs hq) (X := X) (c := c) (P := P) htt hdj hnos hnod
    have e1 := hrel.ge_iff X hX' c hc P
    have e2 := hrel.ge_iff (insert j X) hins' c hc P
    unfold dueT
    rw [if_neg hbit, h, e1, e2, hmk]
    simp only [hjX, not_false_eq_true, true_and]
    rcases le_total (T (mk sl X) c) (T (mk sl X + 2 ^ sl j) c) with hle | hle
    · rw [min_eq_left hle]
      constructor
      · rintro (h1 | ⟨h1, h2⟩)
        · exact h1
        · exact ⟨lt_of_le_of_lt hle h1, by
            have : Nsc J * T (mk sl X) c ≤ Nsc J * T (mk sl X + 2 ^ sl j) c :=
              Nat.mul_le_mul_left _ hle
            have : ((Nsc J * T (mk sl X) c : ℕ) : ℤ) ≤ ((Nsc J * T (mk sl X + 2 ^ sl j) c : ℕ) : ℤ) :=
              by exact_mod_cast this
            omega⟩
      · intro h1; exact Or.inl h1
    · rw [min_eq_right hle]
      constructor
      · rintro (⟨h1, h2⟩ | h1)
        · exact ⟨lt_of_le_of_lt hle h1, by
            have : Nsc J * T (mk sl X + 2 ^ sl j) c ≤ Nsc J * T (mk sl X) c :=
              Nat.mul_le_mul_left _ hle
            have : ((Nsc J * T (mk sl X + 2 ^ sl j) c : ℕ) : ℤ) ≤ ((Nsc J * T (mk sl X) c : ℕ) : ℤ) :=
              by exact_mod_cast this
            omega⟩
        · exact h1
      · intro h1; exact Or.inr h1
  · unfold dueT
    by_cases hbit : mask / 2 ^ sl j % 2 = 1
    · rw [if_pos hbit]
    · rw [if_neg hbit]
      have h1 : T mask c = INF := by
        refine hrel.junk mask c hc fun X' hX' hmk => ?_
        by_cases hjX : j ∈ X'
        · apply hbit
          rw [← hmk]
          exact div_bit_mk.mpr (Finset.mem_image_of_mem sl hjX)
        · refine hno X' ?_ hmk
          rw [halive]
          intro k hk
          exact Finset.mem_erase.mpr ⟨fun h => hjX (h ▸ hk), hX' hk⟩
      have h2 : T (mask + 2 ^ sl j) c = INF := by
        refine hrel.junk _ c hc fun X' hX' hmk => ?_
        have hbit' : (mask + 2 ^ sl j) / 2 ^ sl j % 2 = 1 := by
          have hpos : 0 < 2 ^ sl j := by positivity
          rw [Nat.add_div_right _ hpos]
          omega
        rw [← hmk] at hbit'
        have hjX : j ∈ X' := (mem_image_iff_of_inj hinj hX' hj).mp (div_bit_mk.mp hbit')
        have hX'' : X'.erase j ⊆ alive J t' := fun k hk => hX' (Finset.mem_of_mem_erase hk)
        have hnm : sl j ∉ (X'.erase j).image sl := fun h =>
          (Finset.notMem_erase j X') ((mem_image_iff_of_inj hinj hX'' hj).mp h)
        have hm : mk sl X' = mk sl (X'.erase j) + 2 ^ sl j := by
          conv_lhs => rw [← Finset.insert_erase hjX]
          exact mk_insert hnm
        refine hno (X'.erase j) ?_ (by omega)
        rw [halive]
        intro k hk
        have hk' := Finset.mem_erase.mp hk
        exact Finset.mem_erase.mpr ⟨hk'.1, hX'' hk⟩
      rw [h1, h2, min_self]

/-! ## The start step -/

theorem start_rel (hq : ∀ i : J.Job, 0 < J.q i) {sl : (scale J).Job → ℕ} {t' t : ℤ} {W INF : ℕ}
    {T : ℕ → ℕ → ℕ} {j : (scale J).Job}
    (hrel : Rel J sl t' W INF T) (hinj : SlotInj J sl t')
    (hfree : ∀ k ∈ alive J t', sl k ≠ sl j) (hd : J.d j ≤ INF)
    (htt : t' < t) (hsj : s (I := scale J) j = t)
    (hnos : ∀ k : (scale J).Job, k ≠ j → ¬ (t' < s k ∧ s k ≤ t))
    (hnod : ∀ k : (scale J).Job, ¬ (t' < ((scale J).d k : ℤ) ∧ ((scale J).d k : ℤ) ≤ t)) :
    Rel J sl t W INF
      (startT (sl j) (J.w j) (J.p j) (J.q j) (J.d j) J.machines INF T) := by
  have halive := alive_start (hqs hq j) hsj htt hnos hnod
  have hjn : j ∉ alive J t' := j_not_mem_alive_start hsj htt
  have hqj := hq j
  -- `insert j` on a set of jobs running at `t'`
  have hmk1 : ∀ Y : Finset (scale J).Job, Y ⊆ alive J t' →
      mk sl (insert j Y) = mk sl Y + 2 ^ sl j := by
    intro Y hY
    refine mk_insert ?_
    intro h
    obtain ⟨k, hk, hkk⟩ := Finset.mem_image.mp h
    exact hfree k (hY hk) hkk
  have hsub : ∀ X : Finset (scale J).Job, X ⊆ alive J t → X.erase j ⊆ alive J t' := by
    intro X hX k hk
    have hk' := Finset.mem_erase.mp hk
    have := hX hk'.2
    rw [halive, Finset.mem_insert] at this
    exact this.resolve_left hk'.1
  refine ⟨fun X hX c hc P => ?_, fun mask c hc hno => ?_⟩
  · have hY := hsub X hX
    have h := ge_start (scale J) (hqs hq) (X := X) (c := c) (P := P) htt hsj hnos hnod
    unfold startT
    by_cases hjX : j ∈ X
    · -- `j` runs: the state comes from the one without it
      have hX' : W3Tab.mk sl X = W3Tab.mk sl (X.erase j) + 2 ^ sl j := by
        conv_lhs => rw [← Finset.insert_erase hjX]
        exact hmk1 _ hY
      have hbit : W3Tab.mk sl X / 2 ^ sl j % 2 = 1 :=
        div_bit_mk.mpr (Finset.mem_image_of_mem sl hjX)
      have hsub' : W3Tab.mk sl X - 2 ^ sl j = W3Tab.mk sl (X.erase j) := by omega
      have hcard : pcnt (W3Tab.mk sl X - 2 ^ sl j) = (X.erase j).card := by
        rw [hsub']
        unfold mk
        rw [pcnt_maskOf]
        exact Finset.card_image_of_injOn fun a ha b hb hab =>
          hinj a (hY ha) b (hY hb) hab
      rw [if_pos hbit, hcard, hsub', h]
      simp only [hjX, not_true_eq_false, false_and, true_and, false_or]
      set u := T (W3Tab.mk sl (X.erase j)) (c - J.w j) with hu
      have hc' : c - J.w j ≤ W := by omega
      have hge : ∀ P'' : ℤ, Ge (scale J) t' (X.erase j) (c - J.w j) P'' ↔
          (u < INF ∧ ((Nsc J * u : ℕ) : ℤ) ≤ P'') := fun P'' =>
        hrel.ge_iff (X.erase j) hY (c - J.w j) hc' P''
      have hs : s (I := scale J) j = (Nsc J : ℤ) * s (I := J) j + (j : ℕ) := sc_s J j
      have hs' : s (I := J) j = (J.d j : ℤ) - J.q j := rfl
      have hpp : ((scale J).p j : ℤ) = ((Nsc J * J.p j : ℕ) : ℤ) := rfl
      by_cases hcm : (X.erase j).card < J.machines
      · by_cases hg : u + J.p j + J.q j ≤ J.d j
        · rw [if_pos ⟨hcm, hg⟩]
          have hlt : u + J.p j < INF := by omega
          constructor
          · rintro ⟨-, P'', hP'', h1, h2⟩
            refine ⟨hlt, ?_⟩
            have := ((hge P'').mp hP'').2
            rw [hpp] at h2
            push_cast at this h2 ⊢
            nlinarith
          · rintro ⟨-, h2⟩
            refine ⟨hcm, (Nsc J * u : ℕ), (hge _).mpr ⟨by omega, le_rfl⟩, ?_, ?_⟩
            · exact (guard_iff J j u).mpr (by omega)
            · rw [hpp]; push_cast at h2 ⊢; nlinarith
        · rw [if_neg (fun h => hg h.2)]
          constructor
          · rintro ⟨-, P'', hP'', h1, h2⟩
            exfalso
            have := ((hge P'').mp hP'').2
            have h3 : (((Nsc J * u : ℕ) : ℤ) + (scale J).p j ≤ s (I := scale J) j) := by
              have : (((Nsc J * u : ℕ) : ℤ)) ≤ P'' := this
              omega
            have := (guard_iff J j u).mp h3
            omega
          · rintro ⟨h1, -⟩; exact absurd h1 (lt_irrefl _)
      · rw [if_neg (fun h => hcm h.1)]
        constructor
        · rintro ⟨h1, -⟩; exact absurd h1 hcm
        · rintro ⟨h1, -⟩; exact absurd h1 (lt_irrefl _)
    · -- `j` does not run: nothing changes
      have hX' : X ⊆ alive J t' := by
        intro k hk
        have := hX hk
        rw [halive, Finset.mem_insert] at this
        exact this.resolve_left (fun h => hjX (h ▸ hk))
      have hbit : ¬ (W3Tab.mk sl X / 2 ^ sl j % 2 = 1) := by
        intro hb
        obtain ⟨k, hk, hkk⟩ := Finset.mem_image.mp (div_bit_mk.mp hb)
        exact hfree k (hX' hk) hkk
      rw [if_neg hbit, h]
      simp only [hjX, not_false_eq_true, true_and, false_and, or_false]
      exact hrel.ge_iff X hX' c hc P
  · unfold startT
    have hsubA : alive J t' ⊆ alive J t := by
      rw [halive]; exact Finset.subset_insert _ _
    by_cases hbit : mask / 2 ^ sl j % 2 = 1
    · rw [if_pos hbit]
      by_cases hcond : pcnt (mask - 2 ^ sl j) < J.machines ∧
          T (mask - 2 ^ sl j) (c - J.w j) + J.p j + J.q j ≤ J.d j
      · exfalso
        have hT : T (mask - 2 ^ sl j) (c - J.w j) = INF := by
          refine hrel.junk _ (c - J.w j) (by omega) fun X' hX' hmk => ?_
          have hle : 2 ^ sl j ≤ mask := by
            by_contra hlt
            have h0 : mask / 2 ^ sl j = 0 := Nat.div_eq_of_lt (not_le.mp hlt)
            rw [h0] at hbit
            omega
          refine hno (insert j X') ?_ ?_
          · rw [halive]; exact Finset.insert_subset_insert _ hX'
          · rw [hmk1 X' hX', hmk]; omega
        have := hcond.2
        rw [hT] at this
        omega
      · rw [if_neg hcond]
    · rw [if_neg hbit]
      exact hrel.junk mask c hc fun X' hX' hmk => hno X' (hX'.trans hsubA) hmk

/-! ## The two ends -/

theorem alive_of_lt_all {t₀ : ℤ} (ht : ∀ k : (scale J).Job, t₀ < s (I := scale J) k) :
    alive J t₀ = ∅ := by
  ext k
  simp only [Finset.notMem_empty, iff_false, mem_alive]
  have := ht k
  omega

theorem reachable_of_lt_all {t₀ : ℤ} (ht : ∀ k : (scale J).Job, t₀ < s (I := scale J) k)
    {X : Finset (scale J).Job} {W' : ℕ} {P : ℤ} :
    Reachable (scale J) t₀ X W' P ↔ X = ∅ ∧ W' = 0 ∧ 0 ≤ P := by
  rw [Section4.reachable_iff_model]
  have := (Lax496464Proofs.FFJ.reachable_of_lt_all (I := Lax496464Proofs.Bridge.model (scale J))
    (t := t₀) (fun k => ht k) (X := X) (W' := W') (P' := P))
  exact this

/-- **The base case.** Below every start the table has the empty solution only. -/
theorem base_rel {sl : (scale J).Job → ℕ} {t₀ : ℤ} (W INF : ℕ) (hINF : 0 < INF)
    (ht : ∀ k : (scale J).Job, t₀ < s (I := scale J) k) :
    Rel J sl t₀ W INF (fun X c => if X = 0 ∧ c = 0 then 0 else INF) := by
  have hal := alive_of_lt_all (J := J) ht
  refine ⟨fun X hX c hc P => ?_, fun mask c hc hno => ?_⟩
  · rw [hal] at hX
    have hXe : X = ∅ := Finset.subset_empty.mp hX
    subst hXe
    have hm : W3Tab.mk sl (∅ : Finset (scale J).Job) = 0 := by simp [mk, maskOf]
    rw [hm]
    unfold Ge
    simp only [reachable_of_lt_all ht, true_and]
    by_cases hc0 : c = 0
    · subst hc0
      simp only [if_true, hINF, true_and]
      constructor
      · rintro ⟨W', -, -, hP⟩; simpa using hP
      · intro hP; exact ⟨0, le_rfl, rfl, by simpa using hP⟩
    · simp only [hc0, if_false, lt_irrefl, false_and, iff_false]
      rintro ⟨W', hW', rfl, -⟩
      omega
  · have hm : W3Tab.mk sl (∅ : Finset (scale J).Job) = 0 := by simp [mk, maskOf]
    by_cases h0 : mask = 0
    · exfalso
      exact hno ∅ (by simp) (by rw [hm, h0])
    · simp [h0]

/-- **The read-off.** Once every scaled due date has passed, nothing runs, and the entry
`T 0 W` is finite exactly when some feasible set weighs at least `W`. -/
theorem readoff (hE : EstOrdered J) (hq : ∀ i : J.Job, 0 < J.q i) {sl : (scale J).Job → ℕ}
    {t : ℤ} {W INF : ℕ} {T : ℕ → ℕ → ℕ}
    (hrel : Rel J sl t W INF T) (hall : ∀ k : (scale J).Job, ((scale J).d k : ℤ) ≤ t) :
    T 0 W < INF ↔ HasWeight J W := by
  have hal : alive J t = ∅ := by
    ext k
    simp only [Finset.notMem_empty, iff_false, mem_alive]
    have := hall k
    omega
  have hm : W3Tab.mk sl (∅ : Finset (scale J).Job) = 0 := by simp [mk, maskOf]
  have hge : ∀ P : ℤ, Ge (scale J) t ∅ W P ↔ (T 0 W < INF ∧ ((Nsc J * T 0 W : ℕ) : ℤ) ≤ P) := by
    intro P
    have := hrel.ge_iff ∅ (by rw [hal]) W le_rfl P
    rwa [hm] at this
  have hst : ∀ k : (scale J).Job, s (I := scale J) k ≤ t := fun k => by
    have := sc_s_lt hq k
    have := hall k
    omega
  constructor
  · intro h
    obtain ⟨W', hW', hR⟩ := (hge _).mpr ⟨h, le_rfl⟩
    obtain ⟨Z, hZ, hw⟩ := (Section4.exists_reachable_iff (scale J) hst W').mp ⟨_, _, hR⟩
    exact ⟨Z, (Section4.scale_feasible_iff J hE hq Z).mp hZ, by
      have : weight (scale J) Z = weight J Z := rfl
      omega⟩
  · rintro ⟨Z, hZ, hw⟩
    have hZ' : Feasible (scale J) Z := (Section4.scale_feasible_iff J hE hq Z).mpr hZ
    obtain ⟨X, P, hR⟩ := (Section4.exists_reachable_iff (scale J) hst (weight J Z)).mpr ⟨Z, hZ', rfl⟩
    have hX : X = ∅ := by
      obtain ⟨Z', -, -, hrun, -⟩ := hR
      rw [← hrun]
      apply Finset.eq_empty_of_forall_notMem
      intro k hk
      have hk' := (Finset.mem_filter.mp hk).2
      have := hall k
      omega
    subst hX
    exact ((hge P).mp ⟨weight J Z, hw, hR⟩).1

/-- A job whose due date is the only event in `(t', t]` was running at `t'`. -/
theorem due_mem_alive (hq : ∀ i : J.Job, 0 < J.q i) {t' t : ℤ} {j : (scale J).Job}
    (htt : t' < t) (hdj : ((scale J).d j : ℤ) = t)
    (hnos : ∀ k : (scale J).Job, ¬ (t' < s k ∧ s k ≤ t)) : j ∈ alive J t' := by
  rw [mem_alive]
  have h1 := sc_s_lt hq j
  have h2 := hnos j
  refine ⟨?_, by omega⟩
  by_contra hn
  exact h2 ⟨by omega, by omega⟩

end Lax496464Proofs.Ram.W3Rel
