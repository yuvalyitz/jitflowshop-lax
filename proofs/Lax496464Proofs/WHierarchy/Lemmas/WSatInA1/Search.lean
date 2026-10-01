import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic

/-! # The bounded search tree

`sim c b` walks the clauses in order, keeping a list `ch` of chosen elements: a clause with the key
of `c` that `ch` does not hit is hit by the positive literal named by the next digit of `b` (or the
search fails, also when `k` elements are chosen already).

* **Soundness**: a successful search chooses at most `k` first occurrences and hits every clause
  with the key of `c`.
* **Completeness**: if a set `T` of at most `k` elements hits every such clause, then the search
  along some branch word `b < d ^ k` succeeds and chooses only elements of `T` — the digits follow
  the elements of `T`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search

open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic

variable (cl : List (List ℕ)) (d k c : ℕ)

theorem fold_none (δ : ℕ → ℕ) : ∀ l : List ℕ, l.foldl (simStep cl d k c δ) none = none
  | [] => rfl
  | _ :: l => fold_none δ l

theorem hitB_iff (ch : List ℕ) (c2 : ℕ) :
    hitB cl ch c2 = true ↔
      ∃ i < len cl c2, code cl (off cl c2 + i) % 2 = 0 ∧ fst cl (off cl c2 + i) ∈ ch := by
  simp [hitB]

theorem hitB_mono {ch ch' : List ℕ} (h : ∀ e ∈ ch, e ∈ ch') {c2 : ℕ} (hh : hitB cl ch c2 = true) :
    hitB cl ch' c2 = true := by
  rw [hitB_iff] at hh ⊢
  obtain ⟨i, hi, he, hm⟩ := hh
  exact ⟨i, hi, he, h _ hm⟩

/-! ### Soundness -/

theorem fold_sound (δ : ℕ → ℕ) : ∀ (l : List ℕ) (ch0 ch : List ℕ),
    l.foldl (simStep cl d k c δ) (some ch0) = some ch → (∀ c2 ∈ l, c2 < cl.length) →
    ch0.length ≤ k →
    (∀ e ∈ ch0, e ∈ ch) ∧ ch.length ≤ k ∧ (∀ e ∈ ch, e ∈ ch0 ∨ ∃ j < nL cl, e = fst cl j) ∧
      ∀ c2 ∈ l, key cl d c2 = key cl d c → hitB cl ch c2 = true
  | [], ch0, ch, h, _, hk => by
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h
    exact ⟨fun e he => he, hk, fun e he => Or.inl he, fun _ h => absurd h (by simp)⟩
  | c2 :: l, ch0, ch, h, hl, hk => by
    have hc2 : c2 < cl.length := hl c2 (by simp)
    have hl' : ∀ c3 ∈ l, c3 < cl.length := fun c3 h3 => hl c3 (by simp [h3])
    simp only [List.foldl_cons] at h
    by_cases hg : key cl d c2 = key cl d c ∧ hitB cl ch0 c2 = false
    · have hs : simStep cl d k c δ (some ch0) c2 = if ch0.length = k then none
          else if δ ch0.length < len cl c2 ∧ code cl (off cl c2 + δ ch0.length) % 2 = 0 then
            some (ch0 ++ [fst cl (off cl c2 + δ ch0.length)]) else none := by
        simp only [simStep, if_pos hg]
      rw [hs] at h
      by_cases hk' : ch0.length = k
      · rw [if_pos hk', fold_none] at h; cases h
      · rw [if_neg hk'] at h
        by_cases hp : δ ch0.length < len cl c2 ∧ code cl (off cl c2 + δ ch0.length) % 2 = 0
        · rw [if_pos hp] at h
          obtain ⟨h1, h2, h3, h4⟩ := fold_sound δ l _ ch h hl' (by simp; omega)
          refine ⟨fun e he => h1 e (by simp [he]), h2, fun e he => ?_, ?_⟩
          · rcases h3 e he with h5 | h5
            · simp only [List.mem_append, List.mem_singleton] at h5
              rcases h5 with h5 | rfl
              · exact Or.inl h5
              · exact Or.inr ⟨_, off_lt cl hc2 hp.1, rfl⟩
            · exact Or.inr h5
          · intro c3 hc3 hkey
            simp only [List.mem_cons] at hc3
            rcases hc3 with rfl | hc3
            · refine (hitB_iff cl ch c3).mpr ⟨_, hp.1, hp.2, h1 _ (by simp)⟩
            · exact h4 c3 hc3 hkey
        · rw [if_neg hp, fold_none] at h; cases h
    · have hs : simStep cl d k c δ (some ch0) c2 = some ch0 := by
        simp only [simStep, if_neg hg]
      rw [hs] at h
      obtain ⟨h1, h2, h3, h4⟩ := fold_sound δ l ch0 ch h hl' hk
      refine ⟨h1, h2, h3, fun c3 hc3 hkey => ?_⟩
      simp only [List.mem_cons] at hc3
      rcases hc3 with rfl | hc3
      · have : hitB cl ch0 c3 = true := by
          by_contra hn; exact hg ⟨hkey, by simpa using hn⟩
        exact hitB_mono cl h1 this
      · exact h4 c3 hc3 hkey

/-- **Soundness of the search.** -/
theorem sim_sound {δ : ℕ → ℕ} {ch : List ℕ} (h : simD cl d k c δ = some ch) :
    ch.length ≤ k ∧ (∀ e ∈ ch, ∃ j < nL cl, e = fst cl j) ∧
      ∀ c2 < cl.length, key cl d c2 = key cl d c → hitB cl ch c2 = true := by
  obtain ⟨-, h2, h3, h4⟩ := fold_sound cl d k c δ _ [] ch h (fun c2 h => List.mem_range.mp h)
    (Nat.zero_le _)
  exact ⟨h2, fun e he => (h3 e he).resolve_left (by simp),
    fun c2 hc2 hkey => h4 c2 (List.mem_range.mpr hc2) hkey⟩

/-! ### Completeness -/

theorem fold_complete (T : Finset ℕ) (hT : T.card ≤ k) (hd0 : 0 < d)
    (hd : ∀ c2, len cl c2 ≤ d) : ∀ (l : List ℕ) (ch : List ℕ), ch.Nodup → (∀ e ∈ ch, e ∈ T) →
    (∀ c2 ∈ l, key cl d c2 = key cl d c →
      ∃ i < len cl c2, code cl (off cl c2 + i) % 2 = 0 ∧ fst cl (off cl c2 + i) ∈ T) →
    ∃ δ' : ℕ → ℕ, (∀ n, δ' n < d) ∧ ∀ δ : ℕ → ℕ,
      (∀ n, ch.length ≤ n → n < k → δ n = δ' n) →
      ∃ ch', l.foldl (simStep cl d k c δ) (some ch) = some ch' ∧ ∀ e ∈ ch', e ∈ T
  | [], ch, _, hch, _ => ⟨fun _ => 0, fun _ => hd0, fun _ _ => ⟨ch, rfl, hch⟩⟩
  | c2 :: l, ch, hnd, hch, hhit => by
    have hhit' : ∀ c3 ∈ l, key cl d c3 = key cl d c →
        ∃ i < len cl c3, code cl (off cl c3 + i) % 2 = 0 ∧ fst cl (off cl c3 + i) ∈ T :=
      fun c3 h3 => hhit c3 (by simp [h3])
    by_cases hg : key cl d c2 = key cl d c ∧ hitB cl ch c2 = false
    · obtain ⟨i, hi, he, hT'⟩ := hhit c2 (by simp) hg.1
      set a := fst cl (off cl c2 + i) with ha
      have hna : a ∉ ch := by
        intro hm
        have : hitB cl ch c2 = true := (hitB_iff cl ch c2).mpr ⟨i, hi, he, hm⟩
        rw [hg.2] at this; cases this
      have hlen : ch.length < k := by
        have hsub : insert a ch.toFinset ⊆ T := by
          intro e he'
          rw [Finset.mem_insert, List.mem_toFinset] at he'
          rcases he' with rfl | he'
          · exact hT'
          · exact hch e he'
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simpa using hna), List.toFinset_card_of_nodup hnd]
          at this
        omega
      obtain ⟨δ'', hδ'', hrun⟩ := fold_complete T hT hd0 hd l (ch ++ [a])
        (List.nodup_append.mpr ⟨hnd, by simp, by simp only [List.mem_singleton]; rintro e he _ rfl rfl; exact hna he⟩)
        (fun e he' => by
          simp only [List.mem_append, List.mem_singleton] at he'
          rcases he' with he' | rfl
          · exact hch e he'
          · exact hT') hhit'
      refine ⟨Function.update δ'' ch.length i, fun n => ?_, fun δ hδ => ?_⟩
      · by_cases hn : n = ch.length
        · subst hn; simp only [Function.update_self]; exact lt_of_lt_of_le hi (hd c2)
        · rw [Function.update_of_ne hn]; exact hδ'' n
      · have hdi : δ ch.length = i := by
          rw [hδ ch.length le_rfl hlen, Function.update_self]
        have hs : simStep cl d k c δ (some ch) c2 = some (ch ++ [a]) := by
          simp only [simStep, if_pos hg, if_neg (show ch.length ≠ k by omega), hdi]
          rw [if_pos ⟨hi, he⟩]
        simp only [List.foldl_cons, hs]
        refine hrun δ fun n hn hnk => ?_
        simp only [List.length_append, List.length_singleton] at hn
        rw [hδ n (by omega) hnk, Function.update_of_ne (by omega)]
    · obtain ⟨δ'', hδ'', hrun⟩ := fold_complete T hT hd0 hd l ch hnd hch hhit'
      refine ⟨δ'', hδ'', fun δ hδ => ?_⟩
      have hs : simStep cl d k c δ (some ch) c2 = some ch := by
        simp only [simStep, if_neg hg]
      simp only [List.foldl_cons, hs]
      exact hrun δ hδ

/-- **Completeness of the search.** -/
theorem sim_complete (T : Finset ℕ) (hT : T.card ≤ k) (hc : c < cl.length)
    (hd : ∀ c2, len cl c2 ≤ d)
    (hhit : ∀ c2 < cl.length, key cl d c2 = key cl d c →
      ∃ i < len cl c2, code cl (off cl c2 + i) % 2 = 0 ∧ fst cl (off cl c2 + i) ∈ T) :
    ∃ b < d ^ k, ∃ ch, sim cl d k c b = some ch ∧ ∀ e ∈ ch, e ∈ T := by
  have hd0 : 0 < d := by
    obtain ⟨i, hi, -⟩ := hhit c hc rfl
    exact lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) hi) (hd c)
  obtain ⟨δ', hδ', hrun⟩ := fold_complete cl d k c T hT hd0 hd (List.range cl.length) []
    List.nodup_nil (by simp) (fun c2 h2 => hhit c2 (List.mem_range.mp h2))
  obtain ⟨b, hb, hdig⟩ := exists_digits d k δ' fun p _ => hδ' p
  obtain ⟨ch, h1, h2⟩ := hrun (bdig d b) fun n _ hn => hdig n hn
  exact ⟨b, hb, ch, h1, h2⟩

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search
