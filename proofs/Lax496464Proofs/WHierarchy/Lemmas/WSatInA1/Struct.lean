import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search

/-! # The structure

The relations of the structure are the lists `tss` read as sets; each list is without repetition
(one tuple per stored value, at its first occurrence), so `structWord` encodes the structure. The
relations are characterized by the tuples that were stored: `C` is the set of first occurrences,
`N` the set of keys, `Lr` the set of the tuples found by the searches. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct

open Lax496464.WH_B1_Structures
open Lax496464Proofs.WHierarchy.Logic.StructureCode
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Search
open Lax496464Proofs.WHierarchy.HittingSet.Compress (getD_idxOf getD_mem)

variable (cl : List (List ℕ)) (d k : ℕ)

/-! ### Entries -/

theorem MM_pos : 4 ≤ MM cl := by unfold MM; omega

theorem keyE_le (c p : ℕ) : keyE cl c p ≤ nL cl := by
  unfold keyE
  split_ifs with h1 h2
  · exact le_rfl
  · have := off_lt cl (c := c) (p := p)
    by_cases hc : c < cl.length
    · exact (fst_lt cl (this hc h1)).le
    · unfold len at h1; rw [List.getD_eq_default _ _ (by omega)] at h1; simp at h1
  · exact le_rfl

theorem length_key (c : ℕ) : (key cl d c).length = d + 1 := by simp [key]

theorem key_lt {c x : ℕ} (hx : x ∈ key cl d c) : x < MM cl := by
  simp only [key, List.mem_map, List.mem_range] at hx
  obtain ⟨p, -, rfl⟩ := hx
  have := keyE_le cl c p; unfold MM; omega

theorem length_pad (ch : List ℕ) : (pad cl k ch).length = k + 1 := by simp [pad]

theorem mem_pad {ch : List ℕ} {x : ℕ} (hx : x ∈ pad cl k ch) : x ∈ ch ∨ x = nL cl := by
  simp only [pad, List.mem_map, List.mem_range] at hx
  obtain ⟨q, -, rfl⟩ := hx
  split_ifs with h
  · exact Or.inl (by rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
  · exact Or.inr rfl

theorem mem_pad_of_mem {ch : List ℕ} (hl : ch.length ≤ k + 1) {x : ℕ} (hx : x ∈ ch) :
    x ∈ pad cl k ch := by
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hx
  simp only [pad, List.mem_map, List.mem_range]
  exact ⟨q, by omega, by rw [if_pos hq, List.getD_eq_getElem _ _ hq]⟩

theorem mem_lTuples {t : List ℕ} : t ∈ lTuples cl d k ↔
    ∃ c < cl.length, ∃ b < d ^ k, ∃ ch, sim cl d k c b = some ch ∧ t = key cl d c ++ pad cl k ch := by
  simp only [lTuples, List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c, hc, b, hb, ch, hs, rfl⟩; exact ⟨c, hc, b, hb, ch, hs, rfl⟩
  · rintro ⟨c, hc, b, hb, ch, hs, rfl⟩; exact ⟨c, hc, b, hb, ch, hs, rfl⟩

theorem lTuple_props {t : List ℕ} (ht : t ∈ lTuples cl d k) :
    t.length = d + k + 2 ∧ ∀ x ∈ t, x < MM cl := by
  obtain ⟨c, hc, b, hb, ch, hs, rfl⟩ := (mem_lTuples cl d k).mp ht
  obtain ⟨-, h2, -⟩ := sim_sound cl d k c hs
  refine ⟨by simp [length_key, length_pad]; omega, fun x hx => ?_⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact key_lt cl d hx
  · rcases mem_pad cl k hx with hx | rfl
    · obtain ⟨j, hj, rfl⟩ := h2 x hx
      have := fst_lt cl hj; unfold MM; omega
    · unfold MM; omega

theorem length_lTuples : (lTuples cl d k).length ≤ cl.length * d ^ k := by
  unfold lTuples
  rw [List.length_flatMap]
  have : ∀ c ∈ List.range cl.length, ((List.range (d ^ k)).filterMap fun b =>
      (sim cl d k c b).map fun ch => key cl d c ++ pad cl k ch).length ≤ d ^ k := fun c _ =>
    (List.length_filterMap_le _ _).trans (by simp)
  calc ((List.range cl.length).map _).sum ≤ ((List.range cl.length).map fun _ => d ^ k).sum :=
        List.sum_le_sum (by simpa using this)
    _ = cl.length * d ^ k := by simp

/-! ### The array of numbers -/

theorem length_varNums : (varNums cl).length = nL cl := by simp [varNums]
theorem length_canonNums : (canonNums cl).length = nL cl := by simp [canonNums]
theorem length_nNums : (nNums cl d).length = cl.length := by simp [nNums]
theorem length_lNums : (lNums cl d k).length = (lTuples cl d k).length := by simp [lNums]

theorem length_hs : (hs cl d k).length = sz cl d k := by
  have := length_lTuples cl d k
  simp only [hs, List.length_append, List.length_replicate, length_varNums, length_canonNums,
    length_nNums, length_lNums, sz]
  omega

theorem mem_hs {e : ℕ} (he : e ∈ hs cl d k) :
    e ∈ varNums cl ∨ e ∈ canonNums cl ∨ e ∈ nNums cl d ∨ e ∈ lNums cl d k ∨ e = 0 := by
  simp only [hs, List.mem_append] at he
  rcases he with (((h | h) | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (List.eq_of_mem_replicate h))))

/-- A stored value with a nonzero tag is a tuple of that tag. -/
theorem tagged {e : ℕ} (he : e ∈ hs cl d k) {g : ℕ} (hg : e % MM cl = g) (hg0 : g ≠ 0) :
    (g = 1 ∧ ∃ j < nL cl, e = 1 + MM cl * num (MM cl) [fst cl j]) ∨
    (g = 2 ∧ ∃ c < cl.length, e = 2 + MM cl * num (MM cl) (key cl d c)) ∨
    (g = 3 ∧ ∃ t ∈ lTuples cl d k, e = 3 + MM cl * num (MM cl) t) := by
  have hM := MM_pos cl
  rcases mem_hs cl d k he with h | h | h | h | rfl
  · simp only [varNums, List.mem_map, List.mem_range] at h
    obtain ⟨j, -, rfl⟩ := h
    simp at hg; omega
  · simp only [canonNums, List.mem_map, List.mem_range] at h
    obtain ⟨j, hj, rfl⟩ := h
    left
    refine ⟨?_, j, hj, by simp⟩
    rw [← hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · simp only [nNums, List.mem_map, List.mem_range] at h
    obtain ⟨c, hc, rfl⟩ := h
    right; left
    refine ⟨?_, c, hc, rfl⟩
    rw [← hg, nNum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · simp only [lNums, List.mem_map] at h
    obtain ⟨t, ht, rfl⟩ := h
    right; right
    refine ⟨?_, t, ht, rfl⟩
    rw [← hg, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · simp at hg; omega

theorem mem_hs_of_canon {j : ℕ} (hj : j < nL cl) : 1 + MM cl * fst cl j ∈ hs cl d k := by
  simp only [hs, List.mem_append]
  left; left; left; right
  simp only [canonNums, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩

theorem mem_hs_of_key {c : ℕ} (hc : c < cl.length) : nNum cl d c ∈ hs cl d k := by
  simp only [hs, List.mem_append]
  left; left; right
  simp only [nNums, List.mem_map, List.mem_range]; exact ⟨c, hc, rfl⟩

theorem mem_hs_of_lTuple {t : List ℕ} (ht : t ∈ lTuples cl d k) :
    3 + MM cl * num (MM cl) t ∈ hs cl d k := by
  simp only [hs, List.mem_append]
  left; right
  simp only [lNums, List.mem_map]; exact ⟨t, ht, rfl⟩

/-! ### The emitted lists -/

theorem fe_getD {t : ℕ} (ht : t < sz cl d k) :
    (fe cl d k).getD t 0 = (hs cl d k).idxOf ((hs cl d k).getD t 0) := by
  unfold fe Lax496464Proofs.WHierarchy.HittingSet.Firsts.firsts
  rw [List.getD_eq_getElem _ _ (by simpa [length_hs] using ht)]
  simp

/-- The tuples of tag `g`: the digits of the stored values of that tag. -/
theorem mem_emitList {g a : ℕ} {tu : List ℕ} :
    tu ∈ emitList cl d k g a ↔
      ∃ e ∈ hs cl d k, e % MM cl = g ∧ tu = digitsOf (MM cl) a (e / MM cl) := by
  simp only [emitList, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨t, ⟨ht, hg, -⟩, rfl⟩
    exact ⟨_, getD_mem (by rw [length_hs]; exact ht), hg, rfl⟩
  · rintro ⟨e, he, hg, rfl⟩
    have hi := List.idxOf_lt_length_of_mem he
    rw [length_hs] at hi
    have hv : (hs cl d k).getD ((hs cl d k).idxOf e) 0 = e := getD_idxOf he
    refine ⟨(hs cl d k).idxOf e, ⟨hi, by rw [hv]; exact hg, ?_⟩, by rw [hv]⟩
    rw [fe_getD cl d k hi, hv]

theorem digits_tagged {M g : ℕ} (hg : g < M) {tu : List ℕ} (h : ∀ x ∈ tu, x < M) :
    digitsOf M tu.length ((g + M * num M tu) / M) = tu := by
  rw [tag_div hg]; exact digitsOf_num h

theorem digits_one {M u : ℕ} (hM : 1 < M) (hu : u < M) :
    digitsOf M 1 ((1 + M * num M [u]) / M) = [u] := by
  have h := digits_tagged (g := 1) (M := M) hM (tu := [u]) (by simpa using hu)
  simpa using h

theorem nodup_emitList (g a : ℕ) (hg0 : g ≠ 0)
    (hga : (g = 1 → a = 1) ∧ (g = 2 → a = d + 1) ∧ (g = 3 → a = d + k + 2)) :
    (emitList cl d k g a).Nodup := by
  have hM := MM_pos cl
  -- a stored value of tag `g` is determined by its digits
  have key' : ∀ e ∈ hs cl d k, e % MM cl = g →
      e = g + MM cl * num (MM cl) (digitsOf (MM cl) a (e / MM cl)) := by
    intro e he hg
    rcases tagged cl d k he hg hg0 with ⟨rfl, j, hj, rfl⟩ | ⟨rfl, c, hc, rfl⟩ | ⟨rfl, t, ht, rfl⟩
    · have hf := fst_lt cl hj
      rw [hga.1 rfl, digits_one (by omega) (by unfold MM; omega)]
    · rw [hga.2.1 rfl, ← length_key cl d c,
        digits_tagged (by omega) (fun x hx => key_lt cl d hx)]
    · obtain ⟨hl, hlt⟩ := lTuple_props cl d k ht
      rw [hga.2.2 rfl, ← hl, digits_tagged (by omega) hlt]
  unfold emitList
  refine List.Nodup.map_on ?_ (List.Nodup.filter _ List.nodup_range)
  intro t ht t' ht' heq
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at ht ht'
  have he : (hs cl d k).getD t 0 = (hs cl d k).getD t' 0 := by
    rw [key' _ (getD_mem (by rw [length_hs]; exact ht.1)) ht.2.1,
      key' _ (getD_mem (by rw [length_hs]; exact ht'.1)) ht'.2.1, heq]
  rw [← ht.2.2, ← ht'.2.2, fe_getD cl d k ht.1, fe_getD cl d k ht'.1, he]

/-! ### The structure -/

theorem wf_tss : ∀ i, ∀ t ∈ ((tss cl d k).getD i []).toFinset,
    i < (arities d k).length ∧ t.length = (arities d k).getD i 0 ∧ ∀ a ∈ t, a < nL cl + 1 := by
  have hM := MM_pos cl
  intro i t ht
  rw [List.mem_toFinset] at ht
  have dig : ∀ {a e x : ℕ}, x ∈ digitsOf (MM cl) a e → x < MM cl := by
    intro a e x hx
    simp only [digitsOf, List.mem_map] at hx
    obtain ⟨p, -, rfl⟩ := hx; exact Nat.mod_lt _ (by omega)
  -- the entries of a tagged tuple
  have ent : ∀ {g a : ℕ} {tu : List ℕ}, g ≠ 0 →
      (g = 1 → a = 1) → (g = 2 → a = d + 1) → (g = 3 → a = d + k + 2) →
      tu ∈ emitList cl d k g a → tu.length = a ∧ ∀ x ∈ tu, x < nL cl + 1 := by
    intro g a tu hg0 h1 h2 h3 htu
    obtain ⟨e, he, hg, rfl⟩ := (mem_emitList cl d k).mp htu
    refine ⟨length_digitsOf _ _ _, fun x hx => ?_⟩
    rcases tagged cl d k he hg hg0 with ⟨rfl, j, hj, rfl⟩ | ⟨rfl, c, hc, rfl⟩ | ⟨rfl, t, ht, rfl⟩
    · have hf := fst_lt cl hj
      rw [h1 rfl, digits_one (by omega) (by unfold MM; omega)] at hx
      simp at hx; omega
    · rw [h2 rfl, ← length_key cl d c, digits_tagged (by omega) (fun x hx => key_lt cl d hx)] at hx
      simp only [key, List.mem_map] at hx
      obtain ⟨p, -, rfl⟩ := hx
      have := keyE_le cl c p; omega
    · obtain ⟨hl, hlt⟩ := lTuple_props cl d k ht
      rw [h3 rfl, ← hl, digits_tagged (by omega) hlt] at hx
      obtain ⟨c, hc, b, hb, ch, hs', rfl⟩ := (mem_lTuples cl d k).mp ht
      obtain ⟨-, h2', -⟩ := sim_sound cl d k c hs'
      rcases List.mem_append.mp hx with hx | hx
      · simp only [key, List.mem_map] at hx
        obtain ⟨p, -, rfl⟩ := hx
        have := keyE_le cl c p; omega
      · rcases mem_pad cl k hx with hx | rfl
        · obtain ⟨j, hj, rfl⟩ := h2' x hx; have := fst_lt cl hj; omega
        · omega
  rcases i with _ | _ | _ | _ | i
  · simp [tss] at ht; subst ht; simp [arities]
  · obtain ⟨h1, h2⟩ := ent (g := 1) (by omega) (fun _ => rfl) (by omega) (by omega) ht
    exact ⟨by simp [arities], by simpa [arities] using h1, h2⟩
  · obtain ⟨h1, h2⟩ := ent (g := 2) (by omega) (by omega) (fun _ => rfl) (by omega) ht
    exact ⟨by simp [arities], by simpa [arities] using h1, h2⟩
  · obtain ⟨h1, h2⟩ := ent (g := 3) (by omega) (by omega) (by omega) (fun _ => rfl) ht
    exact ⟨by simp [arities], by simpa [arities] using h1, h2⟩
  · simp [tss] at ht

/-- **The structure.** -/
def A : Structure where
  arities := arities d k
  size := nL cl + 1
  rel i := ((tss cl d k).getD i []).toFinset
  arity_pos := by intro a ha; simp [arities] at ha; omega
  wf := wf_tss cl d k

theorem encodes_structWord : Encodes (structWord cl d k) (A cl d k) := by
  refine encodes_wordOf (A cl d k) (tss cl d k) (by simp [tss, A, arities]) fun i hi => ⟨?_, rfl⟩
  simp only [A, arities, List.length_cons, List.length_nil] at hi
  rcases i with _ | _ | _ | _ | i
  · simp [tss]
  · exact nodup_emitList cl d k 1 1 (by omega) ⟨fun _ => rfl, by omega, by omega⟩
  · exact nodup_emitList cl d k 2 (d + 1) (by omega) ⟨by omega, fun _ => rfl, by omega⟩
  · exact nodup_emitList cl d k 3 (d + k + 2) (by omega) ⟨by omega, by omega, fun _ => rfl⟩
  · omega

/-! ### The relations -/

theorem rel0 {t : List ℕ} : t ∈ (A cl d k).rel 0 ↔ t = [nL cl] := by simp [A, tss]

theorem rel1 {u : ℕ} : [u] ∈ (A cl d k).rel 1 ↔ ∃ j < nL cl, u = fst cl j := by
  have hM := MM_pos cl
  simp only [A, tss, List.getD_cons_succ, List.getD_cons_zero, List.mem_toFinset]
  rw [mem_emitList]
  constructor
  · rintro ⟨e, he, hg, htu⟩
    rcases tagged cl d k he hg (by omega) with ⟨-, j, hj, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · refine ⟨j, hj, ?_⟩
      have hf := fst_lt cl hj
      rw [digits_one (by omega) (by unfold MM; omega)] at htu
      simpa using htu
    · omega
    · omega
  · rintro ⟨j, hj, rfl⟩
    have hf := fst_lt cl hj
    refine ⟨_, mem_hs_of_canon cl d k hj, by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)], ?_⟩
    have := digits_tagged (g := 1) (M := MM cl) (by omega) (tu := [fst cl j])
      (by simp; unfold MM; omega)
    simpa using this.symm

theorem rel2 {t : List ℕ} : t ∈ (A cl d k).rel 2 ↔ ∃ c < cl.length, t = key cl d c := by
  have hM := MM_pos cl
  simp only [A, tss, List.getD_cons_succ, List.getD_cons_zero, List.mem_toFinset]
  rw [mem_emitList]
  constructor
  · rintro ⟨e, he, hg, htu⟩
    rcases tagged cl d k he hg (by omega) with ⟨h, -⟩ | ⟨-, c, hc, rfl⟩ | ⟨h, -⟩
    · omega
    · refine ⟨c, hc, ?_⟩
      rwa [← length_key cl d c, digits_tagged (by omega) (fun x hx => key_lt cl d hx)] at htu
    · omega
  · rintro ⟨c, hc, rfl⟩
    refine ⟨_, mem_hs_of_key cl d k hc, by
      rw [nNum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)], ?_⟩
    rw [nNum, ← length_key cl d c, digits_tagged (by omega) (fun x hx => key_lt cl d hx)]

theorem rel3 {t : List ℕ} : t ∈ (A cl d k).rel 3 ↔ t ∈ lTuples cl d k := by
  have hM := MM_pos cl
  simp only [A, tss, List.getD_cons_succ, List.getD_cons_zero, List.mem_toFinset]
  rw [mem_emitList]
  constructor
  · rintro ⟨e, he, hg, htu⟩
    rcases tagged cl d k he hg (by omega) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, t', ht', rfl⟩
    · omega
    · omega
    · obtain ⟨hl, hlt⟩ := lTuple_props cl d k ht'
      rw [← hl, digits_tagged (by omega) hlt] at htu
      rw [htu]; exact ht'
  · intro ht
    obtain ⟨hl, hlt⟩ := lTuple_props cl d k ht
    refine ⟨_, mem_hs_of_lTuple cl d k ht, by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)], ?_⟩
    rw [← hl, digits_tagged (by omega) hlt]

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Struct
