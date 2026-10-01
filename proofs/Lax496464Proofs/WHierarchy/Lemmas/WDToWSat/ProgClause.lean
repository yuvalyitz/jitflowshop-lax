import Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom

/-!
# The clauses

`clauseCom_spec`: under the digits `ds` in `od`, `clauseCom C` writes `clauseWords D x ds C`, and
`clausesCom_spec` the words of a list of clauses. Built from the literals without `X` (`nonXCom`,
setting `w_st` when one holds) and the `X`-literals (`xLitCom`, writing the code of the tuple).
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgClause

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Cnf Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Digits
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Word Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.Output
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgMath
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgCtx Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgAtom

variable {D : Data} {x : List ℕ} {B : ℕ}

/-- The scalars the clauses assign. -/
def zS : List String := ["w_bs", "w_cnt", "w_f", "w_t", "w_mt", "w_st", "w_c"]

/-- The scalars the atoms assign. -/
def zA : List String := ["w_bs", "w_cnt", "w_f", "w_t", "w_mt"]

/-- The state inside an assignment. -/
def ZPre (D : Data) (x ds : List ℕ) (σ : Env) : Prop := Ctx D x σ ∧ σ.arrs "od" = ds

theorem ZPre.frame {ds : List ℕ} {σ σ' : Env} {S : List String} (h : ZPre D x ds σ)
    (hf : Frame S [] σ σ') (hS : "w_n" ∉ S) : ZPre D x ds σ' :=
  ⟨h.1.frame hf hS (by simp), by rw [hf.2.1 _ (by simp)]; exact h.2⟩

/-- What a literal of the CNF satisfies on a word that fits. -/
structure LitOk (D : Data) (x : List ℕ) (l : Lit) : Prop where
  rel : ∀ i js, l.atom = .rel i js → i < spW x ∧ js.length = x.getD (1 + i) 0
  set : ∀ js, l.atom = .setVar js → js.length = D.s
  idx : ∀ j ∈ l.atom.idxs, j < D.r

/-! ### Frames by syntax -/

theorem wvars_matchCom (l : ℕ) : ∀ (js : List ℕ) (q : ℕ) (y : String),
    y ∈ (matchCom l js q).wvars → y = "w_mt"
  | [], _, y, h => by simp [matchCom] at h
  | j :: js, q, y, h => by
    simp only [matchCom, Com.wvars, List.mem_append, List.nil_append, List.mem_singleton]
      at h
    rcases h with h | h
    · exact h
    · exact wvars_matchCom l js (q + 1) y h

theorem warrs_matchCom (l : ℕ) : ∀ (js : List ℕ) (q : ℕ), (matchCom l js q).warrs = []
  | [], _ => rfl
  | j :: js, q => by simp [matchCom, Com.warrs, warrs_matchCom l js (q + 1)]

theorem reads_matchCom (l : ℕ) : ∀ (js : List ℕ) (q : ℕ), ¬ (matchCom l js q).reads
  | [], _ => by simp [matchCom]
  | j :: js, q => by simp [matchCom, Com.reads, reads_matchCom l js (q + 1)]

theorem noWrite_matchCom (l : ℕ) : ∀ (js : List ℕ) (q : ℕ), (matchCom l js q).NoWrite
  | [], _ => by simp [matchCom, Com.NoWrite]
  | j :: js, q => ⟨by simp [Com.NoWrite], noWrite_matchCom l js (q + 1)⟩

theorem atom_frame (a : Atom) :
    (∀ y ∈ (atomCom a).wvars, y ∈ zA) ∧ (∀ b ∈ (atomCom a).warrs, b ∈ ([] : List String)) ∧
      ¬ (atomCom a).reads ∧ (atomCom a).NoWrite := by
  cases a with
  | rel i js =>
    refine ⟨fun y hy => ?_, fun b hb => ?_, ?_, ?_⟩
    · simp only [atomCom, relCom, tupLoop, tupBody, Com.wvars, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hy
      have := wvars_matchCom js.length js 0 y
      simp only [zA, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    · simp [atomCom, relCom, tupLoop, tupBody, Com.warrs, warrs_matchCom] at hb
    · simp [atomCom, relCom, tupLoop, tupBody, Com.reads, reads_matchCom]
    · simp [atomCom, relCom, tupLoop, tupBody, Com.NoWrite, noWrite_matchCom]
  | eq a b => refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [atomCom, Com.wvars, Com.warrs, Com.reads, zA,
      Com.NoWrite]
  | setVar js => refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [atomCom, Com.NoWrite]

/-! ### The equation atom -/

set_option maxHeartbeats 1000000 in
theorem eqCom_value (hB : BF D x B) {ds : List ℕ} (hds : DsOk D x ds) {a b : ℕ} (ha : a < D.r)
    (hb : b < D.r) :
    Spec B (ZPre D x ds) (atomCom (.eq a b))
      (fun _ σ' => σ'.vars "w_f" = if epsW D x ds a = epsW D x ds b then 1 else 0) 12 := by
  have hlen := hB.len
  have hnB := hB.n
  have haB : a < B := by have := hB.const; unfold cD at this; omega
  have hbB : b < B := by have := hB.const; unfold cD at this; omega
  have hda := hds.getD_lt ha
  have hdb := hds.getD_lt hb
  refine Spec.pre (P := fun σ => ZPre D x ds σ ∧
      a < (σ.arrs "od").length ∧ b < (σ.arrs "od").length ∧
      (σ.arrs "od").getD a 0 < (σ.arrs "U").length ∧ (σ.arrs "od").getD b 0 < (σ.arrs "U").length ∧
      (σ.arrs "od").getD a 0 < B ∧ (σ.arrs "od").getD b 0 < B ∧
      (σ.arrs "U").getD ((σ.arrs "od").getD a 0) 0 = epsW D x ds a ∧
      (σ.arrs "U").getD ((σ.arrs "od").getD b 0) 0 = epsW D x ds b ∧
      epsW D x ds a < B ∧ epsW D x ds b < B) ?_ ?_
  · unfold atomCom
    run_vcg
    · have hcase := ‹(σ.arrs "U").getD ((σ.arrs "od").getD a 0) 0 =
        (σ.arrs "U").getD ((σ.arrs "od").getD b 0) 0›
      rw [‹(σ.arrs "U").getD ((σ.arrs "od").getD a 0) 0 = epsW D x ds a›,
        ‹(σ.arrs "U").getD ((σ.arrs "od").getD b 0) 0 = epsW D x ds b›] at hcase
      simp [Env.setVar, hcase]
    · have hcase := ‹¬(σ.arrs "U").getD ((σ.arrs "od").getD a 0) 0 =
        (σ.arrs "U").getD ((σ.arrs "od").getD b 0) 0›
      rw [‹(σ.arrs "U").getD ((σ.arrs "od").getD a 0) 0 = epsW D x ds a›,
        ‹(σ.arrs "U").getD ((σ.arrs "od").getD b 0) 0 = epsW D x ds b›] at hcase
      simp [Env.setVar, hcase]
  · rintro σ ⟨hc, hod⟩
    have hUl := hc.Ulen
    refine ⟨⟨hc, hod⟩, by rw [hc.odlen]; exact ha, by rw [hc.odlen]; exact hb,
      by rw [hod]; omega, by rw [hod]; omega, by rw [hod]; omega, by rw [hod]; omega,
      elem_read hc hod hds ha, elem_read hc hod hds hb, U_getD_lt hB _, U_getD_lt hB _⟩

/-! ### Literals without `X` -/

/-- The truth of the atom, as the scan computes it. -/
def atomVal (D : Data) (x ds : List ℕ) : Atom → Prop
  | .rel i js => memW x i (js.map (epsW D x ds))
  | .eq a b => epsW D x ds a = epsW D x ds b
  | .setVar _ => False

instance (D : Data) (x ds : List ℕ) (a : Atom) : Decidable (atomVal D x ds a) := by
  cases a <;> unfold atomVal <;> infer_instance

/-- The cost bound of a literal. -/
def Klit (x : List ℕ) (l : Lit) : ℕ := Krel x l.atom.idxs + 30

theorem atomCom_value (hB : BF D x B) (hg : Good x) {ds : List ℕ} (hds : DsOk D x ds) (l : Lit)
    (hl : LitOk D x l) (hX : isXLit l = false) :
    Spec B (ZPre D x ds) (atomCom l.atom)
      (fun _ σ' => σ'.vars "w_f" = if atomVal D x ds l.atom then 1 else 0) (Krel x l.atom.idxs) := by
  obtain ⟨pos, atom⟩ := l
  cases atom with
  | rel i js =>
    obtain ⟨hi, hjl⟩ := hl.rel i js rfl
    exact (relCom_value hB hg hds hi hjl fun j hj => hl.idx j hj).pre fun σ h => h
  | eq a b =>
    exact (eqCom_value hB hds (hl.idx a (by simp [Atom.idxs])) (hl.idx b (by simp [Atom.idxs]))).mono
      (by unfold Krel; omega)
  | setVar js => simp [isXLit] at hX

theorem nonXVal_eq (D : Data) (x ds : List ℕ) (l : Lit) (hX : isXLit l = false) :
    nonXVal x (epsW D x ds) l = decide (atomVal D x ds l.atom = (l.pos = true)) := by
  obtain ⟨pos, atom⟩ := l
  cases atom with
  | rel i js => cases pos <;> simp [nonXVal, atomVal]
  | eq a b => cases pos <;> simp [nonXVal, atomVal]
  | setVar js => simp [isXLit] at hX

set_option maxHeartbeats 1000000 in
theorem nonXCom_spec (hB : BF D x B) (hg : Good x) {ds : List ℕ} (hds : DsOk D x ds) (l : Lit)
    (hl : LitOk D x l) (hX : isXLit l = false) :
    Spec B (ZPre D x ds) (nonXCom l)
      (fun σ σ' => σ'.vars "w_st" = (if nonXVal x (epsW D x ds) l then 1 else σ.vars "w_st") ∧
        Frame zS [] σ σ' ∧ σ'.out = σ.out) (Klit x l) := by
  have hat := Spec.framedOut (atomCom_value hB hg hds l hl hX) zA [] (atom_frame l.atom).1
    (atom_frame l.atom).2.1 (atom_frame l.atom).2.2.1 (atom_frame l.atom).2.2.2
  have hlen := hB.len
  have hite : Spec B (fun τ => τ.vars "w_f" ≤ 1) (.ite (.eq (V "w_f") (.lit (bv l.pos)))
      (.assign "w_st" (.lit 1)) .skip)
      (fun τ τ' => τ'.vars "w_st" = (if τ.vars "w_f" = bv l.pos then 1 else τ.vars "w_st") ∧
        Frame zS [] τ τ' ∧ τ'.out = τ.out) 6 := by
    have hbv : bv l.pos ≤ 1 := by unfold bv; split_ifs <;> omega
    run_vcg
    · refine ⟨by simp [Env.setVar, ‹σ.vars "w_f" = bv l.pos›], Frame.setVar σ (by simp [zS]) _, rfl⟩
    · refine ⟨by simp [‹¬σ.vars "w_f" = bv l.pos›], Frame.refl _ _ _, rfl⟩
  intro σ hσ
  obtain ⟨σ1, hr1, e1, f1, o1⟩ := hat σ hσ
  have hf1 : σ1.vars "w_f" ≤ 1 := by rw [e1]; split_ifs <;> omega
  obtain ⟨σ2, hr2, e2, f2, o2⟩ := hite σ1 hf1
  refine ⟨σ2, (hr1.seq hr2).mono (by unfold Klit; omega), ?_,
    (f1.mono (by simp [zA, zS]) (by simp)).trans f2, o2.trans o1⟩
  rw [e2, e1, f1.1 _ (by simp [zA]), nonXVal_eq D x ds l hX]
  by_cases hv : atomVal D x ds l.atom
  · rw [if_pos hv]
    cases hp : l.pos <;> simp [bv, hv]
  · rw [if_neg hv]
    cases hp : l.pos <;> simp [bv, hv]

/-- **The literals without `X`.** -/
theorem nonXs_spec (hB : BF D x B) (hg : Good x) {ds : List ℕ} (hds : DsOk D x ds) :
    ∀ Ls : List Lit, (∀ l ∈ Ls, LitOk D x l ∧ isXLit l = false) →
    Spec B (ZPre D x ds) (seqList (Ls.map nonXCom))
      (fun σ σ' => σ'.vars "w_st" =
          (if Ls.any (nonXVal x (epsW D x ds)) then 1 else σ.vars "w_st") ∧
        Frame zS [] σ σ' ∧ σ'.out = σ.out) ((Ls.map (Klit x)).sum + 1)
  | [], _ => by
    refine Spec.mono ((Spec.skip (B := B) (P := ZPre D x ds)).post fun σ σ' _ h => ?_) (by simp)
    subst h; exact ⟨by simp, Frame.refl _ _ _, rfl⟩
  | l :: Ls, h => by
    have h1 := nonXCom_spec hB hg hds l (h l (by simp)).1 (h l (by simp)).2
    have h2 := nonXs_spec hB hg hds Ls fun l' hl' => h l' (by simp [hl'])
    refine Spec.mono (Spec.seq h1 h2 (fun σ σ' hp hq => hp.frame hq.2.1 (by simp [zS])) ?_)
      (by simp; omega)
    rintro σ σ' σ'' - ⟨e1, f1, o1⟩ ⟨e2, f2, o2⟩
    refine ⟨?_, f1.trans f2, o2.trans o1⟩
    rw [e2, e1]
    simp only [List.any_cons, Bool.or_eq_true]
    by_cases ha : nonXVal x (epsW D x ds) l = true
    · simp [ha]
    · rw [if_neg ha]
      by_cases hb : Ls.any (nonXVal x (epsW D x ds)) = true <;> simp [hb, ha]

set_option maxHeartbeats 1000000 in
theorem codeStep_spec (hB : BF D x B) {ds : List ℕ} (hds : DsOk D x ds) {j c0 : ℕ} (hj : j < D.r)
    (hval : ds.getD j 0 + nW D x * c0 < B) :
    Spec B (fun σ => ZPre D x ds σ ∧ σ.vars "w_c" = c0)
      (.assign "w_c" (.add (.get "od" (.lit j)) (.mul (V "w_n") (V "w_c"))))
      (fun σ σ' => σ'.vars "w_c" = ds.getD j 0 + nW D x * c0 ∧ Frame zS [] σ σ' ∧
        σ'.out = σ.out) 7 := by
  have hlen := hB.len
  have hnB := hB.n
  have hjB : j < B := by have := hB.const; unfold cD at this; omega
  refine Spec.pre (P := fun σ => (ZPre D x ds σ ∧ σ.vars "w_c" = c0) ∧
      j < (σ.arrs "od").length ∧ (σ.arrs "od").getD j 0 = ds.getD j 0 ∧
      (σ.arrs "od").getD j 0 + σ.vars "w_n" * σ.vars "w_c" < B ∧ σ.vars "w_n" < B ∧
      σ.vars "w_c" < B ∧ σ.vars "w_n" * σ.vars "w_c" = nW D x * c0) ?_ ?_
  · run_vcg
    refine ⟨?_, Frame.setVar σ (by simp [zS]) _, rfl⟩
    simp only [Env.setVar, if_pos]
    rw [‹(σ.arrs "od").getD j 0 = ds.getD j 0›, ‹σ.vars "w_n" * σ.vars "w_c" = nW D x * c0›]
  · rintro σ ⟨⟨hc, hod⟩, hc0⟩
    have hn := hc.n
    have hmul : nW D x * c0 ≤ ds.getD j 0 + nW D x * c0 := by omega
    refine ⟨⟨⟨hc, hod⟩, hc0⟩, by rw [hc.odlen]; exact hj, by rw [hod], ?_, by rw [hn]; omega,
      ?_, by rw [hn, hc0]⟩
    · rw [hod, hn, hc0]; exact hval
    · rw [hc0]
      rcases Nat.eq_zero_or_pos (nW D x) with h0 | h0
      · have := hds.getD_lt hj; omega
      · have : c0 ≤ nW D x * c0 := Nat.le_mul_of_pos_left c0 h0
        omega

theorem digit_step_lt {n d c e : ℕ} (hd : d < n) (hc : c < n ^ e) : d + n * c < n ^ (e + 1) := by
  rw [pow_succ]
  have : n * c + n ≤ n * n ^ e := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hc
  nlinarith

/-- **The code of a tuple of positions.** -/
theorem codeCom_spec (hB : BF D x B) {ds : List ℕ} (hds : DsOk D x ds) :
    ∀ js : List ℕ, (∀ j ∈ js, j < D.r) → js.length ≤ D.s →
    Spec B (ZPre D x ds) (codeCom js)
      (fun σ σ' => σ'.vars "w_c" = codeOf (nW D x) (js.map fun j => ds.getD j 0) ∧
        Frame zS [] σ σ' ∧ σ'.out = σ.out) (7 * js.length + 2)
  | [], _, _ => by
    have hlen := hB.len
    refine (Spec.assign (P := ZPre D x ds) (x := "w_c") (e := .lit 0) (f := fun _ => 0)
      fun σ _ => evalB_lit (by omega)).post fun σ σ' _ h => ?_
    subst h
    exact ⟨by simp [codeOf], Frame.setVar σ (by simp [zS]) _, rfl⟩
  | j :: js, hj, hl => by
    have hlt : codeOf (nW D x) (js.map fun j => ds.getD j 0) < nW D x ^ js.length := by
      have := codeOf_lt (n := nW D x) (js.map fun j => ds.getD j 0) fun d hd => by
        obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
        exact hds.getD_lt (hj j' (by simp [hj']))
      simpa using this
    have hjr : j < D.r := hj j (by simp)
    have hval : ds.getD j 0 + nW D x * codeOf (nW D x) (js.map fun j => ds.getD j 0) < B := by
      have h1 := digit_step_lt (hds.getD_lt hjr) hlt
      have h2 := hB.npow_lt (e := js.length + 1) (by simp at hl; omega)
      omega
    have h1 := codeCom_spec hB hds js (fun j' hj' => hj j' (by simp [hj'])) (by simp at hl; omega)
    have h2 := codeStep_spec hB hds hjr hval
    refine Spec.mono (Spec.seq h1 h2 (fun σ σ' hp hq => ⟨hp.frame hq.2.1 (by simp [zS]), hq.1⟩) ?_)
      (by simp; omega)
    rintro σ σ' σ'' - ⟨e1, f1, o1⟩ ⟨e2, f2, o2⟩
    exact ⟨by rw [e2]; simp [codeOf], f1.trans f2, o2.trans o1⟩

set_option maxHeartbeats 1000000 in
theorem writeCode_spec (hB : BF D x B) {c b : ℕ} (hc : 2 * c + 1 < B) (hb : b ≤ 1) :
    Spec B (fun σ => σ.vars "w_c" = c) (.write (.add (.mul (.lit 2) (V "w_c")) (.lit b)))
      (fun σ σ' => σ'.out = σ.out ++ [2 * c + b] ∧ Frame zS [] σ σ') 6 := by
  have hlen := hB.len
  run_vcg
  refine ⟨by rw [‹σ.vars "w_c" = c›], Frame.refl _ _ _⟩

/-- **An `X`-literal.** -/
theorem xLitCom_spec (hB : BF D x B) {ds : List ℕ} (hds : DsOk D x ds) (l : Lit)
    (hl : LitOk D x l) (hX : isXLit l = true) :
    Spec B (ZPre D x ds) (xLitCom l)
      (fun σ σ' => σ'.out = σ.out ++ [2 * codeW D x ds l + (1 - bv l.pos)] ∧ Frame zS [] σ σ')
      (7 * l.atom.idxs.length + 8) := by
  obtain ⟨pos, atom⟩ := l
  cases atom with
  | rel i js => simp [isXLit] at hX
  | eq a b => simp [isXLit] at hX
  | setVar js =>
    have hjs : js.length = D.s := hl.set js rfl
    have hcode : codeW D x ds ⟨pos, .setVar js⟩ < nW D x ^ D.s := by
      have := codeOf_lt (n := nW D x) (js.map fun j => ds.getD j 0) fun d hd => by
        obtain ⟨j', hj', rfl⟩ := List.mem_map.mp hd
        exact hds.getD_lt (hl.idx j' (by simpa [Atom.idxs] using hj'))
      simpa [codeW, Atom.idxs, hjs] using this
    have hcnt := hB.count_lt.2
    have h1 := codeCom_spec hB hds js (fun j hj => hl.idx j (by simpa [Atom.idxs] using hj))
      (by omega)
    have h2 := writeCode_spec hB (c := codeW D x ds ⟨pos, .setVar js⟩) (b := 1 - bv pos)
      (by omega) (by omega)
    refine Spec.mono (Spec.seq h1 h2 (fun σ σ' _ hq => by rw [hq.1]; rfl) ?_) (by simp [Atom.idxs])
    rintro σ σ' σ'' - ⟨-, f1, o1⟩ ⟨o2, f2⟩
    exact ⟨by rw [o2, o1], f1.trans f2⟩

/-- **The `X`-literals.** -/
theorem xLits_spec (hB : BF D x B) {ds : List ℕ} (hds : DsOk D x ds) :
    ∀ Ls : List Lit, (∀ l ∈ Ls, LitOk D x l ∧ isXLit l = true) →
    Spec B (ZPre D x ds) (seqList (Ls.map xLitCom))
      (fun σ σ' => σ'.out = σ.out ++ Ls.map (fun l => 2 * codeW D x ds l + (1 - bv l.pos)) ∧
        Frame zS [] σ σ') ((Ls.map fun l => 7 * l.atom.idxs.length + 8).sum + 1)
  | [], _ => by
    refine Spec.mono ((Spec.skip (B := B) (P := ZPre D x ds)).post fun σ σ' _ h => ?_) (by simp)
    subst h; exact ⟨by simp, Frame.refl _ _ _⟩
  | l :: Ls, h => by
    have h1 := xLitCom_spec hB hds l (h l (by simp)).1 (h l (by simp)).2
    have h2 := xLits_spec hB hds Ls fun l' hl' => h l' (by simp [hl'])
    refine Spec.mono (Spec.seq h1 h2 (fun σ σ' hp hq => hp.frame hq.2 (by simp [zS])) ?_)
      (by simp; omega)
    rintro σ σ' σ'' - ⟨o1, f1⟩ ⟨o2, f2⟩
    exact ⟨by rw [o2, o1]; simp, f1.trans f2⟩

end Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgClause
