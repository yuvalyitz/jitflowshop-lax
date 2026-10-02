import Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PMain

/-!
# The Layout of the Program

The scalars of the reader, of the setup of `Lemmas/WDToWSat` and of the new part; the arrays `a`,
`bo`, `U`, `od`, `bd1`, `vd1`, `bd2`, `vd2`. `ok_prog`: the program compiles under it. The pieces of
`Lemmas/WDToWSat` compile under that reduction's layout, and `Com.Ok` is monotone in the layout.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PLayout

open Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs (V bump seqList headCom fitCom boCom LCom uCom
  powCom noCom relCom atomCom codeCom ok_atomCom ok_codeCom ok_seqList)
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.Syntax
open Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PDefs

/-! ### Monotonicity of `Ok` -/

theorem Expr.Ok.mono {L L' : Layout} (hs : ∀ y ∈ L.scalars, y ∈ L'.scalars)
    (ha : ∀ a ∈ L.arrays, a ∈ L'.arrays) (ht : L.temps ≤ L'.temps) :
    ∀ (e : Expr) (d : ℕ), Expr.Ok L e d → Expr.Ok L' e d
  | .lit _, _, _ => trivial
  | .var x, _, h => hs x h
  | .get a i, d, h => ⟨ha a h.1, Expr.Ok.mono hs ha ht i d h.2.1, by have := h.2.2; omega⟩
  | .bin _ e f, d, h => ⟨Expr.Ok.mono hs ha ht f d h.1, Expr.Ok.mono hs ha ht e (d + 1) h.2.1,
      by have := h.2.2; omega⟩

theorem Com.Ok.mono {L L' : Layout} (hs : ∀ y ∈ L.scalars, y ∈ L'.scalars)
    (ha : ∀ a ∈ L.arrays, a ∈ L'.arrays) (ht : L.temps ≤ L'.temps) :
    ∀ c : Com, Com.Ok L c → Com.Ok L' c
  | .skip, _ => trivial
  | .assign x e, h => ⟨hs x h.1, Expr.Ok.mono hs ha ht e 0 h.2⟩
  | .store a i e, h => ⟨ha a h.1, Expr.Ok.mono hs ha ht i 0 h.2.1,
      Expr.Ok.mono hs ha ht e 1 h.2.2.1, by have := h.2.2.2; omega⟩
  | .seq c d, h => ⟨Com.Ok.mono hs ha ht c h.1, Com.Ok.mono hs ha ht d h.2⟩
  | .ite b c d, h => ⟨Expr.Ok.mono hs ha ht _ 0 h.1, Com.Ok.mono hs ha ht c h.2.1,
      Com.Ok.mono hs ha ht d h.2.2⟩
  | .while b c, h => ⟨Expr.Ok.mono hs ha ht _ 0 h.1, Com.Ok.mono hs ha ht c h.2⟩
  | .read x, h => hs x h
  | .write e, h => ⟨Expr.Ok.mono hs ha ht e 0 h.1, by have := h.2; omega⟩

/-! ### The layout -/

/-- The scalars of the new part. -/
def gScalars : List String :=
  ["g_NT", "g_M", "g_C", "g_k1", "g_W", "g_D", "g_DD", "g_C2", "g_WCQ", "g_P", "g_Q", "g_b", "g_e",
    "g_b1", "g_v1", "g_b2", "g_v2", "g_w", "g_cf", "g_i", "g_j", "g_j2", "g_fT", "g_fF", "g_und",
    "g_za", "g_zb"]

/-- **The layout.** -/
def layout : Layout :=
  ⟨Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars ++ gScalars,
    ["a", "bo", "U", "od", "bd1", "vd1", "bd2", "vd2"], 12⟩

theorem arrs_sub : ∀ a ∈ Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.layout.arrays,
    a ∈ layout.arrays := by
  intro a ha
  simp only [Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.layout, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  simp only [layout, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem of_w {c : Com} (h : Com.Ok Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.layout c) :
    Com.Ok layout c :=
  Com.Ok.mono (fun _ hy => List.mem_append_left _ hy) arrs_sub le_rfl c h

theorem ok_decG (arr w bs : String) (harr : arr ∈ layout.arrays) (hw : w ∈ layout.scalars)
    (hbs : bs ∈ layout.scalars) : ∀ j c, Com.Ok layout (decG arr w bs j c)
  | _, 0 => trivial
  | j, c + 1 => by
    refine ⟨?_, ?_, ok_decG arr w bs harr hw hbs (j + 1) c⟩ <;>
      simp_all [Com.Ok, Expr.Ok, layout]

theorem ok_powG (dst bs : String) (hd : dst ∈ layout.scalars) (hbs : bs ∈ layout.scalars) :
    ∀ e, Com.Ok layout (powG dst bs e)
  | 0 => ⟨hd, trivial⟩
  | e + 1 => by
    refine ⟨ok_powG dst bs hd hbs e, ?_⟩
    simp_all [Com.Ok, Expr.Ok, layout]

set_option maxHeartbeats 4000000 in
theorem ok_decCom : Com.Ok layout decCom := by
  simp [decCom, seqList, loopC, tBody, f1Body, f2Test, splitI, setIf, bump, layout, gScalars,
    Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok, Cond.Ok, Expr.Ok, condExpr]

theorem ok_evalCom : ∀ ψ : Formula, Com.Ok layout (evalCom ψ)
  | .rel i js => of_w (ok_atomCom (.rel i js))
  | .eq a c => of_w (ok_atomCom (.eq a c))
  | .setVar js => ⟨of_w (ok_codeCom js), ok_decCom⟩
  | .neg φ => ⟨ok_evalCom φ, by
      simp [layout, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok, Expr.Ok]⟩
  | .and φ ψ => ⟨ok_evalCom φ, by
      simp [layout, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Cond.Ok, Expr.Ok, condExpr],
      ok_evalCom ψ, trivial⟩
  | .or φ ψ => ⟨ok_evalCom φ, by
      simp [layout, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Cond.Ok, Expr.Ok, condExpr],
      trivial, ok_evalCom ψ⟩
  | .ex _ _ => by simp [evalCom, layout, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok,
      Expr.Ok]
  | .all _ _ => by simp [evalCom, layout, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok,
      Expr.Ok]

theorem ok_powSteps (v : String) (hv : v ∈ layout.scalars) :
    ∀ e, Com.Ok layout (Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.powSteps v e)
  | 0 => trivial
  | e + 1 => by
    refine ⟨ok_powSteps v hv e, ?_⟩
    simp_all [Com.Ok, Expr.Ok, layout, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars]

theorem ok_powCom (v : String) (hv : v ∈ layout.scalars) (e : ℕ) :
    Com.Ok layout (powCom v e) :=
  ⟨⟨hv, trivial⟩, ok_powSteps v hv e⟩

theorem mem_g {y : String} (h : y ∈ gScalars) : y ∈ layout.scalars :=
  List.mem_append_right _ h

theorem mem_w {y : String} (h : y ∈ Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars) :
    y ∈ layout.scalars :=
  List.mem_append_left _ h

set_option maxHeartbeats 4000000 in
theorem ok_constCom (D : ℕ) : Com.Ok layout (constCom D) := by
  refine ⟨?_, ?_, ok_powG _ _ (mem_g (by decide)) (mem_g (by decide)) D, ?_,
    ok_powG _ _ (mem_g (by decide)) (mem_g (by decide)) D, ?_⟩
  all_goals simp [layout, gScalars, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok,
    Expr.Ok, seqList]

set_option maxHeartbeats 4000000 in
theorem ok_phaseB : Com.Ok layout phaseB := by
  simp [phaseB, bBody, loopC, litE, bump, layout, gScalars,
    Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok, Cond.Ok, Expr.Ok, condExpr]

set_option maxHeartbeats 8000000 in
theorem ok_cfCom : Com.Ok layout cfCom := by
  simp [cfCom, cfTest, splitI, setIf, loopC, bump, layout, gScalars,
    Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok, Cond.Ok, Expr.Ok, condExpr]

theorem ok_decB (b bd : String) (hb : b ∈ layout.scalars) (hbd : bd ∈ layout.arrays) (D : ℕ) :
    Com.Ok layout (decB b bd D) :=
  ⟨⟨mem_g (by decide), hb⟩, ok_decG _ _ _ hbd (mem_g (by decide)) (mem_g (by decide)) 0 D⟩

theorem ok_decV (v vd : String) (hv : v ∈ layout.scalars) (hvd : vd ∈ layout.arrays) (D : ℕ) :
    Com.Ok layout (decV v vd D) :=
  ⟨⟨mem_g (by decide), hv⟩, ok_decG _ _ _ hvd (mem_g (by decide)) (mem_g (by decide)) 0 D⟩

set_option maxHeartbeats 8000000 in
theorem ok_phaseX (D : ℕ) : Com.Ok layout (phaseX D) := by
  have h1 := ok_decB "g_b1" "bd1" (mem_g (by decide)) (by decide) D
  have h2 := ok_decV "g_v1" "vd1" (mem_g (by decide)) (by decide) D
  have h3 := ok_decB "g_b2" "bd2" (mem_g (by decide)) (by decide) D
  have h4 := ok_decV "g_v2" "vd2" (mem_g (by decide)) (by decide) D
  have hc := ok_cfCom
  have hl1 : Com.Ok layout (loopC "g_e" "g_C" lit1) := by
    simp [loopC, lit1, litE, bump, layout, gScalars,
      Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok, Cond.Ok, Expr.Ok, condExpr]
  have hl2 : Com.Ok layout (loopC "g_e" "g_C" lit2) := by
    simp [loopC, lit2, litE, bump, layout, gScalars,
      Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok, Cond.Ok, Expr.Ok, condExpr]
  have hw : Com.Ok layout (.write (V "g_C2")) := ⟨mem_g (by decide), by decide⟩
  have hx2 : Com.Ok layout (xv2Body D) := ⟨h4, hc, hw, hl1, hl2, trivial⟩
  have hl : ∀ (x m : String) (c : Com), x ∈ layout.scalars → m ∈ layout.scalars →
      Com.Ok layout c → Com.Ok layout (loopC x m c) := by
    intro x m c hx hm hc
    exact ⟨⟨hx, trivial⟩, by simp_all [Cond.Ok, Expr.Ok, condExpr, layout], hc, hx,
      by simp_all [Expr.Ok, layout]⟩
  exact hl _ _ _ (mem_g (by decide)) (mem_g (by decide)) ⟨h1, hl _ _ _ (mem_g (by decide))
    (mem_g (by decide)) ⟨h2, hl _ _ _ (mem_g (by decide)) (mem_g (by decide)) ⟨h3,
      hl _ _ _ (mem_g (by decide)) (mem_g (by decide)) hx2⟩⟩⟩

set_option maxHeartbeats 8000000 in
theorem ok_phaseM (Dt : Data) : Com.Ok layout (phaseM Dt) := by
  have hl : ∀ (x m : String) (c : Com), x ∈ layout.scalars → m ∈ layout.scalars →
      Com.Ok layout c → Com.Ok layout (loopC x m c) := by
    intro x m c hx hm hc
    exact ⟨⟨hx, trivial⟩, by simp_all [Cond.Ok, Expr.Ok, condExpr, layout], hc, hx,
      by simp_all [Expr.Ok, layout]⟩
  have hlit : Com.Ok layout litM := by
    simp [litM, litE, layout, gScalars, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok,
      Cond.Ok, Expr.Ok, condExpr]
  have hzb : Com.Ok layout (mzbBody Dt) :=
    ⟨⟨mem_g (by decide), mem_g (by decide)⟩, ok_decG _ _ _ (by decide) (mem_g (by decide))
      (mem_w (by decide)) 0 Dt.q, ⟨mem_g (by decide), trivial⟩, ok_evalCom Dt.ψ, hlit, trivial⟩
  have hv : Com.Ok layout (mvBody Dt) :=
    ⟨ok_decV "g_v1" "vd1" (mem_g (by decide)) (by decide) Dt.D,
      hl _ _ _ (mem_g (by decide)) (mem_g (by decide)) hzb⟩
  have hb : Com.Ok layout (mbBody Dt) :=
    ⟨ok_decB "g_b1" "bd1" (mem_g (by decide)) (by decide) Dt.D,
      hl _ _ _ (mem_g (by decide)) (mem_g (by decide)) hv⟩
  have hza : Com.Ok layout (mzaBody Dt) :=
    ⟨⟨mem_g (by decide), mem_g (by decide)⟩, ok_decG _ _ _ (by decide) (mem_g (by decide))
      (mem_w (by decide)) Dt.q Dt.p, ⟨mem_g (by decide), by decide⟩,
      hl _ _ _ (mem_g (by decide)) (mem_g (by decide)) hb, trivial⟩
  exact hl _ _ _ (mem_g (by decide)) (mem_g (by decide)) hza

set_option maxHeartbeats 8000000 in
/-- **The program compiles.** -/
theorem ok_prog (Dt : Data) : Com.Ok layout (prog Dt) := by
  have h := Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.ok_prog (wd Dt)
  have hcount : Com.Ok layout countCom := by
    simp [countCom, layout, gScalars, Lax496464Proofs.WHierarchy.Lemmas.WDToWSat.ProgDefs.scalars, Com.Ok,
      Expr.Ok]
  refine ⟨of_w h.1, of_w h.2.1, of_w h.2.2.1,
    Expr.Ok.mono (fun y hy => List.mem_append_left _ hy) arrs_sub le_rfl _ 0 h.2.2.2.1, ?_,
    of_w h.2.2.2.2.2⟩
  exact ⟨of_w h.2.2.2.2.1.1, of_w h.2.2.2.2.1.2.1, of_w h.2.2.2.2.1.2.2.1,
    ok_powCom _ (mem_w (by decide)) _, ok_powCom _ (mem_g (by decide)) _,
    ok_powCom _ (mem_g (by decide)) _, ok_constCom _, hcount, ok_phaseB, ok_phaseX _,
    ok_phaseM _, ⟨mem_g (by decide), by decide⟩, trivial⟩

end Lax496464Proofs.WHierarchy.Lemmas.PiTwoToMonotone.PLayout
