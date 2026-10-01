import Lax496464Proofs.WHierarchy.Machine.ReadTape

/-! # Negation elimination: the IMP+ program

After `readTape` (array `a` = the word `x`, `rt_n = |x|`) the program runs these phases.

*Reading and compressing the structure.*
1. `header`: `s := a[0]`, `N := a[1 + s]`;
2. `entPass`: copies all entries of all tuples into the array `E` (`T` of them); leaves `p` at the
   start of the formula, saved as `F0`;
3. `foPass`: `fo[q] = 1` iff `E[q]` does not occur before position `q`;
4. `rkPass`: `R[t]` = the number of distinct entries below `E[t]` (the rank);
5. `Mcom`: `M := min N (T + |x|)`, the size of the compressed universe.

*Writing the expanded structure.*
6. `hdOut`: the vocabulary `2, (r, r, r, 2r, 1)` per symbol, and `M`;
7. `ltOut`: the pairs `u < v < M`;
8. `symPass`: per symbol (tuples `R[o …]`): the relation itself (`copyBlock`), the first tuple
   (`fBlock`, a scan with the lexicographic comparison `cmp`), the last tuple (`lBlock`), the pairs
   of consecutive tuples (`sBlock`, with `succFind`), and `Z` (`zBlock`).

*Writing the formula.*
9. `mxPass`: `bb := 1 + max a`, the first fresh variable;
10. `qOut`: the block `∃ bb … ∃ bb + K - 1`, `K = 2 (|x| - F0)`;
11. `trPass`: walks the prefix code with a stack `st` of polarities and writes the translation,
    fresh variables counted by `fc`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs

open Lean Elab Tactic Meta in
/-- `find_hyp h : pat` renames the most recent hypothesis whose type matches `pat` to `h`, and fails
(so that `first` can move on) if there is none. -/
elab "find_hyp " h:ident " : " pat:term : tactic => withMainContext do
  let ctx ← getLCtx
  let decls := ctx.decls.toArray.filterMap id |>.reverse
  for d in decls do
    if d.isImplementationDetail then continue
    let s ← saveState
    try
      let p ← Term.elabTerm pat none
      Term.synthesizeSyntheticMVarsNoPostponing
      if ← isDefEq p d.type then
        let g ← getMainGoal
        let g' ← g.rename d.fvarId h.getId
        replaceMainGoal [g']
        return
      else
        s.restore
    catch _ => s.restore
  throwError "find_hyp: no hypothesis matches"

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))
abbrev A (e : Expr) : Expr := .get "a" e
abbrev L (n : ℕ) : Expr := .lit n

/-- Write the values of a list of expressions. -/
def writes : List Expr → Com
  | [] => .skip
  | e :: es => .seq (.write e) (writes es)

/-- A counted loop `x := 0; while x < m do body`. -/
def loop (x m : String) (body : Com) : Com := .seq (.assign x (L 0)) (.while (.lt (V x) (V m)) body)

/-! ### 1–5: reading and compressing the structure -/

def header : Com := .seq (.assign "s" (A (L 0))) (.assign "N" (A (.add (L 1) (V "s"))))

def entIn : Com :=
  .seq (.store "E" (V "T") (A (.add (.add (V "p") (L 1)) (V "k")))) (.seq (bump "T") (bump "k"))

def entBody : Com :=
  .seq (.assign "c" (A (V "p")))
  (.seq (.assign "cr" (.mul (V "c") (A (.add (L 1) (V "i")))))
  (.seq (loop "k" "cr" entIn)
  (.seq (.assign "p" (.add (.add (V "p") (L 1)) (V "cr")))
  (bump "i"))))

def entPass : Com :=
  .seq (.assign "T" (L 0)) (.seq (.assign "p" (.add (L 2) (V "s"))) (loop "i" "s" entBody))

def foIn : Com :=
  .seq (.ite (.eq (.get "E" (V "q2")) (.get "E" (V "q"))) (.assign "f" (L 0)) .skip) (bump "q2")

def foBody : Com :=
  .seq (.assign "f" (L 1)) (.seq (loop "q2" "q" foIn) (.seq (.store "fo" (V "q") (V "f")) (bump "q")))

def foPass : Com := loop "q" "T" foBody

def rkIn : Com :=
  .seq (.ite (.lt (.get "E" (V "q")) (.get "E" (V "t")))
    (.assign "cn" (.add (V "cn") (.get "fo" (V "q")))) .skip) (bump "q")

def rkBody : Com :=
  .seq (.assign "cn" (L 0)) (.seq (loop "q" "T" rkIn) (.seq (.store "R" (V "t") (V "cn")) (bump "t")))

def rkPass : Com := loop "t" "T" rkBody

def Mcom : Com :=
  .seq (.assign "M" (V "N"))
    (.ite (.lt (.add (V "T") (V "rt_n")) (V "N")) (.assign "M" (.add (V "T") (V "rt_n"))) .skip)

/-! ### 6–8: the expanded structure -/

def hdBody : Com :=
  .seq (.assign "r" (A (.add (L 1) (V "i"))))
    (.seq (writes [V "r", V "r", V "r", .mul (L 2) (V "r"), L 1]) (bump "i"))

def hdOut : Com :=
  .seq (writes [.add (.mul (L 5) (V "s")) (L 1), L 2]) (.seq (loop "i" "s" hdBody) (.write (V "M")))

def ltIn : Com := .seq (.ite (.lt (V "u") (V "v")) (writes [V "u", V "v"]) .skip) (bump "v")

def ltBody : Com := .seq (loop "v" "M" ltIn) (bump "u")

def ltOut : Com :=
  .seq (.write (.div (.mul (V "M") (.sub (V "M") (L 1))) (L 2))) (loop "u" "M" ltBody)

/-- One step of the lexicographic comparison of the tuples at `x1` and `x2` of `R`. -/
def cmpStep : Com :=
  .ite (.eq (V "dd") (L 0))
    (.ite (.lt (.get "R" (.add (V "x1") (V "l1"))) (.get "R" (.add (V "x2") (V "l1"))))
      (.seq (.assign "dd" (L 1)) (.assign "lt" (L 1)))
      (.ite (.lt (.get "R" (.add (V "x2") (V "l1"))) (.get "R" (.add (V "x1") (V "l1"))))
        (.assign "dd" (L 1)) .skip))
    .skip

/-- **The comparison**: `lt := 1` iff the tuple of length `r` at `x1` is below the one at `x2`. -/
def cmpC : Com :=
  .seq (.assign "dd" (L 0)) (.seq (.assign "lt" (L 0)) (loop "l1" "r" (.seq cmpStep (bump "l1"))))

/-- Write `R[g], …, R[g + nn - 1]`. -/
def wR : Com := loop "l2" "nn" (.seq (.write (.get "R" (.add (V "g") (V "l2")))) (bump "l2"))

/-- Write the tuple starting at `R[e]`. -/
def wTup (e : Expr) : Com := .seq (.assign "g" e) (.seq (.assign "nn" (V "r")) wR)

abbrev tupAt (j : String) : Expr := .add (V "o") (.mul (V j) (V "r"))

def copyBlock : Com :=
  .seq (.write (V "c")) (.seq (.assign "g" (V "o")) (.seq (.assign "nn" (.mul (V "c") (V "r"))) wR))

def minBody : Com :=
  .seq (.assign "x1" (tupAt "j")) (.seq (.assign "x2" (tupAt "bs"))
    (.seq cmpC (.seq (.ite (.eq (V "lt") (L 1)) (.assign "bs" (V "j")) .skip) (bump "j"))))

def maxBody : Com :=
  .seq (.assign "x1" (tupAt "bs")) (.seq (.assign "x2" (tupAt "j"))
    (.seq cmpC (.seq (.ite (.eq (V "lt") (L 1)) (.assign "bs" (V "j")) .skip) (bump "j"))))

def minFind : Com := .seq (.assign "bs" (L 0)) (loop "j" "c" minBody)

def maxFind : Com := .seq (.assign "bs" (L 0)) (loop "j" "c" maxBody)

def fBlock : Com := .ite (.eq (V "c") (L 0)) (.write (L 0))
  (.seq (.write (L 1)) (.seq minFind (wTup (tupAt "bs"))))

def lBlock : Com := .ite (.eq (V "c") (L 0)) (.write (L 0))
  (.seq (.write (L 1)) (.seq maxFind (wTup (tupAt "bs"))))

def sfInner : Com :=
  .ite (.eq (V "fd") (L 0)) (.seq (.assign "bs" (V "w")) (.assign "fd" (L 1)))
    (.seq (.assign "x1" (tupAt "w")) (.seq (.assign "x2" (tupAt "bs"))
      (.seq cmpC (.ite (.eq (V "lt") (L 1)) (.assign "bs" (V "w")) .skip))))

def sfBody : Com :=
  .seq (.assign "x1" (tupAt "js")) (.seq (.assign "x2" (tupAt "w"))
    (.seq cmpC (.seq (.ite (.eq (V "lt") (L 1)) sfInner .skip) (bump "w"))))

/-- The successor of tuple `js`: `fd = 1` and its index in `bs`, if any. -/
def succFind : Com := .seq (.assign "fd" (L 0)) (.seq (.assign "bs" (L 0)) (loop "w" "c" sfBody))

def sBody : Com :=
  .seq succFind (.seq (.ite (.eq (V "fd") (L 1)) (.seq (wTup (tupAt "js")) (wTup (tupAt "bs"))) .skip)
    (bump "js"))

def sBlock : Com := .seq (.write (.sub (V "c") (L 1))) (loop "js" "c" sBody)

def zBlock : Com := .ite (.eq (V "c") (L 0))
  (.seq (.write (V "M")) (loop "u" "M" (.seq (.write (V "u")) (bump "u")))) (.write (L 0))

/-- The five blocks of one symbol. -/
def symW : Com := .seq copyBlock (.seq fBlock (.seq lBlock (.seq sBlock zBlock)))

def symBody : Com :=
  .seq (.assign "c" (A (V "p"))) (.seq (.assign "r" (A (.add (L 1) (V "i"))))
  (.seq symW (.seq (.assign "o" (.add (V "o") (.mul (V "c") (V "r"))))
  (.seq (.assign "p" (.add (.add (V "p") (L 1)) (.mul (V "c") (V "r")))) (bump "i")))))

def symPass : Com := .seq (.assign "o" (L 0)) (.seq (.assign "p" (.add (L 2) (V "s"))) (loop "i" "s" symBody))

/-! ### 9–11: the formula -/

def mxBody : Com := .seq (.ite (.lt (V "mx") (A (V "t2"))) (.assign "mx" (A (V "t2"))) .skip) (bump "t2")

def mxPass : Com :=
  .seq (.assign "mx" (L 0)) (.seq (loop "t2" "rt_n" mxBody) (.assign "bb" (.add (V "mx") (L 1))))

def qBody : Com := .seq (writes [L 6, .add (V "bb") (V "v")]) (bump "v")

def qOut : Com :=
  .seq (.assign "KK" (.mul (L 2) (.sub (V "rt_n") (V "F0")))) (loop "v" "KK" qBody)

/-- Write `wg + l` (if `wk ≠ 0`) or `a[wg + l]` (if `wk = 0`) for `l < wn`. -/
def wseq : Com :=
  loop "wl" "wn" (.seq (.ite (.eq (V "wk") (L 0)) (.write (A (.add (V "wg") (V "wl"))))
    (.write (.add (V "wg") (V "wl")))) (bump "wl"))

def elems : Com :=
  .seq (.ite (.eq (V "k1") (L 0)) (.assign "e1" (A (.add (V "g1") (V "ll"))))
    (.assign "e1" (.add (V "g1") (V "ll"))))
  (.ite (.eq (V "k2") (L 0)) (.assign "e2" (A (.add (V "g2") (V "ll"))))
    (.assign "e2" (.add (V "g2") (V "ll"))))

def lexBody : Com :=
  .seq elems (.seq (writes [L 5, L 0, L 0, L 2, V "e1", V "e2", L 4, L 2, V "e1", V "e2"])
    (bump "ll"))

/-- The code of `ȳ <ₗ z̄` for the two sequences described by `k1, g1` and `k2, g2`, of length
`ln ≥ 1`. -/
def lexCom : Com :=
  .seq (.assign "lm" (.sub (V "ln") (L 1))) (.seq (loop "ll" "lm" lexBody)
    (.seq elems (writes [L 0, L 0, L 2, V "e1", V "e2"])))

/-- Set up and run `wseq`. -/
def wseqOf (k : ℕ) (g n : Expr) : Com :=
  .seq (.assign "wk" (L k)) (.seq (.assign "wg" g) (.seq (.assign "wn" n) wseq))

/-- Set up and run `lexCom`. -/
def lexOf (k1 : ℕ) (g1 : Expr) (k2 : ℕ) (g2 : Expr) : Com :=
  .seq (.assign "k1" (L k1)) (.seq (.assign "g1" g1)
    (.seq (.assign "k2" (L k2)) (.seq (.assign "g2" g2) lexCom)))

abbrev Y0 : Expr := .add (V "p") (L 3)
abbrev FV : Expr := .add (V "fc") (V "ln")
abbrev RI (k : ℕ) : Expr := .add (.mul (L 5) (V "ri")) (L k)

/-- The code of the positive formula replacing `¬R_i ȳ` (with `ȳ` of length `ln ≥ 1`). -/
def negBig : Com :=
  .seq (writes [L 5, L 0, RI 5, L 1, A Y0, L 5, L 4, L 0, RI 2, V "ln"])
  (.seq (wseqOf 1 (V "fc") (V "ln"))
  (.seq (lexOf 0 Y0 1 (V "fc"))
  (.seq (writes [L 5, L 4, L 0, RI 4, .mul (L 2) (V "ln")])
  (.seq (wseqOf 1 (V "fc") (.mul (L 2) (V "ln")))
  (.seq (.write (L 4))
  (.seq (lexOf 1 (V "fc") 0 Y0)
  (.seq (lexOf 0 Y0 1 FV)
  (.seq (writes [L 4, L 0, RI 3, V "ln"])
  (.seq (wseqOf 1 FV (V "ln"))
  (lexOf 1 FV 0 Y0))))))))))

def negRelC : Com :=
  .seq (.ite (.eq (V "ln") (L 0)) (writes [L 0, RI 2, L 0]) negBig)
    (.assign "fc" (.add (V "fc") (.mul (L 2) (V "ln"))))

def posRelC : Com := .seq (writes [L 0, RI 1, V "ln"]) (wseqOf 0 Y0 (V "ln"))

def relBr : Com :=
  .seq (.assign "ri" (A (.add (V "p") (L 1)))) (.seq (.assign "ln" (A (.add (V "p") (L 2))))
  (.seq (.ite (.eq (V "pl") (L 1)) posRelC negRelC)
  (.assign "p" (.add (.add (V "p") (L 3)) (V "ln")))))

def svBr : Com :=
  .seq (.assign "ln" (A (.add (V "p") (L 1)))) (.seq (writes [L 1, V "ln"])
  (.seq (wseqOf 0 (.add (V "p") (L 2)) (V "ln")) (.assign "p" (.add (.add (V "p") (L 2)) (V "ln")))))

def eqBr : Com :=
  .seq (.ite (.eq (V "pl") (L 1)) (writes [L 2, A (.add (V "p") (L 1)), A (.add (V "p") (L 2))])
    (writes [L 5, L 0, L 0, L 2, A (.add (V "p") (L 1)), A (.add (V "p") (L 2)), L 0, L 0, L 2,
      A (.add (V "p") (L 2)), A (.add (V "p") (L 1))]))
  (.assign "p" (.add (V "p") (L 3)))

def negBr : Com :=
  .seq (.store "st" (V "h") (.sub (L 1) (V "pl"))) (.seq (bump "h") (bump "p"))

/-- `∧` (`c = 4`) or `∨` (`c = 5`): the connective, dual under negative polarity. -/
def conBr (e : Expr) : Com :=
  .seq (.write e) (.seq (.store "st" (V "h") (V "pl"))
    (.seq (.store "st" (.add (V "h") (L 1)) (V "pl"))
    (.seq (.assign "h" (.add (V "h") (L 2))) (bump "p"))))

def qBr : Com :=
  .seq (writes [V "tg", A (.add (V "p") (L 1))]) (.seq (.store "st" (V "h") (V "pl"))
    (.seq (bump "h") (.assign "p" (.add (V "p") (L 2)))))

def dispatch : Com :=
  .ite (.eq (V "tg") (L 0)) relBr
  (.ite (.eq (V "tg") (L 1)) svBr
  (.ite (.eq (V "tg") (L 2)) eqBr
  (.ite (.eq (V "tg") (L 3)) negBr
  (.ite (.eq (V "tg") (L 4)) (conBr (.sub (L 5) (V "pl")))
  (.ite (.eq (V "tg") (L 5)) (conBr (.add (L 4) (V "pl"))) qBr)))))

def trBody : Com :=
  .seq (.assign "h" (.sub (V "h") (L 1))) (.seq (.assign "pl" (.get "st" (V "h")))
    (.seq (.assign "tg" (A (V "p"))) dispatch))

def trPass : Com :=
  .seq (.store "st" (L 0) (L 1)) (.seq (.assign "h" (L 1)) (.seq (.assign "fc" (V "bb"))
    (.seq (.assign "p" (V "F0")) (.while (.lt (L 0) (V "h")) trBody))))

/-! ### The program -/

/-- **The body**: array `a` holds the word, `rt_n` its length. -/
def body : Com :=
  .seq header (.seq entPass (.seq (.assign "F0" (V "p")) (.seq foPass (.seq rkPass (.seq Mcom
  (.seq hdOut (.seq ltOut (.seq symPass (.seq mxPass (.seq qOut trPass))))))))))

/-- **The program**: read the tape, then the body. -/
def cmd : Com := .seq Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape body

/-! ### Framing -/

/-- Nothing but the scalars in `S` changed; arrays and input tape are as before. -/
def Keep (S : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp

theorem Keep.trans {S : List String} {σ σ' σ'' : Env} (h : Keep S σ σ') (h' : Keep S σ' σ'') :
    Keep S σ σ'' :=
  ⟨fun y hy => (h'.1 y hy).trans (h.1 y hy), h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Keep.mono {S S' : List String} {σ σ' : Env} (h : Keep S σ σ') (hS : ∀ y ∈ S, y ∈ S') :
    Keep S' σ σ' :=
  ⟨fun y hy => h.1 y fun hm => hy (hS y hm), h.2.1, h.2.2⟩

/-- Framing a specification of a command that never stores and never reads. -/
theorem Spec.keep {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : c.warrs = []) (hr : ¬ c.reads) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Keep S σ σ') K :=
  Spec.post h.frame fun σ σ' _ ⟨hq, hv, ha, hi, _⟩ =>
    ⟨hq, fun y hy => hv y fun hm => hy (hw y hm),
      funext fun a => ha a (by rw [hwa]; simp), hi hr⟩

/-- Framing a specification of a command that never stores, never reads and never writes. -/
theorem Spec.keepOut {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : c.warrs = []) (hr : ¬ c.reads) (hnw : c.NoWrite) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Keep S σ σ' ∧ σ'.out = σ.out) K :=
  Spec.post h.frame fun σ σ' _ ⟨hq, hv, ha, hi, ho⟩ =>
    ⟨hq, ⟨fun y hy => hv y fun hm => hy (hw y hm),
      funext fun a => ha a (by rw [hwa]; simp), hi hr⟩, ho hnw⟩

/-- **Two writing phases in sequence**: the outputs concatenate, the frame composes. -/
theorem Spec.seq_out {B : ℕ} {P : Env → Prop} {c d : Com} {X Y : List ℕ} {K1 K2 : ℕ}
    {S : List String}
    (h1 : Spec B P c (fun σ σ' => σ'.out = σ.out ++ X ∧ Keep S σ σ') K1)
    (h2 : Spec B P d (fun σ σ' => σ'.out = σ.out ++ Y ∧ Keep S σ σ') K2)
    (hP : ∀ σ σ', P σ → Keep S σ σ' → P σ') :
    Spec B P (.seq c d) (fun σ σ' => σ'.out = σ.out ++ (X ++ Y) ∧ Keep S σ σ') (K1 + K2) :=
  Spec.seq h1 h2 (fun σ σ' hp hq => hP σ σ' hp hq.2)
    (fun σ σ' σ'' _ hq hq' => ⟨by rw [hq'.1, hq.1, List.append_assoc], hq.2.trans hq'.2⟩)

/-- A conditional whose test holds. -/
theorem Spec.ite_pos {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {b : Cond} {c d : Com} {K : ℕ}
    (hb : ∀ σ, P σ → b.evalB B σ = some true) (h : Spec B P c Q K) :
    Spec B P (.ite b c d) Q (1 + b.size + K) :=
  Spec.ite (fun σ hσ => ⟨_, hb σ hσ⟩) (h.pre fun σ hσ => hσ.1)
    (fun σ ⟨hσ, hf⟩ => by rw [hb σ hσ] at hf; cases hf)

/-- A conditional whose test fails. -/
theorem Spec.ite_neg {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {b : Cond} {c d : Com} {K : ℕ}
    (hb : ∀ σ, P σ → b.evalB B σ = some false) (h : Spec B P d Q K) :
    Spec B P (.ite b c d) Q (1 + b.size + K) :=
  Spec.ite (fun σ hσ => ⟨_, hb σ hσ⟩) (fun σ ⟨hσ, ht⟩ => by rw [hb σ hσ] at ht; cases ht)
    (h.pre fun σ hσ => hσ.1)

/-- The test `v = n` of a scalar against a literal. -/
theorem evalB_eq_lit {B : ℕ} {σ : Env} {v : String} {n : ℕ} (hv : σ.vars v < B) (hn : n < B) :
    (Cond.eq (V v) (L n)).evalB B σ = some (σ.vars v == n) :=
  evalB_condEq (evalB_var hv) (evalB_lit hn)

end Lax496464Proofs.WHierarchy.Lemmas.NegElim.ProgDefs
