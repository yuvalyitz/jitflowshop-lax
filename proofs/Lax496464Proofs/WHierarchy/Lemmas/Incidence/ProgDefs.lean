import Lax496464Proofs.WHierarchy.Machine.ReadTape
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct

/-! # The IMP+ program of the incidence reduction: definitions

After `readTape` (array `a` = the word `x`, `rt_n = |x|`), `body` runs nine phases:

1. `header`: `ic_s := a[0]` (symbols), `ic_N := a[1 + ic_s]` (universe);
2. `blocks`: walks the blocks, `ic_b` ends at the start of the formula, `ic_g` = number of tuples;
3. `maxPass`: `ic_F := 1 + max a`, the first fresh variable;
4. `prePass`: walks the tokens of the formula: `ic_q` = number of atoms, `ic_r` = largest arity;
5. `headOut`: writes the vocabulary and the size of the incidence structure;
6. `pOut`: writes the blocks of the unary symbols `P_i`;
7. `eOut`: writes the blocks of the binary symbols `E_l`;
8. `qOut`: writes the quantifiers of the fresh variables;
9. `fOut`: walks the tokens of the formula again and writes their translations.

All scalars of `body` are prefixed `ic_`. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))
abbrev A (e : Expr) : Expr := .get "a" e

/-! ### 1–3: reading the structure -/

def header : Com :=
  .seq (.assign "ic_s" (A (.lit 0))) (.assign "ic_N" (A (.add (.lit 1) (V "ic_s"))))

def blockBody : Com :=
  .seq (.assign "ic_c" (A (V "ic_b")))
  (.seq (.assign "ic_g" (.add (V "ic_g") (V "ic_c")))
  (.seq (.assign "ic_b" (.add (.add (V "ic_b") (.lit 1))
      (.mul (V "ic_c") (A (.add (.lit 1) (V "ic_i"))))))
  (bump "ic_i")))

def blockLoop : Com := .seq (.assign "ic_i" (.lit 0)) (.while (.lt (V "ic_i") (V "ic_s")) blockBody)

def blocks : Com :=
  .seq (.assign "ic_b" (.add (.lit 2) (V "ic_s"))) (.seq (.assign "ic_g" (.lit 0)) blockLoop)

def maxBody : Com :=
  .seq (.ite (.lt (V "ic_m") (A (V "ic_p"))) (.assign "ic_m" (A (V "ic_p"))) .skip) (bump "ic_p")

def maxLoop : Com := .seq (.assign "ic_p" (.lit 0)) (.while (.lt (V "ic_p") (V "rt_n")) maxBody)

def maxPass : Com :=
  .seq (.assign "ic_m" (.lit 0)) (.seq maxLoop (.assign "ic_F" (.add (V "ic_m") (.lit 1))))

/-! ### 4: the first walk over the tokens -/

def preRel : Com :=
  .seq (.assign "ic_k" (A (.add (V "ic_p") (.lit 2))))
  (.seq (.assign "ic_q" (.add (V "ic_q") (.lit 1)))
  (.seq (.ite (.lt (V "ic_r") (V "ic_k")) (.assign "ic_r" (V "ic_k")) .skip)
  (.assign "ic_p" (.add (.add (V "ic_p") (.lit 3)) (V "ic_k")))))

def preBody : Com :=
  .seq (.assign "ic_t" (A (V "ic_p")))
  (.ite (.eq (V "ic_t") (.lit 0)) preRel
  (.ite (.eq (V "ic_t") (.lit 2)) (.assign "ic_p" (.add (V "ic_p") (.lit 3)))
  (.ite (.eq (V "ic_t") (.lit 6)) (.assign "ic_p" (.add (V "ic_p") (.lit 2)))
    (.assign "ic_p" (.add (V "ic_p") (.lit 1))))))

def preLoop : Com := .while (.lt (V "ic_p") (V "rt_n")) preBody

def prePass : Com :=
  .seq (.assign "ic_p" (V "ic_b"))
  (.seq (.assign "ic_q" (.lit 0)) (.seq (.assign "ic_r" (.lit 0)) preLoop))

/-! ### 5–7: the incidence structure -/

def onesLoop : Com :=
  .seq (.assign "ic_i" (.lit 0)) (.while (.lt (V "ic_i") (V "ic_s")) (.seq (.write (.lit 1)) (bump "ic_i")))

def twosLoop : Com :=
  .seq (.assign "ic_i" (.lit 0)) (.while (.lt (V "ic_i") (V "ic_r")) (.seq (.write (.lit 2)) (bump "ic_i")))

def headOut : Com :=
  .seq (.write (.add (V "ic_s") (V "ic_r")))
  (.seq onesLoop (.seq twosLoop (.write (.add (V "ic_N") (V "ic_g")))))

def pElemBody : Com := .seq (.write (.add (.add (V "ic_N") (V "ic_g2")) (V "ic_j"))) (bump "ic_j")

def pElemLoop : Com :=
  .seq (.assign "ic_j" (.lit 0)) (.while (.lt (V "ic_j") (V "ic_c")) pElemBody)

def pBody : Com :=
  .seq (.assign "ic_c" (A (V "ic_b2")))
  (.seq (.write (V "ic_c"))
  (.seq pElemLoop
  (.seq (.assign "ic_g2" (.add (V "ic_g2") (V "ic_c")))
  (.seq (.assign "ic_b2" (.add (.add (V "ic_b2") (.lit 1))
      (.mul (V "ic_c") (A (.add (.lit 1) (V "ic_i"))))))
  (bump "ic_i")))))

def pLoop : Com := .seq (.assign "ic_i" (.lit 0)) (.while (.lt (V "ic_i") (V "ic_s")) pBody)

def pOut : Com :=
  .seq (.assign "ic_g2" (.lit 0)) (.seq (.assign "ic_b2" (.add (.lit 2) (V "ic_s"))) pLoop)

def ecBody : Com :=
  .seq (.assign "ic_c" (A (V "ic_b2")))
  (.seq (.assign "ic_w" (A (.add (.lit 1) (V "ic_i"))))
  (.seq (.ite (.lt (V "ic_l") (V "ic_w")) (.assign "ic_e" (.add (V "ic_e") (V "ic_c"))) .skip)
  (.seq (.assign "ic_b2" (.add (.add (V "ic_b2") (.lit 1)) (.mul (V "ic_c") (V "ic_w"))))
  (bump "ic_i"))))

def ecLoop : Com := .seq (.assign "ic_i" (.lit 0)) (.while (.lt (V "ic_i") (V "ic_s")) ecBody)

def eCountC : Com :=
  .seq (.assign "ic_e" (.lit 0)) (.seq (.assign "ic_b2" (.add (.lit 2) (V "ic_s"))) ecLoop)

def pairBody : Com :=
  .seq (.write (A (.add (.add (.add (V "ic_b2") (.lit 1)) (.mul (V "ic_j") (V "ic_w"))) (V "ic_l"))))
  (.seq (.write (.add (.add (V "ic_N") (V "ic_g2")) (V "ic_j"))) (bump "ic_j"))

def pairLoop : Com :=
  .seq (.assign "ic_j" (.lit 0)) (.while (.lt (V "ic_j") (V "ic_c")) pairBody)

def eeBody : Com :=
  .seq (.assign "ic_c" (A (V "ic_b2")))
  (.seq (.assign "ic_w" (A (.add (.lit 1) (V "ic_i"))))
  (.seq (.ite (.lt (V "ic_l") (V "ic_w")) pairLoop .skip)
  (.seq (.assign "ic_g2" (.add (V "ic_g2") (V "ic_c")))
  (.seq (.assign "ic_b2" (.add (.add (V "ic_b2") (.lit 1)) (.mul (V "ic_c") (V "ic_w"))))
  (bump "ic_i")))))

def eeLoop : Com := .seq (.assign "ic_i" (.lit 0)) (.while (.lt (V "ic_i") (V "ic_s")) eeBody)

def eEmitC : Com :=
  .seq (.assign "ic_g2" (.lit 0)) (.seq (.assign "ic_b2" (.add (.lit 2) (V "ic_s"))) eeLoop)

def eBody : Com := .seq eCountC (.seq (.write (V "ic_e")) (.seq eEmitC (bump "ic_l")))

def eOut : Com := .seq (.assign "ic_l" (.lit 0)) (.while (.lt (V "ic_l") (V "ic_r")) eBody)

/-! ### 8–9: the formula -/

def qBody : Com := .seq (.write (.lit 6)) (.seq (.write (.add (V "ic_F") (V "ic_j"))) (bump "ic_j"))

def qOut : Com := .seq (.assign "ic_j" (.lit 0)) (.while (.lt (V "ic_j") (V "ic_q")) qBody)

def argBody : Com :=
  .seq (.write (.lit 4))
  (.seq (.write (.lit 0))
  (.seq (.write (.add (V "ic_s") (V "ic_l")))
  (.seq (.write (.lit 2))
  (.seq (.write (A (.add (.add (V "ic_p") (.lit 3)) (V "ic_l"))))
  (.seq (.write (V "ic_zz"))
  (bump "ic_l"))))))

def argLoop : Com := .seq (.assign "ic_l" (.lit 0)) (.while (.lt (V "ic_l") (V "ic_k")) argBody)

def pComp : Com :=
  .ite (.lt (V "ic_i2") (V "ic_s"))
    (.ite (.eq (A (.add (.lit 1) (V "ic_i2"))) (V "ic_k")) (.assign "ic_P" (V "ic_i2"))
      (.assign "ic_P" (.add (V "ic_s") (V "ic_r"))))
    (.assign "ic_P" (.add (V "ic_s") (V "ic_r")))

def relTail : Com :=
  .seq (.write (.lit 0))
  (.seq (.write (V "ic_P"))
  (.seq (.write (.lit 1))
  (.seq (.write (V "ic_zz"))
  (.seq (bump "ic_z")
  (.assign "ic_p" (.add (.add (V "ic_p") (.lit 3)) (V "ic_k")))))))

def relOut : Com :=
  .seq (.assign "ic_i2" (A (.add (V "ic_p") (.lit 1))))
  (.seq (.assign "ic_k" (A (.add (V "ic_p") (.lit 2))))
  (.seq (.assign "ic_zz" (.add (V "ic_F") (V "ic_z")))
  (.seq argLoop (.seq pComp relTail))))

def eqOut : Com :=
  .seq (.write (.lit 2))
  (.seq (.write (A (.add (V "ic_p") (.lit 1))))
  (.seq (.write (A (.add (V "ic_p") (.lit 2))))
  (.assign "ic_p" (.add (V "ic_p") (.lit 3)))))

def exOut : Com :=
  .seq (.write (.lit 6))
  (.seq (.write (A (.add (V "ic_p") (.lit 1))))
  (.assign "ic_p" (.add (V "ic_p") (.lit 2))))

def otherOut : Com := .seq (.write (V "ic_t")) (.assign "ic_p" (.add (V "ic_p") (.lit 1)))

def fBody : Com :=
  .seq (.assign "ic_t" (A (V "ic_p")))
  (.ite (.eq (V "ic_t") (.lit 0)) relOut
  (.ite (.eq (V "ic_t") (.lit 2)) eqOut
  (.ite (.eq (V "ic_t") (.lit 6)) exOut otherOut)))

def fLoop : Com := .while (.lt (V "ic_p") (V "rt_n")) fBody

def fOut : Com := .seq (.assign "ic_p" (V "ic_b")) (.seq (.assign "ic_z" (.lit 0)) fLoop)

/-! ### The program -/

/-- **The body**: array `a` holds the word, `rt_n` its length. -/
def body : Com :=
  .seq header (.seq blocks (.seq maxPass (.seq prePass
  (.seq headOut (.seq pOut (.seq eOut (.seq qOut fOut)))))))

/-- **The program**: read the tape, then the body. -/
def cmd : Com := .seq Lax496464Proofs.WHierarchy.Machine.ReadTape.readTape body

/-- The scalars of `body`. -/
def bodyVars : List String :=
  ["ic_s", "ic_N", "ic_b", "ic_g", "ic_c", "ic_i", "ic_m", "ic_p", "ic_F", "ic_q", "ic_r",
    "ic_t", "ic_k", "ic_g2", "ic_b2", "ic_j", "ic_e", "ic_w", "ic_l", "ic_z", "ic_zz", "ic_i2",
    "ic_P"]

/-- Nothing but the scalars in `S` changed; arrays and input tape are as before. -/
def Keep (S : List String) (σ σ' : Env) : Prop :=
  (∀ y, y ∉ S → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp

/-- Framing a specification of a command that never stores and never reads. -/
theorem Spec.keep {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : c.warrs = []) (hr : ¬ c.reads) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Keep S σ σ') K :=
  Spec.post h.frame fun σ σ' _ ⟨hq, hv, ha, hi, _⟩ =>
    ⟨hq, fun y hy => hv y fun hm => hy (hw y hm),
      funext fun a => ha a (by rw [hwa]; simp), hi hr⟩

/-- Framing a specification of a command that never stores, never reads, never writes. -/
theorem Spec.keepOut {B : ℕ} {P : Env → Prop} {Q : Env → Env → Prop} {c : Com} {K : ℕ}
    (h : Spec B P c Q K) (S : List String) (hw : ∀ y, y ∈ c.wvars → y ∈ S)
    (hwa : c.warrs = []) (hr : ¬ c.reads) (hnw : c.NoWrite) :
    Spec B P c (fun σ σ' => Q σ σ' ∧ Keep S σ σ' ∧ σ'.out = σ.out) K :=
  Spec.post h.frame fun σ σ' _ ⟨hq, hv, ha, hi, ho⟩ =>
    ⟨hq, ⟨fun y hy => hv y fun hm => hy (hw y hm),
      funext fun a => ha a (by rw [hwa]; simp), hi hr⟩, ho hnw⟩

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs
