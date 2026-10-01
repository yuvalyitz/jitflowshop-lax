import Lax808846Proofs.Tactic
import Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.Defs

/-!
# Σ₁[2] model checking to Clique: the IMP+ program

The array `a` holds the word `x` and `rt_n` its length (after `readTape`). The phases mirror
`Defs` step for step:

* `hdr`: the number of symbols `zs`, the block starts `bs[i] = hp x i`, the formula start `zp`, the
  size `zN` of the universe;
* `tokz`: `|x|` steps of the tokenizer, filling `nt`, `na` (the nodes), `vs`, `ab`, `ar` (the atoms),
  the counts `zT`, `zq` and the flag `zfl`;
* `elb`: the candidate values `el[0 .. zne)`, `zk = 2 zq`;
* `evl`: `ok[c]` for every valuation `c < zC = 2^zq`, by a stack evaluation in `st`;
* `gph`: the compressed sparse row word of the graph, then `zk`.

Every read of `a` at a computed position is guarded (`rdV`): `0` out of range.
-/

namespace Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs

open Lax808846Proofs.Imp

abbrev V (s : String) : Expr := .var s
abbrev bump (s : String) : Com := .assign s (.add (V s) (.lit 1))

/-- `dst := a[b + k]`, or `0` out of range. -/
def rdV (dst b : String) (k : ℕ) : Com :=
  .ite (.lt (.add (V b) (.lit k)) (V "rt_n")) (.assign dst (.get "a" (.add (V b) (.lit k))))
    (.assign dst (.lit 0))

/-! ### The header -/

/-- One block of the header walk. -/
def hdrBody : Com :=
  .seq (.store "bs" (V "zhi") (V "zp"))
  (.seq (rdV "zhc" "zp" 0)
  (.seq (rdV "zhw" "zhi" 1)
  (.seq (.assign "znx" (.add (.add (V "zp") (.lit 1)) (.mul (V "zhc") (V "zhw"))))
  (.seq (.ite (.lt (V "rt_n") (V "znx")) (.assign "zp" (V "rt_n")) (.assign "zp" (V "znx")))
    (bump "zhi")))))

def hdrLoop : Com := .seq (.assign "zhi" (.lit 0)) (.while (.lt (V "zhi") (V "zs")) hdrBody)

/-- The header. -/
def hdr : Com :=
  .seq (.ite (.lt (.lit 0) (V "rt_n")) (.assign "zs" (.get "a" (.lit 0))) (.assign "zs" (.lit 0)))
  (.seq (.assign "zp" (.add (V "zs") (.lit 2)))
  (.seq (.ite (.lt (V "rt_n") (V "zp")) (.assign "zp" (V "rt_n")) .skip)
  (.seq hdrLoop
    (rdV "zN" "zs" 1))))

/-! ### The tokenizer -/

/-- Record a node `(g, m)`. -/
def pushNode (g m : Expr) : Com :=
  .seq (.store "nt" (V "zT") g) (.seq (.store "na" (V "zT") m) (bump "zT"))

/-- Record the variables of an atom. -/
def pushVars : Com :=
  .seq (.store "vs" (.add (V "zq") (V "zq")) (V "zy1"))
    (.store "vs" (.add (.add (V "zq") (V "zq")) (.lit 1)) (V "zy2"))

/-- The symbol part of a relation atom. -/
def relSym : Com :=
  .ite (.lt (V "zi") (V "zs"))
    (.seq (.store "ab" (V "zq") (.get "bs" (V "zi")))
    (.seq (rdV "zw" "zi" 1)
    (.seq (.store "ar" (V "zq") (V "zw"))
      (.ite (.eq (V "zn") (V "zw")) .skip (.assign "zfl" (.lit 0))))))
    (.seq (.store "ab" (V "zq") (.lit 0))
    (.seq (.store "ar" (V "zq") (.lit 0))
      (.assign "zfl" (.lit 0))))

/-- The variables of a relation atom. -/
def relVars : Com :=
  .seq (.ite (.eq (V "zn") (.lit 0)) (.assign "zy1" (.lit 0)) (rdV "zy1" "zp" 3))
    (.ite (.eq (V "zn") (.lit 2)) (rdV "zy2" "zp" 4) (.assign "zy2" (V "zy1")))

/-- A relation atom `0, i, n, y₁, …`. -/
def relC : Com :=
  .seq (rdV "zi" "zp" 1)
  (.seq (rdV "zn" "zp" 2)
  (.seq relVars
  (.seq (pushNode (.lit 0) (V "zq"))
  (.seq pushVars
  (.seq relSym
  (.seq (bump "zq")
    (.ite (.lt (V "zn") (V "rt_n")) (.assign "zp" (.add (.add (V "zp") (.lit 3)) (V "zn")))
      (.assign "zp" (V "rt_n")))))))))

/-- An equation `2, y₁, y₂`. -/
def eqC : Com :=
  .seq (rdV "zy1" "zp" 1)
  (.seq (rdV "zy2" "zp" 2)
  (.seq (pushNode (.lit 2) (V "zq"))
  (.seq pushVars
  (.seq (.store "ab" (V "zq") (.lit 0))
  (.seq (.store "ar" (V "zq") (.lit 0))
  (.seq (bump "zq")
    (.assign "zp" (.add (V "zp") (.lit 3)))))))))

/-- Any other tag. -/
def otherC : Com :=
  .seq (pushNode (V "zg") (.lit 0)) (.assign "zp" (.add (V "zp") (.lit 1)))

/-- One step of the tokenizer at `zp < |x|`. -/
def tokStepC : Com :=
  .seq (.assign "zg" (.get "a" (V "zp")))
    (.ite (.eq (V "zg") (.lit 6)) (.assign "zp" (.add (V "zp") (.lit 2)))
      (.ite (.eq (V "zg") (.lit 0)) relC
        (.ite (.eq (V "zg") (.lit 2)) eqC otherC)))

def tokBody : Com := .seq (.ite (.lt (V "zp") (V "rt_n")) tokStepC .skip) (bump "ztt")

def tokLoop : Com := .seq (.assign "ztt" (.lit 0)) (.while (.lt (V "ztt") (V "rt_n")) tokBody)

/-- The tokenizer. -/
def tokz : Com :=
  .seq (.seq (.assign "zT" (.lit 0)) (.seq (.assign "zq" (.lit 0)) (.assign "zfl" (.lit 1)))) tokLoop

/-! ### The candidate values -/

def elBody1 : Com :=
  .seq (.assign "zv" (.get "a" (V "zei")))
    (.seq (.ite (.lt (V "zv") (V "zN"))
      (.seq (.store "el" (V "zne") (V "zv")) (bump "zne")) .skip) (bump "zei"))

def elLoop1 : Com := .seq (.assign "zei" (.lit 0)) (.while (.lt (V "zei") (V "rt_n")) elBody1)

def elBody2 : Com := .seq (.store "el" (V "zne") (V "zej")) (.seq (bump "zne") (bump "zej"))

def elLoop2 : Com := .seq (.assign "zej" (.lit 0)) (.while (.lt (V "zej") (V "zlim")) elBody2)

/-- The candidates. -/
def elb : Com :=
  .seq (.assign "zk" (.add (V "zq") (V "zq")))
  (.seq (.assign "zlim" (.add (V "rt_n") (V "zk")))
  (.seq (.ite (.lt (V "zN") (V "zlim")) (.assign "zlim" (V "zN")) .skip)
  (.seq (.assign "zne" (.lit 0))
  (.seq elLoop1
  (.seq elLoop2
    (.ite (.eq (V "zfl") (.lit 1)) .skip (.assign "zne" (.lit 0))))))))

/-! ### The evaluation -/

/-- Push bit `zm` of `zc`. -/
def pushBit : Com :=
  .seq (.assign "zh" (.shiftr (V "zc") (V "zm")))
  (.seq (.store "st" (V "zsp") (.sub (V "zh") (.mul (.div (V "zh") (.lit 2)) (.lit 2))))
    (bump "zsp"))

def negC : Com :=
  .ite (.eq (V "zsp") (.lit 0)) .skip
    (.store "st" (.sub (V "zsp") (.lit 1)) (.sub (.lit 1) (.get "st" (.sub (V "zsp") (.lit 1)))))

def andC : Com :=
  .ite (.lt (V "zsp") (.lit 2)) .skip
    (.seq (.ite (.eq (.get "st" (.sub (V "zsp") (.lit 1))) (.lit 0))
        (.store "st" (.sub (V "zsp") (.lit 2)) (.lit 0)) .skip)
      (.assign "zsp" (.sub (V "zsp") (.lit 1))))

def orC : Com :=
  .ite (.lt (V "zsp") (.lit 2)) .skip
    (.seq (.ite (.eq (.add (.get "st" (.sub (V "zsp") (.lit 2))) (.get "st" (.sub (V "zsp") (.lit 1))))
          (.lit 0))
        (.store "st" (.sub (V "zsp") (.lit 2)) (.lit 0))
        (.store "st" (.sub (V "zsp") (.lit 2)) (.lit 1)))
      (.assign "zsp" (.sub (V "zsp") (.lit 1))))

/-- The operation of node `zj`. -/
def opC : Com :=
  .ite (.eq (V "zg") (.lit 0)) pushBit
    (.ite (.eq (V "zg") (.lit 2)) pushBit
      (.ite (.eq (V "zg") (.lit 3)) negC
        (.ite (.eq (V "zg") (.lit 4)) andC
          (.ite (.eq (V "zg") (.lit 5)) orC .skip))))

def evStepC : Com :=
  .seq (.seq (.assign "zj" (.sub (V "zT") (.add (V "zet") (.lit 1))))
    (.seq (.assign "zg" (.get "nt" (V "zj"))) (.assign "zm" (.get "na" (V "zj")))))
  (.seq opC (bump "zet"))

def evLoop : Com := .seq (.assign "zet" (.lit 0)) (.while (.lt (V "zet") (V "zT")) evStepC)

/-- Evaluate under the valuation `zc` and record it. -/
def evBody : Com :=
  .seq (.assign "zsp" (.lit 0))
  (.seq evLoop
  (.seq (.ite (.eq (V "zsp") (.lit 0)) (.store "ok" (V "zc") (.lit 0))
      (.store "ok" (V "zc") (.get "st" (.sub (V "zsp") (.lit 1)))))
    (bump "zc")))

def evl : Com :=
  .seq (.assign "zC" (.shiftl (.lit 1) (V "zq")))
    (.seq (.assign "zc" (.lit 0)) (.while (.lt (V "zc") (V "zC")) evBody))

/-! ### The adjacency test -/

/-- Decode the vertices `gs` and `gt`. -/
def decC : Com :=
  .seq (.assign "r1" (.sub (V "gs") (.mul (.div (V "gs") (V "zk")) (V "zk"))))
  (.seq (.assign "t1" (.div (V "gs") (V "zk")))
  (.seq (.assign "e1" (.sub (V "t1") (.mul (.div (V "t1") (V "zne")) (V "zne"))))
  (.seq (.assign "c1" (.div (V "t1") (V "zne")))
  (.seq (.assign "r2" (.sub (V "gt") (.mul (.div (V "gt") (V "zk")) (V "zk"))))
  (.seq (.assign "t2" (.div (V "gt") (V "zk")))
  (.seq (.assign "e2" (.sub (V "t2") (.mul (.div (V "t2") (V "zne")) (V "zne"))))
    (.assign "c2" (.div (V "t2") (V "zne")))))))))

/-- One tuple of the scan. -/
def scanBody : Com :=
  .seq (.assign "apos" (.add (.add (V "asb") (.lit 1)) (.mul (V "asj") (V "asa"))))
  (.seq (rdV "au1" "apos" 0)
  (.seq (.ite (.eq (V "au1") (V "aw1"))
      (.ite (.eq (V "asa") (.lit 1)) (.assign "atr" (.lit 1))
        (.seq (rdV "au2" "apos" 1)
          (.ite (.eq (V "au2") (V "aw2")) (.assign "atr" (.lit 1)) .skip)))
      .skip)
    (bump "asj")))

def scanLoop : Com := .seq (.assign "asj" (.lit 0)) (.while (.lt (V "asj") (V "acnt")) scanBody)

/-- The scan of the block of atom `am1`. -/
def scanC : Com :=
  .seq (.seq (.assign "asb" (.get "ab" (V "am1")))
    (.seq (rdV "acnt" "asb" 0)
    (.seq (.ite (.lt (V "rt_n") (V "acnt")) (.assign "acnt" (V "rt_n")) .skip)
      (.assign "atr" (.lit 0)))))
    scanLoop

/-- The atom test for the atom `am1` of the two rows. -/
def atomC : Com :=
  .seq (.ite (.lt (V "r1") (V "r2")) (.seq (.assign "aw1" (V "av1")) (.assign "aw2" (V "av2")))
      (.seq (.assign "aw1" (V "av2")) (.assign "aw2" (V "av1"))))
  (.seq (.seq (.assign "ah" (.shiftr (V "c1") (V "am1")))
    (.assign "abt" (.sub (V "ah") (.mul (.div (V "ah") (.lit 2)) (.lit 2)))))
  (.seq (.assign "asa" (.get "ar" (V "am1")))
  (.seq (.ite (.eq (V "asa") (.lit 0))
      (.ite (.eq (V "aw1") (V "aw2")) (.assign "atr" (.lit 1)) (.assign "atr" (.lit 0)))
      scanC)
    (.ite (.eq (V "atr") (V "abt")) (.assign "gf" (.lit 1)) .skip))))

/-- The reads and the consistency flag. -/
def rowsA : Com :=
  .seq (.assign "av1" (.get "el" (V "e1")))
  (.seq (.assign "av2" (.get "el" (V "e2")))
  (.seq (.assign "az1" (.get "vs" (V "r1")))
  (.seq (.assign "az2" (.get "vs" (V "r2")))
  (.seq (.assign "ace" (.lit 1))
    (.ite (.eq (V "az1") (V "az2"))
      (.ite (.eq (V "av1") (V "av2")) .skip (.assign "ace" (.lit 0))) .skip)))))

/-- The rows differ: consistency, then the atom test. -/
def rowsC : Com :=
  .seq rowsA
    (.ite (.eq (V "ace") (.lit 1))
      (.seq (.seq (.assign "am1" (.div (V "r1") (.lit 2))) (.assign "am2" (.div (V "r2") (.lit 2))))
        (.ite (.eq (V "am1") (V "am2")) atomC (.assign "gf" (.lit 1))))
      .skip)

/-- The test after decoding. -/
def testC : Com :=
  .seq (.assign "gf" (.lit 0))
    (.ite (.eq (V "c1") (V "c2"))
      (.seq (.assign "ao" (.get "ok" (V "c1")))
        (.ite (.eq (V "ao") (.lit 1)) (.ite (.eq (V "r1") (V "r2")) .skip rowsC) .skip))
      .skip)

/-- `gf := 1` iff `gs` and `gt` are adjacent. -/
def adjCom : Com := .seq decC testC

/-! ### The passes -/

def rowCount : Com :=
  .seq (.assign "gd" (.lit 0))
   (.seq (.assign "gt" (.lit 0))
    (.while (.lt (V "gt") (V "zNG"))
     (.seq adjCom (.seq (.assign "gd" (.add (V "gd") (V "gf"))) (bump "gt")))))

def emitIf : Com := .ite (.eq (V "gf") (.lit 1)) (.write (V "gt")) .skip

def rowEmit : Com :=
  .seq (.assign "gt" (.lit 0))
   (.while (.lt (V "gt") (V "zNG"))
    (.seq adjCom (.seq emitIf (bump "gt"))))

def pass1 : Com :=
  .seq (.assign "gM" (.lit 0))
   (.seq (.assign "gs" (.lit 0))
    (.while (.lt (V "gs") (V "zNG"))
     (.seq rowCount (.seq (.assign "gM" (.add (V "gM") (V "gd"))) (bump "gs")))))

def pass2 : Com :=
  .seq (.assign "goff" (.lit 0))
   (.seq (.assign "gs" (.lit 0))
    (.while (.lt (V "gs") (V "zNG"))
     (.seq rowCount (.seq (.assign "goff" (.add (V "goff") (V "gd")))
       (.seq (.write (V "goff")) (bump "gs"))))))

def pass3 : Com :=
  .seq (.assign "gs" (.lit 0))
   (.while (.lt (V "gs") (V "zNG")) (.seq rowEmit (bump "gs")))

/-- The graph: the word of `Defs.reduce`. -/
def gph : Com :=
  .seq (.assign "zNG" (.mul (V "zC") (.mul (V "zne") (V "zk"))))
  (.seq pass1
  (.seq (.write (V "zNG"))
  (.seq (.write (.div (V "gM") (.lit 2)))
  (.seq (.write (.lit 0))
  (.seq pass2
  (.seq pass3
    (.write (V "zk"))))))))

/-- Everything after reading the tape. -/
def body : Com := .seq hdr (.seq tokz (.seq elb (.seq evl gph)))

end Lax496464Proofs.WHierarchy.Lemmas.BinaryToClique.ProgDefs
