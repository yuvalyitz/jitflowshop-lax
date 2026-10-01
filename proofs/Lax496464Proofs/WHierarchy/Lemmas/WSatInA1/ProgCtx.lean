import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst
import Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.RowsMath

/-! # The context of the phases after the constants, and the value bound

`Ctx`: the arrays and scalars set up by phases 1 and 2, which the later phases keep; `BB`: the facts
about the value bound the phases need. -/

namespace Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Defs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.Basic
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgParse
open Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgConst

/-- The scalars that hold the constants from phase 2 on. -/
def ctxVars : List String :=
  ["w_m", "w_L", "w_k", "w_M", "w_dk", "hs_t", "w_md", "w_K1", "w_F", "w_nv", "w_d1"]

/-- The context: the word, the clauses and the constants. -/
def Ctx (cl : List (List ℕ)) (d k : ℕ) (σ : Env) : Prop :=
  σ.arrs "a" = wordOf' cl k ∧ σ.arrs "co" = coList cl ∧ σ.arrs "cd" = cl.flatten ∧
    σ.vars "w_m" = cl.length ∧ σ.vars "w_L" = nL cl ∧ σ.vars "w_k" = k ∧ CPost cl d k σ

theorem Ctx.keep {cl : List (List ℕ)} {d k : ℕ} {σ σ' : Env} (h : Ctx cl d k σ)
    (hv : ∀ y ∈ ctxVars, σ'.vars y = σ.vars y)
    (ha : ∀ a ∈ ["a", "co", "cd"], σ'.arrs a = σ.arrs a) : Ctx cl d k σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [ha _ (by simp)]; assumption)
    | (rw [hv _ (by simp [ctxVars])]; assumption)

section Proj
variable {cl : List (List ℕ)} {d k : ℕ} {σ : Env} (h : Ctx cl d k σ)
include h
theorem Ctx.hco : σ.arrs "co" = coList cl := h.2.1
theorem Ctx.hcd : σ.arrs "cd" = cl.flatten := h.2.2.1
theorem Ctx.hm : σ.vars "w_m" = cl.length := h.2.2.2.1
theorem Ctx.hL : σ.vars "w_L" = nL cl := h.2.2.2.2.1
theorem Ctx.hk : σ.vars "w_k" = k := h.2.2.2.2.2.1
theorem Ctx.hM : σ.vars "w_M" = MM cl := h.2.2.2.2.2.2.1
theorem Ctx.hdk : σ.vars "w_dk" = d ^ k := h.2.2.2.2.2.2.2.1
theorem Ctx.ht : σ.vars "hs_t" = sz cl d k := h.2.2.2.2.2.2.2.2.1
theorem Ctx.hmd : σ.vars "w_md" = MM cl ^ (d + 2) := h.2.2.2.2.2.2.2.2.2.1
theorem Ctx.hK1 : σ.vars "w_K1" = k + 1 := h.2.2.2.2.2.2.2.2.2.2.1
theorem Ctx.hF : σ.vars "w_F" = FF d k := h.2.2.2.2.2.2.2.2.2.2.2.1
theorem Ctx.hnv : σ.vars "w_nv" = nv d k := h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem Ctx.hd1 : σ.vars "w_d1" = d + 1 := h.2.2.2.2.2.2.2.2.2.2.2.2.2
end Proj

/-- The value bound the phases need. -/
structure BB (cl : List (List ℕ)) (d k B : ℕ) : Prop where
  cb : CBound cl d k B
  hx : ∀ v ∈ wordOf' cl k, v < B
  hl : cl.length + nL cl + 4 < B
  var : ∀ j < nL cl, code cl j / 2 * MM cl < B
  big : 4 * MM cl ^ (d + k + 4) < B

theorem MM_ge (cl : List (List ℕ)) : 4 ≤ MM cl := by unfold MM; omega

theorem nL_lt_MM (cl : List (List ℕ)) : nL cl < MM cl := by unfold MM; omega

theorem pow_le_big (cl : List (List ℕ)) {i n : ℕ} (h : i ≤ n) : MM cl ^ i ≤ MM cl ^ n :=
  Nat.pow_le_pow_right (by have := MM_ge cl; omega) h

theorem code_lt {cl : List (List ℕ)} {k B j : ℕ} (hx : ∀ v ∈ wordOf' cl k, v < B)
    (hj : j < nL cl) : code cl j < B := by
  obtain ⟨c, hc, p, hp, rfl⟩ := exists_clause_of_lt cl hj
  have hw := word_code (k := k) hc hp
  have hl := length_wordOf' (cl := cl) (k := k)
  have hol := off_len_le cl hc
  rw [← hw]
  exact hx _ (Lax496464Proofs.WHierarchy.HittingSet.Compress.getD_mem (by omega))

end Lax496464Proofs.WHierarchy.Lemmas.WSatInA1.ProgCtx
