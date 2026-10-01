import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgHead
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgPre
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutE
import Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgForm

/-! # The whole body writes the output of the reduction

`body_spec`: after `readTape`, the nine phases of `body` write the word of the incidence structure
followed by the code of the translated formula (`outWord_eq`). -/

namespace Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgMain

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax496464.WH_B2_FirstOrder
open Lax496464Proofs.WHierarchy.Logic.SatFacts
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Tok Lax496464Proofs.WHierarchy.Lemmas.Incidence.Struct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Parse Lax496464Proofs.WHierarchy.Lemmas.Incidence.Sem
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.Syntax Lax496464Proofs.WHierarchy.Lemmas.Incidence.Correct
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDefs Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgDom
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgTok Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgHead
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgPre Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutS
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutE Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgOutF
open Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgForm

variable {x : List ℕ} {φ : Formula} {B : ℕ}

/-- **The output, as the program writes it.** -/
theorem outWord_eq (x : List ℕ) (φ : Formula) :
    outWord x φ = headList x φ ++ pList' x (sOf x) ++ eAll x (rOf φ) ++ qList x (nrel φ) ++
      ((Cx x φ).tr 0 φ).encode := by
  unfold outWord phiOf
  rw [IncData.word_eq, encode_exBlock]
  simp only [headList, pList', eAll, qList, eL, zsOf, List.flatMap_map, List.append_assoc]
  rfl

/-- The output phases. -/
def rest : Com := .seq headOut (.seq pOut (.seq eOut (.seq qOut fOut)))

/-- The cost of the output phases. -/
def Krest (x : List ℕ) (φ : Formula) : ℕ :=
  Khead x + (Kp x + (Ke x φ + (((20 + 4) * nrel φ + 6) + (10 + Kfl x))))

theorem rest_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (Ctx x φ) rest (fun σ σ' => σ'.out = σ.out ++ (headList x φ ++ pList' x (sOf x) ++
      eAll x (rOf φ) ++ qList x (nrel φ) ++ ((Cx x φ).tr 0 φ).encode)) (Krest x φ) := by
  have h9 := fOut_spec hd hB
  have h8 := qOut_spec hd hB
  have h7 := eOut_spec hd hB
  have h6 := pOut_spec hd hB
  have h5 := headOut_spec hd hB
  have g89 : Spec B (Ctx x φ) (.seq qOut fOut) (fun σ σ' => σ'.out = σ.out ++
      (qList x (nrel φ) ++ ((Cx x φ).tr 0 φ).encode)) (((20 + 4) * nrel φ + 6) + (10 + Kfl x)) :=
    Spec.seq h8 h9 (fun _ _ hc hq => Ctx.keep hc hq.2 (by decide))
      (fun _ _ _ _ hq hq' => by rw [hq'.1, hq.1, List.append_assoc])
  have g79 : Spec B (Ctx x φ) (.seq eOut (.seq qOut fOut)) (fun σ σ' => σ'.out = σ.out ++
      (eAll x (rOf φ) ++ (qList x (nrel φ) ++ ((Cx x φ).tr 0 φ).encode)))
      (Ke x φ + (((20 + 4) * nrel φ + 6) + (10 + Kfl x))) :=
    Spec.seq h7 g89 (fun _ _ hc hq => Ctx.keep hc hq.2 (by decide))
      (fun _ _ _ _ hq hq' => by rw [hq', hq.1, List.append_assoc])
  have g69 : Spec B (Ctx x φ) (.seq pOut (.seq eOut (.seq qOut fOut))) (fun σ σ' => σ'.out =
      σ.out ++ (pList' x (sOf x) ++ (eAll x (rOf φ) ++ (qList x (nrel φ) ++
        ((Cx x φ).tr 0 φ).encode))))
      (Kp x + (Ke x φ + (((20 + 4) * nrel φ + 6) + (10 + Kfl x)))) :=
    Spec.seq h6 g79 (fun _ _ hc hq => Ctx.keep hc hq.2 (by decide))
      (fun _ _ _ _ hq hq' => by rw [hq', hq.1, List.append_assoc])
  refine Spec.seq h5 g69 (fun _ _ hc hq => Ctx.keep hc hq.2 (by decide))
    (fun _ _ _ _ hq hq' => ?_)
  rw [hq', hq.1]
  simp only [List.append_assoc]

/-- The cost of the reading phases. -/
def Kread (x : List ℕ) : ℕ :=
  20 + ((10 + (40 + 4) * sOf x + 6) + ((10 + (30 + 4) * x.length + 6) + (10 + Kpre x)))

/-- The cost of the body. -/
def Kbody (x : List ℕ) (φ : Formula) : ℕ := Kread x + Krest x φ

theorem body_spec (hd : Dom x φ) (hB : BOK x B) :
    Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length) body
      (fun σ σ' => σ'.out = σ.out ++ outWord x φ) (Kbody x φ) := by
  have h1 := header_spec hd hB
  have h2 := blocks_spec hd hB
  have h3 := maxPass_spec hB
  have h4 := prePass_spec hd hB
  have hr := rest_spec hd hB
  have g4 : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
      σ.vars "ic_s" = sOf x ∧ σ.vars "ic_N" = nOf x ∧ σ.vars "ic_b" = fsOf x ∧
      σ.vars "ic_g" = tOf x ∧ σ.vars "ic_F" = fOf x) (.seq prePass rest)
      (fun σ σ' => σ'.out = σ.out ++ outWord x φ) ((10 + Kpre x) + Krest x φ) := by
    refine Spec.seq (h4.pre fun σ h => ⟨h.1, h.2.1, h.2.2.2.2.1⟩) hr ?_ ?_
    · rintro σ σ' ⟨ha, hn, hs, hN, hb, hg, hF⟩ ⟨⟨hq, hrr⟩, hk, -⟩
      obtain ⟨hv, harr, -⟩ := hk
      refine ⟨by rw [harr]; exact ha, ?_, ?_, ?_, ?_, ?_, ?_, hq, hrr⟩
      · rw [hv _ (by decide)]; exact hn
      · rw [hv _ (by decide)]; exact hs
      · rw [hv _ (by decide)]; exact hN
      · rw [hv _ (by decide)]; exact hb
      · rw [hv _ (by decide)]; exact hg
      · rw [hv _ (by decide)]; exact hF
    · rintro σ σ' σ'' - ⟨-, -, ho⟩ ho'
      rw [ho', ho, outWord_eq]
  have g3 : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
      σ.vars "ic_s" = sOf x ∧ σ.vars "ic_N" = nOf x ∧ σ.vars "ic_b" = fsOf x ∧
      σ.vars "ic_g" = tOf x) (.seq maxPass (.seq prePass rest))
      (fun σ σ' => σ'.out = σ.out ++ outWord x φ)
      ((10 + (30 + 4) * x.length + 6) + ((10 + Kpre x) + Krest x φ)) := by
    refine Spec.seq (h3.pre fun σ h => ⟨h.1, h.2.1⟩) g4 ?_ ?_
    · rintro σ σ' ⟨ha, hn, hs, hN, hb, hg⟩ ⟨hF, hk, -⟩
      obtain ⟨hv, harr, -⟩ := hk
      refine ⟨by rw [harr]; exact ha, ?_, ?_, ?_, ?_, ?_, hF⟩
      · rw [hv _ (by decide)]; exact hn
      · rw [hv _ (by decide)]; exact hs
      · rw [hv _ (by decide)]; exact hN
      · rw [hv _ (by decide)]; exact hb
      · rw [hv _ (by decide)]; exact hg
    · rintro σ σ' σ'' - ⟨-, -, ho⟩ ho'
      rw [ho', ho]
  have g2 : Spec B (fun σ => σ.arrs "a" = x ∧ σ.vars "rt_n" = x.length ∧
      σ.vars "ic_s" = sOf x ∧ σ.vars "ic_N" = nOf x) (.seq blocks (.seq maxPass (.seq prePass rest)))
      (fun σ σ' => σ'.out = σ.out ++ outWord x φ)
      ((10 + (40 + 4) * sOf x + 6) + ((10 + (30 + 4) * x.length + 6) + ((10 + Kpre x) +
        Krest x φ))) := by
    refine Spec.seq (h2.pre fun σ h => ⟨h.1, h.2.2.1⟩) g3 ?_ ?_
    · rintro σ σ' ⟨ha, hn, hs, hN⟩ ⟨⟨hb, hg⟩, hk, -⟩
      obtain ⟨hv, harr, -⟩ := hk
      refine ⟨by rw [harr]; exact ha, ?_, ?_, ?_, hb, hg⟩
      · rw [hv _ (by decide)]; exact hn
      · rw [hv _ (by decide)]; exact hs
      · rw [hv _ (by decide)]; exact hN
    · rintro σ σ' σ'' - ⟨-, -, ho⟩ ho'
      rw [ho', ho]
  refine Spec.mono (Spec.seq (h1.pre fun σ h => h.1) g2 ?_ ?_) (le_of_eq ?_)
  · rintro σ σ' ⟨ha, hn⟩ ⟨⟨hs, hN⟩, hk, -⟩
    obtain ⟨hv, harr, -⟩ := hk
    exact ⟨by rw [harr]; exact ha, by rw [hv _ (by decide)]; exact hn, hs, hN⟩
  · rintro σ σ' σ'' - ⟨-, -, ho⟩ ho'
    rw [ho', ho]
  · unfold Kbody Kread; ring

end Lax496464Proofs.WHierarchy.Lemmas.Incidence.ProgMain
