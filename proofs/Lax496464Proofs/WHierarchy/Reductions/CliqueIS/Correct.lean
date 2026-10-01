import Lax496464.WH_A2_FptReductions
import Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math

/-! # The complement map is a reduction, both ways, with the parameter unchanged

A graph word and the complement word present graphs with complementary edges and the same `k`; so
`complWord` reduces `p-Clique` to `p-Independent-Set` and back (`isReduction_clique_is`,
`isReduction_is_clique`), with the parameter unchanged. -/

namespace Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Correct

open Lax271696.VertexCover Lax496464.WH_A2_FptReductions Lax496464.WH_C1_GraphProblems
open Lax496464Proofs.WHierarchy.Graphs.CsrUnique Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Math

/-- A question about the instance a word presents is a question about *the* instance. -/
theorem exists_encodes_iff {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (hx : EncodesParamInstance x n G k) (P : (n : ℕ) → SimpleGraph (Fin n) → ℕ → Prop) :
    (∃ n' G' k', EncodesParamInstance x n' G' k' ∧ P n' G' k') ↔ P n G k := by
  constructor
  · rintro ⟨n', G', k', h', hP⟩
    obtain rfl := vertices_eq hx h'
    obtain ⟨rfl, rfl⟩ := graph_param_eq hx h'
    exact hP
  · exact fun hP => ⟨n, G, k, hx, hP⟩

theorem clique_iff {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (hx : EncodesParamInstance x n G k) :
    Clique.Yes x ↔ ∃ s : Finset (Fin n), G.IsNClique k s :=
  exists_encodes_iff hx fun n G k => ∃ s : Finset (Fin n), G.IsNClique k s

theorem independentSet_iff {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {k : ℕ}
    (hx : EncodesParamInstance x n G k) :
    IndependentSet.Yes x ↔ ∃ s : Finset (Fin n), Gᶜ.IsNClique k s :=
  exists_encodes_iff hx fun n G k => ∃ s : Finset (Fin n), Gᶜ.IsNClique k s

theorem complWord_mem {x : List ℕ} (hx : x ∈ GraphInstances) : complWord x ∈ GraphInstances := by
  obtain ⟨n, G, k, h⟩ := hx
  exact ⟨n, Gᶜ, k, encodes_complWord h⟩

/-- `p-Clique` to `p-Independent-Set`. -/
theorem isReduction_clique_is : IsReduction Clique IndependentSet complWord where
  maps_domain _ hx := complWord_mem hx
  correct x hx := by
    obtain ⟨n, G, k, h⟩ := hx
    rw [clique_iff h, independentSet_iff (encodes_complWord h), compl_compl]

/-- `p-Independent-Set` to `p-Clique`. -/
theorem isReduction_is_clique : IsReduction IndependentSet Clique complWord where
  maps_domain _ hx := complWord_mem hx
  correct x hx := by
    obtain ⟨n, G, k, h⟩ := hx
    rw [independentSet_iff h, clique_iff (encodes_complWord h)]

theorem param_complWord (x : List ℕ) : (complWord x).getLast?.getD 0 = x.getLast?.getD 0 :=
  kOf_complWord x

theorem paramBounded_clique_is : ParamBounded Clique IndependentSet complWord :=
  ⟨id, Computable.id, fun x _ => le_of_eq (param_complWord x)⟩

theorem paramBounded_is_clique : ParamBounded IndependentSet Clique complWord :=
  ⟨id, Computable.id, fun x _ => le_of_eq (param_complWord x)⟩

end Lax496464Proofs.WHierarchy.Reductions.CliqueIS.Correct
