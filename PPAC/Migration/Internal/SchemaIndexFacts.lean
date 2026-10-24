import PPAC.Migration.Internal.SchemaIndexGraphExistence
import PPAC.Migration.Internal.SyntaxIndexLiftEdges

/-! Actual source/target scopes and uniform zero-head facts for the three graphs. -/
namespace PPAC.Migration.Internal.SchemaIndexFacts
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax SchemaIndexSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem matrix_map {m} {Γ : Context m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m) (env : Fin 2 → Fin m)
    (hm : Derives Γ (SchemaIndexSyntax.matrix site w n scopes g env)) :
    Derives Γ (SyntaxIndexMapSyntax.indexMap w g (sourceScope site scopes) (targetScope site scopes)) := by
  rcases site with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact SyntaxIndexLift.target_map w (env 0) n (scopes 1) (scopes 0) (scopes 2) g (.conjR (.conjR hm))
  · exact SyntaxIndexLift.target_map w (env 1) (scopes 0) (scopes 1) (scopes 1) (scopes 2) g (.conjR (.conjR hm))
  · exact SyntaxIndexLift.target_map w (env 1) (scopes 0) (scopes 2) (scopes 1) (scopes 3) g (.conjR (.conjR hm))

theorem graph_map {m} {Γ : Context m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m)
    (hg : Derives Γ (SchemaIndexSyntax.graph site w n scopes g)) :
    Derives Γ (SyntaxIndexMapSyntax.indexMap w g (sourceScope site scopes) (targetScope site scopes)) := by
  let B := body site w n scopes g
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := matrix_map site (old 2 w) (old 2 n) (fun i => old 2 (scopes i)) (old 2 g) (slot 2) hB
  exact of_eq (by simp only [SyntaxIndexMapSyntax.indexMap_rename, sourceScope_map, targetScope_map]) ho

theorem matrix_zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3) (w n : Fin m)
    (scopes : Fin 4 → Fin m) (g : Fin m) (env : Fin 2 → Fin m) (z y : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SchemaIndexSyntax.matrix site w n scopes g env)) (hz : Derives Γ (empty z)) :
    Derives Γ ((edge g z y).iff (empty y)) := by
  rcases site with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact SyntaxIndexLiftEdges.zero_iff hZ w (env 0) n (scopes 1) (scopes 0) (scopes 2) g z y hw (.conjR (.conjR hm)) hz
  · exact SyntaxIndexLiftEdges.zero_iff hZ w (env 1) (scopes 0) (scopes 1) (scopes 1) (scopes 2) g z y hw (.conjR (.conjR hm)) hz
  · exact SyntaxIndexLiftEdges.zero_iff hZ w (env 1) (scopes 0) (scopes 2) (scopes 1) (scopes 3) g z y hw (.conjR (.conjR hm)) hz

theorem graph_zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (site : Fin 3) (w n : Fin m)
    (scopes : Fin 4 → Fin m) (g z y : Fin m) (hw : Derives Γ (omega w))
    (hg : Derives Γ (SchemaIndexSyntax.graph site w n scopes g)) (hz : Derives Γ (empty z)) :
    Derives Γ ((edge g z y).iff (empty y)) := by
  let B := body site w n scopes g
  let Δ := Context.add B (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 B _ hg
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw B)
  have hz2 := of_eq (empty_rename z (old 2)) (HornBinderRules.under_body 2 hz B)
  have ho := matrix_zero_iff (HornBinderRules.zf_body 2 hZ B) site (old 2 w) (old 2 n) (fun i => old 2 (scopes i))
    (old 2 g) (slot 2) (old 2 z) (old 2 y) hw2 hB hz2
  exact of_eq (by simp only [Formula.iff, Formula.rename, edge_rename, empty_rename]) ho

end PPAC.Migration.Internal.SchemaIndexFacts
