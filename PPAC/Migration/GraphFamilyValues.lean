import PPAC.Migration.GraphFamilyEdges

/-! 相容性在实际并图中保证所有输入上的单值性。 -/
namespace PPAC.Migration.GraphFamilyValues
open Source SourceAlgebra SourceLogic GraphSyntax GraphLogic InsertSyntax GraphFamilySyntax GraphFamilyEdges

theorem single_valued {m} {Γ : Context m} (g f x y z : Fin m)
    (hu : Derives Γ (unionOf g f)) (hc : Derives Γ (compatible f))
    (hy : Derives Γ (edge g x y)) (hz : Derives Γ (edge g x z)) : Derives Γ (.equal y z) := by
  have heY := edge_from_union g f x y hu hy
  have heZ := edge_from_union g f x z hu hz
  let H := (Formula.mem (Fin.last m) f.castSucc).conj (edge (Fin.last m) x.castSucc y.castSucc)
  let Γh := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at heY
  apply Derives.exE (p := H) heY
  have hcH : Derives Γh (compatible f.castSucc) := by
    simpa only [Formula.raise, compatible_rename] using under hc H
  have heZH : Derives Γh (memberEdge f.castSucc x.castSucc z.castSucc) := by
    simpa only [Formula.raise, memberEdge_rename] using under heZ H
  let K := (Formula.mem (Fin.last (m+1)) f.castSucc.castSucc).conj
    (edge (Fin.last (m+1)) x.castSucc.castSucc z.castSucc.castSucc)
  let Γk := Context.add K (Context.image Formula.raise Γh)
  change Derives Γh (.ex K) at heZH
  apply Derives.exE (p := K) heZH
  have hcK : Derives Γk (compatible f.castSucc.castSucc) := by
    simpa only [Formula.raise, compatible_rename] using under hcH K
  have hH : Derives Γh H := .hyp (Or.inl rfl)
  have hHK : Derives Γk ((Formula.mem (Fin.last m).castSucc f.castSucc.castSucc).conj
      (edge (Fin.last m).castSucc x.castSucc.castSucc y.castSucc.castSucc)) := by
    simpa only [Formula.raise, H, Formula.rename, edge_rename] using under hH K
  have hK : Derives Γk K := .hyp (Or.inl rfl)
  have ha := Derives.impE (.impE (compatible_at f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hcK)
    (.conjL hHK)) (.conjL hK)
  exact .impE (.impE (agrees_at (Fin.last m).castSucc (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc z.castSucc.castSucc ha)
    (.conjR hHK)) (.conjR hK)
end PPAC.Migration.GraphFamilyValues
