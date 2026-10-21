import PPAC.Migration.GraphFamilyExistence
import PPAC.Migration.GraphPointwise
import PPAC.Migration.RestrictionAlgebra
import PPAC.Migration.TransitiveCoverLogic

/-! 任意内部相容图族的并限制到某成员完整定义域时，实际等于该成员；不重新选历史。 -/
namespace PPAC.Migration.GraphFamilyRestriction
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic InsertSyntax RestrictionSyntax
open GraphFamilySyntax GraphFamilyEdges

theorem edge_to_member {m} {Γ : Context m} (g c h d x y : Fin m)
    (hu : Derives Γ (unionOf g c)) (hc : Derives Γ (compatible c)) (hm : Derives Γ (.mem h c))
    (hf : Derives Γ (functionOn h d)) (hx : Derives Γ (.mem x d)) (hy : Derives Γ (edge g x y)) :
    Derives Γ (edge h x y) := by
  have hv := GraphProperties.output_exists h d x hf hx
  let V := edge h.castSucc x.castSucc (Fin.last m)
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have huV : Derives Ξ (unionOf g.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu V
  have hcV : Derives Ξ (compatible c.castSucc) := by
    simpa only [Formula.raise, compatible_rename] using under hc V
  have hmV : Derives Ξ (.mem h.castSucc c.castSucc) := under hm V
  have hyV : Derives Ξ (edge g.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hy V
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hgv := edge_into_union g.castSucc c.castSucc h.castSucc x.castSucc (Fin.last m) huV hmV hV
  have heq := GraphFamilyValues.single_valued g.castSucc c.castSucc x.castSucc (Fin.last m) y.castSucc huV hcV hgv hyV
  simpa only [Formula.raise, edge_rename] using GraphPointwiseSyntax.edge_subst_output h.castSucc x.castSucc (Fin.last m) y.castSucc heq hV

theorem member_restriction {m} {Γ : Context m} (g c h d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hu : Derives Γ (unionOf g c)) (hc : Derives Γ (compatible c)) (hm : Derives Γ (.mem h c))
    (hf : Derives Γ (functionOn h d)) : Derives Γ (restrict h g d) := by
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hu' : Derives Δ (unionOf g.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have hc' : Derives Δ (compatible c.castSucc) := by
    simpa only [Formula.raise, compatible_rename] using Derives.rename Fin.castSucc hc
  have hm' : Derives Δ (.mem h.castSucc c.castSucc) := Derives.rename Fin.castSucc hm
  have hf' : Derives Δ (functionOn h.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (.impE (add (subset_at h.castSucc g.castSucc (Fin.last m)
      (TransitiveCoverLogic.subset_union g.castSucc c.castSucc h.castSucc hu' hm')) _) (.hyp (Or.inl rfl)))
      (.impE (add (entries_at h.castSucc d.castSucc (Fin.last m) (.conjL hf')) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let P := (Formula.mem (Fin.last m) g.castSucc).conj (entryOn d.castSucc (Fin.last m))
    let Γp := Context.add P Δ
    have hP : Derives Γp P := .hyp (Or.inl rfl)
    let B := entryWitnesses d.castSucc (Fin.last m)
    let Ξ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γp))
    apply entry_elim d.castSucc (Fin.last m) _ (.conjR hP)
    have heB : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using OrderedPairElimination.under_two (add he' P) B
    have huB : Derives Ξ (unionOf g.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc) := by
      simpa only [Formula.raise, unionOf_rename] using OrderedPairElimination.under_two (add hu' P) B
    have hcB : Derives Ξ (compatible c.castSucc.castSucc.castSucc) := by
      simpa only [Formula.raise, compatible_rename] using OrderedPairElimination.under_two (add hc' P) B
    have hmB : Derives Ξ (.mem h.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc) :=
      OrderedPairElimination.under_two (add hm' P) B
    have hfB : Derives Ξ (functionOn h.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc) := by
      simpa only [Formula.raise, functionOn_rename] using OrderedPairElimination.under_two (add hf' P) B
    have hpB : Derives Ξ (.mem (Fin.last m).castSucc.castSucc g.castSucc.castSucc.castSucc) :=
      OrderedPairElimination.under_two (.conjL hP) B
    have hB : Derives Ξ B := .hyp (Or.inl rfl)
    have hgEdge := edge_intro g.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
      (Fin.last m).castSucc.castSucc hpB (.conjR hB)
    have hhEdge := edge_to_member g.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc
      d.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) huB hcB hmB hfB (.conjL hB) hgEdge
    exact GraphPointwiseEntries.member_from_edge h.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2)) heB (.conjR hB) hhEdge
theorem input_into_union {m} {Γ : Context m} (g c h x : Fin m)
    (hu : Derives Γ (unionOf g c)) (hm : Derives Γ (.mem h c)) (hx : Derives Γ (hasEdge h x)) :
    Derives Γ (hasEdge g x) := by
  let Y := edge h.castSucc x.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hx
  apply Derives.exE (p := Y) hx
  have huY : Derives Ξ (unionOf g.castSucc c.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu Y
  have hmY : Derives Ξ (.mem h.castSucc c.castSucc) := under hm Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hed := edge_into_union g.castSucc c.castSucc h.castSucc x.castSucc (Fin.last m) huY hmY hY
  simpa only [Formula.raise, hasEdge_rename] using GraphDomainBound.has_edge_intro g.castSucc x.castSucc (Fin.last m) hed

end PPAC.Migration.GraphFamilyRestriction
