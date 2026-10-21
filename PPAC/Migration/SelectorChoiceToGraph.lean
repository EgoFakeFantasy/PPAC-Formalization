import PPAC.Migration.SelectedGraphChoice

/-! 原不交族选择集AC推出原图AC；所有标签行、族、选择集和图均为内部见证。 -/
namespace PPAC.Migration.SelectorChoiceToGraph
open Source SourceAlgebra SourceLogic ChoiceSyntax

theorem selector_ac_at {m} {Γ : Context m} (b : Fin m)
    (hc : Derives Γ (selectorAC.rename Fin.elim0)) :
    Derives Γ (((familyNonempty b).conj (disjoint b)).imp (selectorExists b)) := by
  have hi := specialize_close (((familyNonempty (0 : Fin 1)).conj (disjoint 0)).imp (selectorExists 0)) (fun _ => b) hc
  simpa only [Formula.rename, familyNonempty_rename, disjoint_rename, selectorExists_rename] using hi

theorem from_AC {m} {Γ : Context m} (hA : TaggedFamilyContext.Evidence Γ) (a : Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement SelectedPairSyntax.matrix).rename Fin.elim0))
    (hc : Derives Γ (selectorAC.rename Fin.elim0)) (ha : Derives Γ (familyNonempty a)) :
    Derives Γ (graphExists a) := by
  have hb := TaggedFamilyLogic.exists_admissible hA a ha
  let B := TaggedFamilySyntax.admissible (Fin.last m) a.castSucc
  let Γb := Context.add B (Context.image Formula.raise Γ)
  change Derives Γ (.ex B) at hb
  apply Derives.exE (p := B) hb
  have hAB := TaggedFamilyContext.under hA B
  have hrB : Derives Γb ((Source.SetLanguage.replacement SelectedPairSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hr B
  have hcB : Derives Γb (selectorAC.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hc B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hs := Derives.impE (selector_ac_at (Fin.last m) hcB) (.conjR hB)
  let S := selector (Fin.last (m+1)) (Fin.last m).castSucc
  let Ξ := Context.add S (Context.image Formula.raise Γb)
  change Derives Γb (.ex S) at hs
  apply Derives.exE (p := S) hs
  have hAS := TaggedFamilyContext.under hAB S
  have hrS : Derives Ξ ((Source.SetLanguage.replacement SelectedPairSyntax.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hrB S
  have hfS : Derives Ξ (TaggedFamilySyntax.family (Fin.last m).castSucc a.castSucc.castSucc) := by
    simpa only [Formula.raise, TaggedFamilySyntax.family_rename] using under (.conjL hB) S
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  simpa only [Formula.raise, graphExists_rename] using
    SelectedGraphChoice.from_selector hAS (Fin.last (m+1)) (Fin.last m).castSucc a.castSucc.castSucc hrS hfS hS
end PPAC.Migration.SelectorChoiceToGraph
