import PPAC.Migration.GraphPointwiseEntries

/-! 任意相容函数图的域包含推出图包含；同域时推出图相等。 -/
namespace PPAC.Migration.GraphPointwise
open Source SourceAlgebra SourceLogic GraphSyntax GraphLogic GraphFamilySyntax GraphPointwiseSyntax RestrictionSyntax

theorem transfer_edge {m} {Γ : Context m} (f g d e x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g e))
    (hd : Derives Γ (subset d e)) (ha : Derives Γ (agrees f g)) (hy : Derives Γ (edge f x y)) :
    Derives Γ (edge g x y) := by
  have hx := Derives.impE (subset_at d e x hd) (GraphProperties.domain_of_edge f d x y he hf hy)
  have hv := GraphProperties.output_exists g e x hg hx
  let Z := edge g.castSucc x.castSucc (Fin.last m)
  let Γz := Context.add Z (Context.image Formula.raise Γ)
  change Derives Γ (.ex Z) at hv
  apply Derives.exE (p := Z) hv
  have haZ : Derives Γz (agrees f.castSucc g.castSucc) := by
    simpa only [Formula.raise, agrees_rename] using under ha Z
  have hyZ : Derives Γz (edge f.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hy Z
  have hZ : Derives Γz Z := .hyp (Or.inl rfl)
  have heq := Derives.impE (Derives.impE (agrees_at f.castSucc g.castSucc x.castSucc y.castSucc (Fin.last m) haZ) hyZ) hZ
  have hr := edge_subst_output g.castSucc x.castSucc (Fin.last m) y.castSucc (eq_symm heq) hZ
  simpa only [Formula.raise, edge_rename] using hr

theorem included_of_agrees {m} {Γ : Context m} (f g d e : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g e))
    (hd : Derives Γ (subset d e)) (ha : Derives Γ (agrees f g)) : Derives Γ (edgeIncluded f g) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hf' : Derives Δ (functionOn f.castSucc.castSucc d.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hf)
  have hg' : Derives Δ (functionOn g.castSucc.castSucc e.castSucc.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  have hd' : Derives Δ (subset d.castSucc.castSucc e.castSucc.castSucc) := by
    simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hd)
  have ha' : Derives Δ (agrees f.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, agrees_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)
  apply Derives.impI
  exact transfer_edge f.castSucc.castSucc g.castSucc.castSucc d.castSucc.castSucc e.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (add he' _) (add hf' _) (add hg' _) (add hd' _) (add ha' _) (.hyp (Or.inl rfl))

theorem subset_of_agrees {m} {Γ : Context m} (f g d e : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g e))
    (hd : Derives Γ (subset d e)) (ha : Derives Γ (agrees f g)) : Derives Γ (subset f g) :=
  GraphPointwiseEntries.graph_subset f g d he (.conjL hf) (included_of_agrees f g d e he hf hg hd ha)

theorem equal_of_agrees {m} {Γ : Context m} (f g d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hg : Derives Γ (functionOn g d)) (ha : Derives Γ (agrees f g)) :
    Derives Γ (.equal f g) := by
  have hr : Derives Γ (subset d d) := .allI (.impI (.hyp (Or.inl rfl)))
  exact GraphPointwiseEntries.equal_of_edges f g d d he (.conjL hf) (.conjL hg)
    (.conjI (included_of_agrees f g d d he hf hg hr ha)
      (included_of_agrees g f d d he hg hf hr (agrees_symm f g ha)))
end PPAC.Migration.GraphPointwise
