import PPAC.Migration.GraphPointwiseSyntax
import PPAC.Migration.RestrictionSyntax

/-! 以完整entriesOn排除杂项，把逐边推导升级为实际图集合的成员推导。 -/
namespace PPAC.Migration.GraphPointwiseEntries
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic GraphPointwiseSyntax OrderedPairElimination

theorem member_from_edge {m} {Γ : Context m} (g p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (ordered p x y)) (hg : Derives Γ (edge g x y)) : Derives Γ (.mem p g) := by
  let Q := (Formula.mem (Fin.last m) g.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim g x y _ hg
  have heQ : Derives Γq (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Q
  have hpQ : Derives Γq (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under hp Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  exact mem_subst (eq_symm (OrderedPairLogic.unique p.castSucc (Fin.last m) x.castSucc y.castSucc heQ hpQ (.conjR hQ))) (.conjL hQ)

theorem membership {m} {Γ : Context m} (f g d p : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (entriesOn f d)) (hi : Derives Γ (edgeIncluded f g)) (hp : Derives Γ (.mem p f)) :
    Derives Γ (.mem p g) := by
  have hw := Derives.impE (entries_at f d p hf) hp
  let B := entryWitnesses d p
  let Γb := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply entry_elim d p _ hw
  have heB : Derives Γb (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under_two he B
  have hiB : Derives Γb (edgeIncluded f.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, edgeIncluded_rename] using under_two hi B
  have hpB : Derives Γb (.mem p.castSucc.castSucc f.castSucc.castSucc) := under_two hp B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hg := Derives.impE (edgeIncluded_at f.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hiB)
    (edge_intro f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) p.castSucc.castSucc hpB (.conjR hB))
  exact member_from_edge g.castSucc.castSucc p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) heB (.conjR hB) hg

theorem graph_subset {m} {Γ : Context m} (f g d : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (entriesOn f d)) (hi : Derives Γ (edgeIncluded f g)) : Derives Γ (RestrictionSyntax.subset f g) := by
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hf' : Derives (Context.image Formula.raise Γ) (entriesOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, entriesOn_rename] using Derives.rename Fin.castSucc hf
  have hi' : Derives (Context.image Formula.raise Γ) (edgeIncluded f.castSucc g.castSucc) := by
    simpa only [Formula.raise, edgeIncluded_rename] using Derives.rename Fin.castSucc hi
  apply Derives.impI
  exact membership f.castSucc g.castSucc d.castSucc (Fin.last m) (add he' _) (add hf' _) (add hi' _) (.hyp (Or.inl rfl))

theorem equal_of_edges {m} {Γ : Context m} (f g d e : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (entriesOn f d)) (hg : Derives Γ (entriesOn g e)) (hi : Derives Γ (sameEdges f g)) :
    Derives Γ (.equal f g) := by
  have hfg := graph_subset f g d he hf (.conjL hi)
  have hgf := graph_subset g f e he hg (.conjR hi)
  apply Derives.impE (extensionality_instance f g he)
  apply Derives.allI
  have hfg' : Derives (Context.image Formula.raise Γ) (RestrictionSyntax.subset f.castSucc g.castSucc) := by
    simpa only [Formula.raise, RestrictionSyntax.subset_rename] using Derives.rename Fin.castSucc hfg
  have hgf' : Derives (Context.image Formula.raise Γ) (RestrictionSyntax.subset g.castSucc f.castSucc) := by
    simpa only [Formula.raise, RestrictionSyntax.subset_rename] using Derives.rename Fin.castSucc hgf
  exact .conjI (RestrictionSyntax.subset_at f.castSucc g.castSucc (Fin.last m) hfg')
    (RestrictionSyntax.subset_at g.castSucc f.castSucc (Fin.last m) hgf')
end PPAC.Migration.GraphPointwiseEntries
