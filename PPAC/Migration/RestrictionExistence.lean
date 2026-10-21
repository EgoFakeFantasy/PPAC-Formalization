import PPAC.Migration.RestrictionAlgebra

/-! 分离构造的限制集合实际是给定子定义域上的完整原函数图。 -/
namespace PPAC.Migration.RestrictionExistence
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax RestrictionSyntax

theorem exists_function_restriction {m} {Γ : Context m} (f d b : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0))
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hb : Derives Γ (subset b d)) : Derives Γ (existsRestriction f b) := by
  have hg := exists_restrict f b hs
  let G := restrict (Fin.last m) f.castSucc b.castSucc
  let Γg := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hrG : Derives Γg G := .hyp (Or.inl rfl)
  have heG : Derives Γg (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he G
  have hfG : Derives Γg (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hf G
  have hbG : Derives Γg (subset b.castSucc d.castSucc) := by
    simpa only [Formula.raise, subset_rename] using under hb G
  have hfun := RestrictionFunction.function_restrict (Fin.last m) f.castSucc d.castSucc b.castSucc hfG hbG hrG
  have hlaw := RestrictionEdges.all_edges (Fin.last m) f.castSucc b.castSucc heG hrG
  have hw : Derives Γg (witness (Fin.last m) f.castSucc b.castSucc) := .conjI hrG (.conjI hfun hlaw)
  have ho : Derives Γg (existsRestriction f.castSucc b.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, witness_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hw
  simpa only [Formula.raise, existsRestriction_rename] using ho
end PPAC.Migration.RestrictionExistence
