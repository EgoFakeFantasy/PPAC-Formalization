import PPAC.Migration.OrdinalLeastLogic

/-! 非空可定义序数性质的实际最小序数存在；使用对象成员极小元及原序数比较。 -/
namespace PPAC.Migration.OrdinalLeastExistence
open Source SourceAlgebra SourceLogic OrdinalLeastSyntax
open ReplacementPredicates (paramsUp)

theorem exists_least {n m} {Γ : Context m} (p : Formula (n+1)) (ρ : Fin n → Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0))
    (hmsep : Derives Γ ((Source.SetLanguage.separation (matrix p).neg.neg).rename Fin.elim0))
    (htc : Derives Γ (ObjectTransitiveCover.coverSentence.rename Fin.elim0))
    (hh : Derives Γ (has p ρ)) : Derives Γ (leastExists p ρ) := by
  have hg : Derives Γ (GlobalMinimalSyntax.has (matrix p) ρ) := by
    simpa only [GlobalMinimalSyntax.has, matrix_pred, has] using hh
  have hx := GlobalMinimal.minimal_exists (matrix p) ρ hmsep hf htc hg
  let A := GlobalMinimalSyntax.minimal (matrix p) (paramsUp ρ) (Fin.last m)
  let Ξ := Context.add A (Context.image Formula.raise Γ)
  change Derives Γ (.ex A) at hx
  apply Derives.exE (p := A) hx
  have heA : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he A
  have hfA : Derives Ξ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf A
  have hsA : Derives Ξ ((Source.SetLanguage.separation OrdinalDifference.outsideMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hs A
  have hA : Derives Ξ A := .hyp (Or.inl rfl)
  have hl := OrdinalLeastLogic.least_of_minimal p (paramsUp ρ) (Fin.last m) heA hfA hsA hA
  have hout : Derives Ξ (leastExists p (paramsUp ρ)) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, least_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact hl
  simpa only [Formula.raise, leastExists_rename] using hout
end PPAC.Migration.OrdinalLeastExistence
