import PPAC.Migration.Internal.HornLookupSearchCondition

/-! 原字段行实际编码与有界全表轨迹组成成功图，无预给外部行码。 -/
namespace PPAC.Migration.Internal.HornLookupSomeSyntax
open Source SourceAlgebra SourceLogic HornLookupRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

def returned {m} (w n i y : Fin m) : Formula m := .ex
  ((row w.castSucc n.castSucc i.castSucc y.castSucc (Fin.last m)).conj (HornLookupSearchCondition.condition w.castSucc (Fin.last m)))

def hasOutput {m} (w n i : Fin m) : Formula m := .ex (returned w.castSucc n.castSucc i.castSucc (Fin.last m))

def noOutput {m} (w n i : Fin m) : Formula m := (hasOutput w n i).neg

theorem returned_rename {m k} (w n i y : Fin m) (ρ : Fin m → Fin k) :
    (returned w n i y).rename ρ = returned (ρ w) (ρ n) (ρ i) (ρ y) := by
  simp only [returned, Formula.rename, row_rename, HornLookupSearchCondition.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem hasOutput_rename {m k} (w n i : Fin m) (ρ : Fin m → Fin k) :
    (hasOutput w n i).rename ρ = hasOutput (ρ w) (ρ n) (ρ i) := by
  simp only [hasOutput, Formula.rename, returned_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem noOutput_rename {m k} (w n i : Fin m) (ρ : Fin m → Fin k) :
    (noOutput w n i).rename ρ = noOutput (ρ w) (ρ n) (ρ i) := by
  simp only [noOutput, Formula.neg, Formula.rename, hasOutput_rename]

theorem intro_returned {m} {Γ : Context m} (w n i y r : Fin m) (hr : Derives Γ (row w n i y r))
    (hc : Derives Γ (HornLookupSearchCondition.condition w r)) : Derives Γ (returned w n i y) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, row_rename, HornLookupSearchCondition.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr hc)

end PPAC.Migration.Internal.HornLookupSomeSyntax
