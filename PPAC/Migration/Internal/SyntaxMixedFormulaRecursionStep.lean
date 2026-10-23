import PPAC.Migration.Internal.SyntaxMixedFormulaRecursionSyntax

/-! 原Separation和Extensionality消去具体混合替换集合值算子的总单值前提；覆盖全部内部历史。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaRecursionStep
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxMixedFormulaOperatorSyntax SyntaxMixedFormulaRecursionSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m) :
    Derives Γ (OrdinalRecursionTotal.total matrix ρ) := by
  simp only [OrdinalRecursionTotal.total, OrdinalRecursionTotal.hasValue, matrix_operator, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (OrdinalSyntax.ordinal (Fin.last m).castSucc).conj (functionOn (Fin.last (m+1)) (Fin.last m).castSucc)
  exact SyntaxMixedFormulaOperatorExistence.exists_value (ZFContext.under_two hZ B) _ _ _

theorem deterministic {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 1 → Fin m) :
    Derives Γ (OrdinalRecursionDeterminism.deterministic matrix ρ) := by
  simp only [OrdinalRecursionDeterminism.deterministic, OrdinalRecursionDeterminism.functional, matrix_operator, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (OrdinalSyntax.ordinal (Fin.last m).castSucc).conj (functionOn (Fin.last (m+1)) (Fin.last m).castSucc)
  have hZ2 := ZFContext.under_two hZ B
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let Y := value (ρ 0).castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc
  let U := value (ρ 0).castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))
  have hZ4 := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ2 Fin.castSucc) Fin.castSucc) Y) U
  exact SyntaxMixedFormulaOperatorExistence.unique hZ4 _ _ _ _ _ (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxMixedFormulaRecursionStep
