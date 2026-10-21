import PPAC.Migration.Internal.SyntaxTypeRecursionSyntax

/-! 原Separation和Extensionality实际消去集合值算子的总单值前提，所有内部输入均覆盖。 -/
namespace PPAC.Migration.Internal.SyntaxTypeRecursionStep
open Source SourceAlgebra SourceLogic GraphSyntax SyntaxTypeStateSyntax SyntaxTypeRecursionSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) :
    Derives Γ (OrdinalRecursionTotal.total matrix ρ) := by
  simp only [OrdinalRecursionTotal.total, OrdinalRecursionTotal.hasValue, matrix_operator, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (OrdinalSyntax.ordinal (Fin.last m).castSucc).conj (functionOn (Fin.last (m+1)) (Fin.last m).castSucc)
  exact SyntaxTypeStateExistence.exists_state (ZFContext.under_two hZ B) _ _ _ _

theorem deterministic {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) :
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
  let Y := state (ρ 0).castSucc.castSucc.castSucc.castSucc (ρ 1).castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc
  let U := state (ρ 0).castSucc.castSucc.castSucc.castSucc (ρ 1).castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))
  have hZ4 := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ2 Fin.castSucc) Fin.castSucc) Y) U
  exact SyntaxTypeStateExistence.unique hZ4 _ _ _ _ _ _ (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.SyntaxTypeRecursionStep
