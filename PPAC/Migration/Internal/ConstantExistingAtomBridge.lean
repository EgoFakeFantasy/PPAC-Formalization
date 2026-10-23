import PPAC.Migration.Internal.OriginalEqualityExistingAtom

/-! 原常量数值数据与既有零元公式程序的精确双条件；背景上下文守卫显式保留。 -/
namespace PPAC.Migration.Internal.ConstantExistingAtomBridge
open Source SourceAlgebra SourceLogic

theorem constant_iff {m} {Γ : Context m} (truth : Bool) (w a b c d n q : Fin m)
    (hs : Derives Γ (SyntaxTermSyntax.contexts w a b)) (ht : Derives Γ (SyntaxTermSyntax.contexts w c d)) :
    Derives Γ ((OriginalFormulaLocalData.constant (SyntaxAtomSyntax.nullaryTag truth) w n q).iff
      (FormulaTransformAtomSyntax.nullary truth w a b c d n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    have he : Derives (Context.add (OriginalFormulaLocalData.constant (SyntaxAtomSyntax.nullaryTag truth) w n q) Γ) (OriginalFormulaLocalData.constant (SyntaxAtomSyntax.nullaryTag truth) w n q) := .hyp (Or.inl rfl)
    exact .conjI (.conjI (add hs _) (.conjL he)) (.conjI (add ht _) (.conjR he))
  · apply Derives.impI
    have he : Derives (Context.add (FormulaTransformAtomSyntax.nullary truth w a b c d n q) Γ) (FormulaTransformAtomSyntax.nullary truth w a b c d n q) := .hyp (Or.inl rfl)
    exact .conjI (.conjR (.conjL he)) (.conjR (.conjR he))

end PPAC.Migration.Internal.ConstantExistingAtomBridge
