import PPAC.Migration.Internal.OriginalLogicalProgram

/-! 实际独立程序递归图中的read与完整执行关系；全部域与状态保留为对象集合。 -/
namespace PPAC.Migration.Internal.OriginalHistoryRead
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem read_iff_executed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w h D x R S a b c d q : Fin m) (hw : Derives Γ (omega w))
    (hD : Derives Γ (OrdinalSyntax.ordinal D)) (hx : Derives Γ (.mem x D))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h D)) :
    Derives Γ ((FormulaTransformHistorySyntax.read w h x R S a b c d q).iff
      (FormulaTransformExecutionSyntax.executed w R S a b c d x q)) := by
  have hOld := Derives.impE (.conjL (FormulaTransformRecursionCorrectness.graph_iff hZ w h D hw)) hg
  have hRead := SyntaxMixedFormulaJudgment.read_iff hZ w h D x R S a b c d q hD hx hOld
  have hExec := FormulaTransformRecursionCorrectness.execution_iff hZ w R S a b c d x q hw
  exact SyntaxTypeLocalTransfer.iff_trans hRead (.conjI (.conjR hExec) (.conjL hExec))

end PPAC.Migration.Internal.OriginalHistoryRead
