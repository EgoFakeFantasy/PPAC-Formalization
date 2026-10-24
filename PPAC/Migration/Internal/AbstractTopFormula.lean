import PPAC.Migration.Internal.AbstractFormulaCorrectnessInduction
import PPAC.Migration.Internal.AbstractOperationFrameRoot

/-! 实际 AbstractFreeTop 环境在空深度提供 mode1 全公式运行证书。 -/
namespace PPAC.Migration.Internal.AbstractTopFormula
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem run_iff_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode z P a b A B R S q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a B)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode z P n q).iff
      (FormulaTransformExecutionSyntax.executed w R S a B A b n q)) :=
  AbstractFormulaCorrectnessInduction.run_iff_execution hZ w n mode z P a B A b R S q hw
    (AbstractOperationFrameRoot.from_actual hZ w mode z P a b A B R S hw hm hd hz he) hn

theorem run_iff_program {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode z P a b A B R S h q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a B))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode z P n q).iff
      (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a B A b h n q)) :=
  AbstractFormulaCorrectnessInduction.run_iff_program hZ w n mode z P a B A b R S h q hw
    (AbstractOperationFrameRoot.from_actual hZ w mode z P a b A B R S hw hm hd hz he) hn hg

end PPAC.Migration.Internal.AbstractTopFormula
