import PPAC.Migration.Internal.InstantiateFormulaCorrectnessInduction
import PPAC.Migration.Internal.InstantiateOperationFrameRoot

/-! 实际空绑定目标的InstantiateTop环境给出原mode2完整公式运行，无元数据或兼容性额外前提。 -/
namespace PPAC.Migration.Internal.InstantiateTopFormula
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem run_iff_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode z P b A R S q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n A b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode z P n q).iff
      (FormulaTransformExecutionSyntax.executed w R S A b z b n q)) :=
  InstantiateFormulaCorrectnessInduction.run_iff_execution hZ w n mode z P A b z b R S q hw
    (InstantiateOperationFrameRoot.from_actual_input hZ w mode z P b A R S hw hm hz he) hn

theorem run_iff_program {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n mode z P b A R S h q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n A b))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode z P n q).iff
      (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S A b z b h n q)) :=
  InstantiateFormulaCorrectnessInduction.run_iff_program hZ w n mode z P A b z b R S h q hw
    (InstantiateOperationFrameRoot.from_actual_input hZ w mode z P b A R S hw hm hz he) hn hg

end PPAC.Migration.Internal.InstantiateTopFormula
