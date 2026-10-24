import PPAC.Migration.Internal.InstantiateOperationFrameRoot
import PPAC.Migration.Internal.InstantiateFrameTerm

/-! 实际零深度 InstantiateTop 环境上的项程序和 coded mixed substitution；无兼容frame前提。 -/
namespace PPAC.Migration.Internal.InstantiateTopTermOperation
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P b A R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w A b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode z P n q).iff
      (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) :=
  InstantiateFrameTerm.program_iff hZ w mode z P A b z b R S n q hw
    (InstantiateOperationFrameRoot.from_actual_input hZ w mode z P b A R S hw hm hz he) ht

theorem coded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P b A R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w A b n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode z P n q).iff
      (SyntaxCodedMixedTermSyntax.substituted w R S A b z b n q)) :=
  InstantiateFrameTerm.coded_iff hZ w mode z P A b z b R S n q hw
    (InstantiateOperationFrameRoot.from_actual_input hZ w mode z P b A R S hw hm hz he) ht

theorem guarded_coded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P b A R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S)) :
    Derives Γ (((SyntaxTermSyntax.term w A b n).conj (OriginalTransformRowSyntax.run 1 w mode z P n q)).iff
      (SyntaxCodedMixedTermSyntax.substituted w R S A b z b n q)) :=
  InstantiateFrameTerm.guarded_coded_iff hZ w mode z P A b z b R S n q hw
    (InstantiateOperationFrameRoot.from_actual_input hZ w mode z P b A R S hw hm hz he)

end PPAC.Migration.Internal.InstantiateTopTermOperation
