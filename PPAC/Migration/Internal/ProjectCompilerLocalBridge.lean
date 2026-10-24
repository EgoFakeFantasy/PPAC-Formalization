import PPAC.Migration.Internal.ProjectCompilerQueryBridge

/-! The actual history-dependent step equals the direct twelve-case Compiler criterion. -/
namespace PPAC.Migration.Internal.ProjectCompilerLocalBridge
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem local_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c h n b q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.carrier w a c))
    (hg : Derives Γ (ProjectCompilerRecursionSyntax.graph w c h n)) :
    Derives Γ ((ProjectCompilerLocalSyntax.localStep w b q h n).iff (ProjectCompilerRecursiveSyntax.criterion w n b q)) := by
  have he := ProjectCompilerQueryBridge.all_queries hZ w a c h n hw hn hc hg
  apply ProjectSourceCodeCongruence.conj_congr (ProjectSourceTypeLocalTransfer.iff_refl _)
  apply ProjectSourceCodeCongruence.conj_congr (ProjectSourceTypeLocalTransfer.iff_refl _)
  apply ProjectSourceCodeCongruence.ex_congr
  have he1 := of_eq (ProjectCompilerQuerySyntax.equivalent_rename ProjectCompilerLocalSyntax.readMatrix (ProjectCompilerLocalSyntax.one h)
    ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n Fin.castSucc) (Derives.rename Fin.castSucc he)
  exact ProjectSourceCodeCongruence.conj_congr (ProjectSourceTypeLocalTransfer.iff_refl _)
    (ProjectCompilerCaseTransport.all_cases ProjectCompilerLocalSyntax.readMatrix (ProjectCompilerLocalSyntax.one h.castSucc)
      ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w.castSucc)
      w.castSucc b.castSucc (Fin.last m) n.castSucc q.castSucc he1)

end PPAC.Migration.Internal.ProjectCompilerLocalBridge
