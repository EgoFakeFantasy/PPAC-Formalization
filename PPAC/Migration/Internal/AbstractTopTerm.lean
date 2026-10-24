import PPAC.Migration.Internal.AbstractTopVariable
import PPAC.Migration.Internal.OriginalTermScopeElimination
import PPAC.Migration.Internal.TermTransformProgramCorrectness

/-! 原mode1零深度全部纯项运行接实际首槽抽象码表的独立程序和原编码混合项操作。 -/
namespace PPAC.Migration.Internal.AbstractTopTerm
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem program_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a B n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode z P n q).iff
      (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) := by
  apply OriginalTermScopeElimination.eliminate w a B n _ ht
  intro bound
  let D := SyntaxTermSyntax.branchWitness bound w (SyntaxTermSyntax.limit bound a B) n
  let Δ := Context.add D (Context.image Formula.raise Γ)
  have hZ1 := ZFContext.under hZ D
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw D)
  have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 mode Fin.castSucc) (under hm D)
  have hd1 := of_eq (OriginalTermTraceSyntax.metadata_rename w z P Fin.castSucc) (under hd D)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz D)
  have he1 := of_eq (SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename w a b A B R S Fin.castSucc) (under he D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hbranch : Derives Δ ((Formula.mem (Fin.last m) (SyntaxTermSyntax.limit bound a.castSucc B.castSucc)).conj
      (SyntaxVariableSyntax.code bound w.castSucc (Fin.last m) n.castSucc)) :=
    of_eq (by simp only [D, SyntaxTermSyntax.branchWitness, SyntaxTermSyntax.limit_map]) hD
  have ho := AbstractTopVariable.program_at_variable hZ1 bound w.castSucc mode.castSucc z.castSucc P.castSucc
    a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc n.castSucc q.castSucc (Fin.last m)
    hw1 hm1 hd1 hz1 he1 (.conjL hbranch) (.conjR hbranch)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, TermTransformProgramSyntax.run_rename]) ho

theorem coded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a B n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode z P n q).iff
      (SyntaxCodedMixedTermSyntax.substituted w R S a B A b n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (program_iff hZ w mode z P a b A B R S n q hw hm hd hz he ht)
    (TermTransformProgramCorrectness.at_typed_term hZ w R S a B A b n q hw
      (SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S he) ht)

end PPAC.Migration.Internal.AbstractTopTerm
