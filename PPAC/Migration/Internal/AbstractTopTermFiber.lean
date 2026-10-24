import PPAC.Migration.Internal.AbstractTopTermOperation
import PPAC.Migration.Internal.OriginalNumericTermValueTransfer

/-! 实际零深度抽象码表给出全部内部纯项的原Run1有类型唯一纤维，正式消去列表接口Promise。 -/
namespace PPAC.Migration.Internal.AbstractTopTermFiber
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalNumericTermValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem agreement {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a B n)) : Derives Γ (OriginalNumericTermValueSyntax.agreement w mode z P R S n) := by
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 mode Fin.castSucc) (Derives.rename Fin.castSucc hm)
  have hd1 := of_eq (OriginalTermTraceSyntax.metadata_rename w z P Fin.castSucc) (Derives.rename Fin.castSucc hd)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (Derives.rename Fin.castSucc hz)
  have he1 := of_eq (SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename w a b A B R S Fin.castSucc) (Derives.rename Fin.castSucc he)
  have ht1 := of_eq (SyntaxTermSyntax.term_rename w a B n Fin.castSucc) (Derives.rename Fin.castSucc ht)
  exact AbstractTopTerm.program_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc mode.castSucc z.castSucc P.castSucc
    a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m) hw1 hm1 hd1 hz1 he1 ht1

theorem fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S n : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (ht : Derives Γ (SyntaxTermSyntax.term w a B n)) : Derives Γ (OriginalNumericTermValueSyntax.fiber w mode z P A b n) := by
  have ha := agreement hZ w mode z P a b A B R S n hw hm hd hz he ht
  have hL := SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S he
  have hf := TermTransformProgramValue.actual_fiber hZ w R S a B A b n hw (.conjI hL ht)
  exact OriginalNumericTermValueTransfer.fiber_of_program w mode z P R S a B A b n ha hf

theorem promise {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S)) :
    Derives Γ (OriginalNumericTermValueSyntax.promise w mode z P a B A b) := by
  apply Derives.allI
  apply Derives.impI
  let E := SyntaxTermSyntax.term w.castSucc a.castSucc B.castSucc (Fin.last m)
  let Δ := Context.add E (Context.image Formula.raise Γ)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have hm1 := of_eq (SyntaxNumeralSyntax.numeral_rename 1 mode Fin.castSucc) (under hm E)
  have hd1 := of_eq (OriginalTermTraceSyntax.metadata_rename w z P Fin.castSucc) (under hd E)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz E)
  have he1 := of_eq (SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename w a b A B R S Fin.castSucc) (under he E)
  exact fiber (ZFContext.under hZ E) w.castSucc mode.castSucc z.castSucc P.castSucc a.castSucc b.castSucc A.castSucc B.castSucc R.castSucc S.castSucc (Fin.last m)
    hw1 hm1 hd1 hz1 he1 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.AbstractTopTermFiber
