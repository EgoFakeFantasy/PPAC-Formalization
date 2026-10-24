import PPAC.Migration.Internal.AbstractTopFormula
import PPAC.Migration.Internal.SyntaxTopFormulaTyping

/-! 实际首槽公式抽象与原mode1零深度运行等价；两张实际码表在对象EX中取得并消去。 -/
namespace PPAC.Migration.Internal.AbstractTopFormulaOperation
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTopFormulaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxTypeLocalTransfer (iff_trans)

theorem at_codes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a B)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (abstracted w a b A B n q)) := by
  have hrun := AbstractTopFormula.run_iff_execution hZ w n mode z P a b A B R S q hw hm hd hz he hn
  have hjudgment := FormulaTransformRecursionCorrectness.execution_iff hZ w R S a B A b n q hw
  have hcodes := SyntaxTopFormulaCodes.abstract_at_codes hZ w a b A B n q R S hw he
  exact iff_trans (iff_trans hrun hjudgment) (.conjI (.conjR hcodes) (.conjL hcodes))

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a B)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (abstracted w a b A B n q)) := by
  let D := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 D _ (SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B hw hi)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ D
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw D)
  have hm2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hm D)
  have hd2 : Derives Δ (OriginalTermTraceSyntax.metadata w.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OriginalTermTraceSyntax.metadata_rename]) (SyntaxRenameBinders.under_2 hd D)
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 hz D)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (SyntaxRenameBinders.under_2 hn D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := at_codes_iff hZ2 w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc
    a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc q.castSucc.castSucc hw2 hm2 hd2 hz2 hD hn2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, abstracted_rename]) ho

theorem source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (abstracted w a b A B n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n a B) :=
  SyntaxTopFormulaTyping.abstract_source_type hZ w a b A B n q hw hq

theorem guarded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P a b A B n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 1 mode))
    (hd : Derives Γ (OriginalTermTraceSyntax.metadata w z P)) (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopEnvironmentSyntax.abstractInput w a b A B)) :
    Derives Γ (((FormulaCodeSyntax.formulaCode w n a B).conj (OriginalTransformRowSyntax.run 3 w mode z P n q)).iff (abstracted w a b A B n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := (FormulaCodeSyntax.formulaCode w n a B).conj (OriginalTransformRowSyntax.run 3 w mode z P n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have he := run_iff (ZFContext.add hZ E) w mode z P a b A B n q (add hw E) (add hm E) (add hd E) (add hz E) (add hi E) (.conjL hE)
    exact .impE (.conjL he) (.conjR hE)
  · apply Derives.impI
    let E := abstracted w a b A B n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have ht := source_type (ZFContext.add hZ E) w a b A B n q (add hw E) hE
    have he := run_iff (ZFContext.add hZ E) w mode z P a b A B n q (add hw E) (add hm E) (add hd E) (add hz E) (add hi E) ht
    exact .conjI ht (.impE (.conjR he) hE)

end PPAC.Migration.Internal.AbstractTopFormulaOperation
