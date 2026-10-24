import PPAC.Migration.Internal.InstantiateTopFormula
import PPAC.Migration.Internal.SyntaxTopFormulaTyping

/-! 原mode2全公式运行对应既有实际InstantiateTop判断；两实际码表在对象EX内构造和消去。 -/
namespace PPAC.Migration.Internal.InstantiateTopFormulaOperation
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTopFormulaSyntax
open SyntaxRenameQuerySyntax (of_eq)
open SyntaxTypeLocalTransfer (iff_trans)

theorem at_codes_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P b A R S n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n A b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (instantiated w z b A P n q)) := by
  have hrun := InstantiateTopFormula.run_iff_execution hZ w n mode z P b A R S q hw hm hz he hn
  have hjudgment := FormulaTransformRecursionCorrectness.execution_iff hZ w R S A b z b n q hw
  have hcodes := SyntaxTopFormulaCodes.instantiate_at_codes hZ w z b A P n q R S hw he
  exact iff_trans (iff_trans hrun hjudgment) (.conjI (.conjR hcodes) (.conjL hcodes))

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P b A n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopEnvironmentSyntax.instantiateInput w z b A P))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n A b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (instantiated w z b A P n q)) := by
  let D := SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc z.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc P.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 D _ (SyntaxTopCodedEnvironmentExistence.instantiate_exists hZ w z b A P hw hi)
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ D
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw D)
  have hm2 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hm D)
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (SyntaxRenameBinders.under_2 hz D)
  have hn2 : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc n.castSucc.castSucc A.castSucc.castSucc b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (SyntaxRenameBinders.under_2 hn D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have ho := at_codes_iff hZ2 w.castSucc.castSucc mode.castSucc.castSucc z.castSucc.castSucc P.castSucc.castSucc
    b.castSucc.castSucc A.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc q.castSucc.castSucc hw2 hm2 hz2 hD hn2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, instantiated_rename]) ho

theorem source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z P b A n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (instantiated w z b A P n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n A b) :=
  SyntaxTopFormulaTyping.instantiate_source_type hZ w z b A P n q hw hq

theorem guarded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w mode z P b A n q : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 2 mode))
    (hz : Derives Γ (empty z))
    (hi : Derives Γ (SyntaxTopEnvironmentSyntax.instantiateInput w z b A P)) :
    Derives Γ (((FormulaCodeSyntax.formulaCode w n A b).conj (OriginalTransformRowSyntax.run 3 w mode z P n q)).iff (instantiated w z b A P n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := (FormulaCodeSyntax.formulaCode w n A b).conj (OriginalTransformRowSyntax.run 3 w mode z P n q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have he := run_iff (ZFContext.add hZ E) w mode z P b A n q (add hw E) (add hm E) (add hz E) (add hi E) (.conjL hE)
    exact .impE (.conjL he) (.conjR hE)
  · apply Derives.impI
    let E := instantiated w z b A P n q
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have ht := source_type (ZFContext.add hZ E) w z P b A n q (add hw E) hE
    have he := run_iff (ZFContext.add hZ E) w mode z P b A n q (add hw E) (add hm E) (add hz E) (add hi E) ht
    exact .conjI ht (.impE (.conjR he) hE)

end PPAC.Migration.Internal.InstantiateTopFormulaOperation
