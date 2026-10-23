import PPAC.Migration.Internal.NativeTopQuotationCorrespondence

/-! 原首槽数值判断与固定原SyntaxSubstitution树操作的quotation对应；仍为外部有限有效语法模式。 -/
namespace PPAC.Migration.Internal.NativeTopQuotationOriginal
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem instantiate_original_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (ht : Derives Γ (PureQuotationSyntax.term replacement w t))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n))
    (hA : Derives Γ (successor A a)) :
    Derives Γ ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (OriginalTreeQuotationSyntax.tree (PureSyntaxOperations.instantiateTree (PureSyntaxQuotation.termTree replacement) (PureSyntaxQuotation.formulaTree input)) w q)) := by
  have ho := NativeTopQuotationCorrespondence.instantiate_iff hZ input replacement w a b A t n q hw ha hb ht hn hA
  exact of_eq (congrArg (fun tree => (SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (OriginalTreeQuotationSyntax.tree tree w q)) (PureSyntaxOperations.instantiate_encoding input replacement).symm) ho

theorem abstract_original_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n))
    (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B b)) :
    Derives Γ ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxSubstitution.abstractTop (PureSyntaxQuotation.formulaTree input)) w q)) := by
  have ho := NativeTopQuotationCorrespondence.abstract_iff hZ input w a b A B n q hw ha hb hn hA hB
  exact of_eq (congrArg (fun tree => (SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (OriginalTreeQuotationSyntax.tree tree w q)) (PureSyntaxOperations.abstract_encoding input).symm) ho

end PPAC.Migration.Internal.NativeTopQuotationOriginal
