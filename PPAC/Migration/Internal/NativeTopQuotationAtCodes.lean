import PPAC.Migration.Internal.NativeTopQuotationEnvironment

/-! 实际原首槽码表下，原首槽公式判断精确计算原生instantiateTop/abstractFreeTop quotation。 -/
namespace PPAC.Migration.Internal.NativeTopQuotationAtCodes
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem instantiate_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n q R S : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (ht : Derives Γ (PureQuotationSyntax.term replacement w t)) (hn : Derives Γ (PureQuotationSyntax.formula input w n)) :
    Derives Γ ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (PureQuotationSyntax.formula (input.instantiateTop replacement) w q)) := by
  have hInput := SyntaxTopCodedEnvironmentTyping.instantiate_input w a b A t R S he
  have hA := SyntaxNumeralSyntax.intro_succ bound.length A a ha (.conjR hInput)
  have hEnv := NativeTopQuotationEnvironment.instantiate_environment hZ replacement w a b A t R S hw ha hb he ht
  have hFull := NativeFormulaQuotationCorrespondence.formula_iff hZ input (NativeTopQuotationIndices.instantiateBound replacement)
    (@NativeTopQuotationIndices.identityFree bound free) w R S A b a b n q hw hA hb ha hb hEnv hn
  have hTop := SyntaxTopFormulaCodes.instantiate_at_codes hZ w a b A t n q R S hw he
  have ho := SyntaxTypeLocalTransfer.iff_trans hTop hFull
  exact of_eq (by simp only [NativeTopQuotationIndices.instantiate_formula]) ho

theorem abstract_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n q R S : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n)) :
    Derives Γ ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (PureQuotationSyntax.formula input.abstractFreeTop w q)) := by
  have hInput := SyntaxTopCodedEnvironmentTyping.abstract_input w a b A B R S he
  have hA := SyntaxNumeralSyntax.intro_succ bound.length A a ha (.conjL (.conjR hInput))
  have hB := SyntaxNumeralSyntax.intro_succ free.length B b hb (.conjR (.conjR hInput))
  have hEnv := NativeTopQuotationEnvironment.abstract_environment hZ (bound := bound) (free := free) w a b A B R S hw ha hb he
  have hFull := NativeFormulaQuotationCorrespondence.formula_iff hZ input (@NativeTopQuotationIndices.abstractBound bound free)
    (@NativeTopQuotationIndices.abstractFree bound free) w R S a B A b n q hw ha hB hA hb hEnv hn
  have hTop := SyntaxTopFormulaCodes.abstract_at_codes hZ w a b A B n q R S hw he
  have ho := SyntaxTypeLocalTransfer.iff_trans hTop hFull
  exact of_eq (by simp only [NativeTopQuotationIndices.abstract_formula]) ho

end PPAC.Migration.Internal.NativeTopQuotationAtCodes
