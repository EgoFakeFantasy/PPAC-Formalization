import PPAC.Migration.Internal.NativeSubstitutionEnvironment

/-! 原生Term.substituteMapped的实际对象数值quotation对应；不以宿主树等式替代。 -/
namespace PPAC.Migration.Internal.NativeTermQuotationSubstitution
open Source SourceAlgebra SourceLogic OmegaSyntax NativeSubstitutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem term_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (σ : Mapping sb tb tf) (τ : Mapping sf tb tf) {sort : YesMetaZFC.SetTheory.SetSort}
    (input : PureSyntaxQuotation.Tm sb sf sort) (w R S a b c d n q : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral sb.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral sf.length b))
    (he : Derives Γ (environment σ τ w a b c d R S)) (hn : Derives Γ (PureQuotationSyntax.term input w n)) :
    Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff
      (PureQuotationSyntax.term (input.substituteMapped σ τ) w q)) := by
  cases sort
  have haImages : Derives Γ (SyntaxNumeralSyntax.numeral (NativeSubstitutionImages.images sb σ).length a) := of_eq (by simp only [NativeSubstitutionImages.images_length]) ha
  have hbImages : Derives Γ (SyntaxNumeralSyntax.numeral (NativeSubstitutionImages.images sf τ).length b) := of_eq (by simp only [NativeSubstitutionImages.images_length]) hb
  exact match input with
  | .bvar entry => by
    have ho := TermQuotationSubstitution.term_iff hZ true (NativeSubstitutionImages.images sb σ) (NativeSubstitutionImages.images sf τ)
      (NativeSubstitutionImages.entryIndex σ entry) w a b c d R S n q hw haImages hbImages he hn
    change Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff
      (PureQuotationSyntax.term ((NativeSubstitutionImages.images sb σ).get (NativeSubstitutionImages.entryIndex σ entry)) w q)) at ho
    rw [NativeSubstitutionImages.get_image] at ho
    exact ho
  | .fvar entry => by
    have ho := TermQuotationSubstitution.term_iff hZ false (NativeSubstitutionImages.images sb σ) (NativeSubstitutionImages.images sf τ)
      (NativeSubstitutionImages.entryIndex τ entry) w a b c d R S n q hw haImages hbImages he hn
    change Derives Γ ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff
      (PureQuotationSyntax.term ((NativeSubstitutionImages.images sf τ).get (NativeSubstitutionImages.entryIndex τ entry)) w q)) at ho
    rw [NativeSubstitutionImages.get_image] at ho
    exact ho
  | .app symbol _ => nomatch symbol

end PPAC.Migration.Internal.NativeTermQuotationSubstitution
