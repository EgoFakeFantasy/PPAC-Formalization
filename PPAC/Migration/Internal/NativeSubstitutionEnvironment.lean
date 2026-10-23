import PPAC.Migration.Internal.NativeSubstitutionSyntax

/-! 原生替换实际环境及量词提升在原ZF核内成立；严格列表等式只用于连接这些对象证书。 -/
namespace PPAC.Migration.Internal.NativeSubstitutionEnvironment
open Source SourceAlgebra SourceLogic OmegaSyntax NativeSubstitutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (σ : Mapping sb tb tf) (τ : Mapping sf tb tf) (w a b c d : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral sb.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral sf.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral tb.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral tf.length d)) :
    Derives Γ (existsEnvironment σ τ w a b c d) :=
  TermQuotationEnvironment.exists_environment hZ _ _ w a b c d hw
    (of_eq (by simp only [NativeSubstitutionImages.images_length]) ha)
    (of_eq (by simp only [NativeSubstitutionImages.images_length]) hb) hc hd

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (σ : Mapping sb tb tf) (τ : Mapping sf tb tf) (w a b c d : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral sb.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral sf.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral tb.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral tf.length d)) :
    Derives Γ (fiber σ τ w a b c d) :=
  TermQuotationEnvironment.actual_fiber hZ _ _ w a b c d hw
    (of_eq (by simp only [NativeSubstitutionImages.images_length]) ha)
    (of_eq (by simp only [NativeSubstitutionImages.images_length]) hb) hc hd

theorem at_lifted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (σ : Mapping sb tb tf) (τ : Mapping sf tb tf) (w R S a b c d A C K H : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral sb.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral sf.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral tb.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral tf.length d))
    (he : Derives Γ (environment σ τ w a b c d R S))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H)) :
    Derives Γ (environment (YesMetaZFC.Logic.FirstOrder.VariableSubstitution.liftBound YesMetaZFC.SetTheory.SetSort.set σ)
      (YesMetaZFC.Logic.FirstOrder.VariableSubstitution.weakenBound YesMetaZFC.SetTheory.SetSort.set τ) w A b C d K H) := by
  have ho := TermQuotationLiftEnvironment.at_lifted hZ (NativeSubstitutionImages.images sb σ) (NativeSubstitutionImages.images sf τ)
    w R S a b c d A C K H hw (of_eq (by simp only [NativeSubstitutionImages.images_length]) ha)
      (of_eq (by simp only [NativeSubstitutionImages.images_length]) hb) hc hd he hl
  exact of_eq (environment_lift σ τ w A b C d K H).symm ho

end PPAC.Migration.Internal.NativeSubstitutionEnvironment
