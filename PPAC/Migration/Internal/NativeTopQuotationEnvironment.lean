import PPAC.Migration.Internal.TopQuotationReadings

/-! 原首槽实际码表就是具体原生替换的完整quotation环境；由原长度/字段单射性恢复整表。 -/
namespace PPAC.Migration.Internal.NativeTopQuotationEnvironment
open Source SourceAlgebra SourceLogic OmegaSyntax NativeSubstitutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem instantiate_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S))
    (ht : Derives Γ (PureQuotationSyntax.term replacement w t)) :
    Derives Γ (environment (NativeTopQuotationIndices.instantiateBound replacement) (@NativeTopQuotationIndices.identityFree bound free) w A b a b R S) := by
  have hInput := SyntaxTopCodedEnvironmentTyping.instantiate_input w a b A t R S he
  have hA : Derives Γ (SyntaxNumeralSyntax.numeral (NativeSubstitutionImages.images (YesMetaZFC.SetTheory.SetSort.set :: bound) (NativeTopQuotationIndices.instantiateBound replacement)).length A) :=
    of_eq (by simp only [NativeSubstitutionImages.images_length] <;> rfl) (SyntaxNumeralSyntax.intro_succ bound.length A a ha (.conjR hInput))
  have hB : Derives Γ (SyntaxNumeralSyntax.numeral (NativeSubstitutionImages.images free (@NativeTopQuotationIndices.identityFree bound free)).length b) := of_eq (by simp only [NativeSubstitutionImages.images_length]) hb
  have hLists := SyntaxTopCodedEnvironmentTyping.instantiate_lists w a b A t R S he
  have hRLen : Derives Γ (StructuralListLengthSyntax.hasLength w R A) := .conjR (.conjL (.conjR (.conjR (.conjL hLists))))
  have hSLen : Derives Γ (StructuralListLengthSyntax.hasLength w S b) := .conjR (.conjL (.conjR (.conjR (.conjR hLists))))
  have hRR := TopQuotationReadings.instantiate_bound_readings hZ replacement w a b A t R S hw ha he ht
  have hSR := TopQuotationReadings.instantiate_free_readings hZ (bound := bound) (free := free) w a b A t R S hw hb he
  have hRQ := TermImageReading.images_of_readings hZ _ w A R hw hA hRLen hRR
  have hSQ := TermImageReading.images_of_readings hZ _ w b S hw hB hSLen hSR
  exact .conjI (.conjI hRQ hSQ) hLists

theorem abstract_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (w a b A B R S : Fin m) (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a)) (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S)) :
    Derives Γ (environment (@NativeTopQuotationIndices.abstractBound bound free) (@NativeTopQuotationIndices.abstractFree bound free) w a B A b R S) := by
  have hInput := SyntaxTopCodedEnvironmentTyping.abstract_input w a b A B R S he
  have hA : Derives Γ (SyntaxNumeralSyntax.numeral (NativeSubstitutionImages.images bound (@NativeTopQuotationIndices.abstractBound bound free)).length a) := of_eq (by simp only [NativeSubstitutionImages.images_length]) ha
  have hB : Derives Γ (SyntaxNumeralSyntax.numeral (NativeSubstitutionImages.images (YesMetaZFC.SetTheory.SetSort.set :: free) (@NativeTopQuotationIndices.abstractFree bound free)).length B) :=
    of_eq (by simp only [NativeSubstitutionImages.images_length] <;> rfl) (SyntaxNumeralSyntax.intro_succ free.length B b hb (.conjR (.conjR hInput)))
  have hLists := SyntaxTopCodedEnvironmentTyping.abstract_lists w a b A B R S he
  have hRLen : Derives Γ (StructuralListLengthSyntax.hasLength w R a) := .conjR (.conjL (.conjR (.conjR (.conjL hLists))))
  have hSLen : Derives Γ (StructuralListLengthSyntax.hasLength w S B) := .conjR (.conjL (.conjR (.conjR (.conjR hLists))))
  have hRR := TopQuotationReadings.abstract_bound_readings hZ (bound := bound) (free := free) w a b A B R S hw ha he
  have hSR := TopQuotationReadings.abstract_free_readings hZ (bound := bound) (free := free) w a b A B R S hw hb he
  have hRQ := TermImageReading.images_of_readings hZ _ w a R hw hA hRLen hRR
  have hSQ := TermImageReading.images_of_readings hZ _ w B S hw hB hSLen hSR
  exact .conjI (.conjI hRQ hSQ) hLists

end PPAC.Migration.Internal.NativeTopQuotationEnvironment
