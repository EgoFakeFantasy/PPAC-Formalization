import PPAC.Migration.Internal.NativeTopQuotationValue

/-! 原首槽实例化/抽象的实际码表、原操作quotation及带类型联合唯一纤维的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectNativeTopQuotation
open Source SourceAlgebra SourceLogic OmegaSyntax

def instantiateBoundFieldSentence {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: bound) YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((PureQuotationSyntax.term replacement w t).imp ((SyntaxNumeralSyntax.numeral entry.index i).imp ((((Formula.mem i A).conj (StructuralListFieldSyntax.field w R i q)).iff (PureQuotationSyntax.term ((NativeTopQuotationIndices.instantiateBound replacement) entry) w q)))))))).close

theorem source_instantiateBoundField {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: bound) YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateBoundFieldSentence (bound := bound) (free := free) replacement entry w a b A t R S i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral entry.index i) (Context.add (PureQuotationSyntax.term replacement w t) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PureQuotationSyntax.term replacement w t) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral entry.index i) := .hyp (Or.inl rfl)
  exact TopQuotationVariableFields.instantiate_bound hZ (bound := bound) (free := free) replacement entry w a b A t R S i q h0 h1 h2 h3 h4

theorem instantiateBoundField_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: bound) YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateBoundFieldSentence (bound := bound) (free := free) replacement entry w a b A t R S i q)) := TheoryTransport.sentence (source_instantiateBoundField (bound := bound) (free := free) replacement entry w a b A t R S i q)

theorem native_instantiateBoundField {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: bound) YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateBoundFieldSentence (bound := bound) (free := free) replacement entry w a b A t R S i q)) := ZFReplay.replay (instantiateBoundField_kernel_certificate (bound := bound) (free := free) replacement entry w a b A t R S i q)

def instantiateBoundReadingsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((PureQuotationSyntax.term replacement w t).imp ((TermImageReadingSyntax.readings (NativeSubstitutionImages.images (YesMetaZFC.SetTheory.SetSort.set :: bound) (NativeTopQuotationIndices.instantiateBound replacement)) w R)))))).close

theorem source_instantiateBoundReadings {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateBoundReadingsSentence (bound := bound) (free := free) replacement w a b A t R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.term replacement w t) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PureQuotationSyntax.term replacement w t) := .hyp (Or.inl rfl)
  exact TopQuotationReadings.instantiate_bound_readings hZ (bound := bound) (free := free) replacement w a b A t R S h0 h1 h2 h3

theorem instantiateBoundReadings_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateBoundReadingsSentence (bound := bound) (free := free) replacement w a b A t R S)) := TheoryTransport.sentence (source_instantiateBoundReadings (bound := bound) (free := free) replacement w a b A t R S)

theorem native_instantiateBoundReadings {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateBoundReadingsSentence (bound := bound) (free := free) replacement w a b A t R S)) := ZFReplay.replay (instantiateBoundReadings_kernel_certificate (bound := bound) (free := free) replacement w a b A t R S)

def instantiateFreeFieldSentence {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable free YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((SyntaxNumeralSyntax.numeral entry.index i).imp ((((Formula.mem i b).conj (StructuralListFieldSyntax.field w S i q)).iff (PureQuotationSyntax.term ((@NativeTopQuotationIndices.identityFree bound free) entry) w q))))))).close

theorem source_instantiateFreeField {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable free YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateFreeFieldSentence (bound := bound) (free := free) entry w a b A t R S i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral entry.index i) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral entry.index i) := .hyp (Or.inl rfl)
  exact TopQuotationVariableFields.instantiate_free hZ (bound := bound) (free := free) entry w a b A t R S i q h0 h1 h2 h3

theorem instantiateFreeField_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable free YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateFreeFieldSentence (bound := bound) (free := free) entry w a b A t R S i q)) := TheoryTransport.sentence (source_instantiateFreeField (bound := bound) (free := free) entry w a b A t R S i q)

theorem native_instantiateFreeField {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable free YesMetaZFC.SetTheory.SetSort.set) (w a b A t R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateFreeFieldSentence (bound := bound) (free := free) entry w a b A t R S i q)) := ZFReplay.replay (instantiateFreeField_kernel_certificate (bound := bound) (free := free) entry w a b A t R S i q)

def instantiateFreeReadingsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A t R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((TermImageReadingSyntax.readings (NativeSubstitutionImages.images free (@NativeTopQuotationIndices.identityFree bound free)) w S))))).close

theorem source_instantiateFreeReadings {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A t R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateFreeReadingsSentence (bound := bound) (free := free)  w a b A t R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inl rfl)
  exact TopQuotationReadings.instantiate_free_readings hZ (bound := bound) (free := free) w a b A t R S h0 h1 h2

theorem instantiateFreeReadings_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateFreeReadingsSentence (bound := bound) (free := free)  w a b A t R S)) := TheoryTransport.sentence (source_instantiateFreeReadings (bound := bound) (free := free)  w a b A t R S)

theorem native_instantiateFreeReadings {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateFreeReadingsSentence (bound := bound) (free := free)  w a b A t R S)) := ZFReplay.replay (instantiateFreeReadings_kernel_certificate (bound := bound) (free := free)  w a b A t R S)

def abstractBoundFieldSentence {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable bound YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxNumeralSyntax.numeral entry.index i).imp ((((Formula.mem i a).conj (StructuralListFieldSyntax.field w R i q)).iff (PureQuotationSyntax.term ((@NativeTopQuotationIndices.abstractBound bound free) entry) w q))))))).close

theorem source_abstractBoundField {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable bound YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractBoundFieldSentence (bound := bound) (free := free) entry w a b A B R S i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral entry.index i) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral entry.index i) := .hyp (Or.inl rfl)
  exact TopQuotationVariableFields.abstract_bound hZ (bound := bound) (free := free) entry w a b A B R S i q h0 h1 h2 h3

theorem abstractBoundField_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable bound YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractBoundFieldSentence (bound := bound) (free := free) entry w a b A B R S i q)) := TheoryTransport.sentence (source_abstractBoundField (bound := bound) (free := free) entry w a b A B R S i q)

theorem native_abstractBoundField {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable bound YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractBoundFieldSentence (bound := bound) (free := free) entry w a b A B R S i q)) := ZFReplay.replay (abstractBoundField_kernel_certificate (bound := bound) (free := free) entry w a b A B R S i q)

def abstractBoundReadingsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((TermImageReadingSyntax.readings (NativeSubstitutionImages.images bound (@NativeTopQuotationIndices.abstractBound bound free)) w R))))).close

theorem source_abstractBoundReadings {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractBoundReadingsSentence (bound := bound) (free := free)  w a b A B R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact TopQuotationReadings.abstract_bound_readings hZ (bound := bound) (free := free) w a b A B R S h0 h1 h2

theorem abstractBoundReadings_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractBoundReadingsSentence (bound := bound) (free := free)  w a b A B R S)) := TheoryTransport.sentence (source_abstractBoundReadings (bound := bound) (free := free)  w a b A B R S)

theorem native_abstractBoundReadings {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractBoundReadingsSentence (bound := bound) (free := free)  w a b A B R S)) := ZFReplay.replay (abstractBoundReadings_kernel_certificate (bound := bound) (free := free)  w a b A B R S)

def abstractFreeFieldSentence {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: free) YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((SyntaxNumeralSyntax.numeral entry.index i).imp ((((Formula.mem i B).conj (StructuralListFieldSyntax.field w S i q)).iff (PureQuotationSyntax.term ((@NativeTopQuotationIndices.abstractFree bound free) entry) w q))))))).close

theorem source_abstractFreeField {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: free) YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractFreeFieldSentence (bound := bound) (free := free) entry w a b A B R S i q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral entry.index i) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral entry.index i) := .hyp (Or.inl rfl)
  exact TopQuotationVariableFields.abstract_free hZ (bound := bound) (free := free) entry w a b A B R S i q h0 h1 h2 h3

theorem abstractFreeField_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: free) YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractFreeFieldSentence (bound := bound) (free := free) entry w a b A B R S i q)) := TheoryTransport.sentence (source_abstractFreeField (bound := bound) (free := free) entry w a b A B R S i q)

theorem native_abstractFreeField {m} {bound free : PureSyntaxQuotation.Ctx} (entry : YesMetaZFC.Logic.FirstOrder.Variable (YesMetaZFC.SetTheory.SetSort.set :: free) YesMetaZFC.SetTheory.SetSort.set) (w a b A B R S i q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractFreeFieldSentence (bound := bound) (free := free) entry w a b A B R S i q)) := ZFReplay.replay (abstractFreeField_kernel_certificate (bound := bound) (free := free) entry w a b A B R S i q)

def abstractFreeReadingsSentence {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((TermImageReadingSyntax.readings (NativeSubstitutionImages.images (YesMetaZFC.SetTheory.SetSort.set :: free) (@NativeTopQuotationIndices.abstractFree bound free)) w S))))).close

theorem source_abstractFreeReadings {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractFreeReadingsSentence (bound := bound) (free := free)  w a b A B R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact TopQuotationReadings.abstract_free_readings hZ (bound := bound) (free := free) w a b A B R S h0 h1 h2

theorem abstractFreeReadings_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractFreeReadingsSentence (bound := bound) (free := free)  w a b A B R S)) := TheoryTransport.sentence (source_abstractFreeReadings (bound := bound) (free := free)  w a b A B R S)

theorem native_abstractFreeReadings {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractFreeReadingsSentence (bound := bound) (free := free)  w a b A B R S)) := ZFReplay.replay (abstractFreeReadings_kernel_certificate (bound := bound) (free := free)  w a b A B R S)

def instantiateEnvironmentSentence {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((PureQuotationSyntax.term replacement w t).imp ((NativeSubstitutionSyntax.environment (NativeTopQuotationIndices.instantiateBound replacement) (@NativeTopQuotationIndices.identityFree bound free) w A b a b R S))))))).close

theorem source_instantiateEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateEnvironmentSentence (bound := bound) (free := free) replacement w a b A t R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.term replacement w t) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PureQuotationSyntax.term replacement w t) := .hyp (Or.inl rfl)
  exact NativeTopQuotationEnvironment.instantiate_environment hZ replacement w a b A t R S h0 h1 h2 h3 h4

theorem instantiateEnvironment_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateEnvironmentSentence (bound := bound) (free := free) replacement w a b A t R S)) := TheoryTransport.sentence (source_instantiateEnvironment (bound := bound) (free := free) replacement w a b A t R S)

theorem native_instantiateEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateEnvironmentSentence (bound := bound) (free := free) replacement w a b A t R S)) := ZFReplay.replay (instantiateEnvironment_kernel_certificate (bound := bound) (free := free) replacement w a b A t R S)

def abstractEnvironmentSentence {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((NativeSubstitutionSyntax.environment (@NativeTopQuotationIndices.abstractBound bound free) (@NativeTopQuotationIndices.abstractFree bound free) w a B A b R S)))))).close

theorem source_abstractEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractEnvironmentSentence (bound := bound) (free := free)  w a b A B R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact NativeTopQuotationEnvironment.abstract_environment hZ (bound := bound) (free := free) w a b A B R S h0 h1 h2 h3

theorem abstractEnvironment_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractEnvironmentSentence (bound := bound) (free := free)  w a b A B R S)) := TheoryTransport.sentence (source_abstractEnvironment (bound := bound) (free := free)  w a b A B R S)

theorem native_abstractEnvironment {m} {bound free : PureSyntaxQuotation.Ctx} (w a b A B R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractEnvironmentSentence (bound := bound) (free := free)  w a b A B R S)) := ZFReplay.replay (abstractEnvironment_kernel_certificate (bound := bound) (free := free)  w a b A B R S)

def instantiateAtCodesSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp ((PureQuotationSyntax.term replacement w t).imp ((PureQuotationSyntax.formula input w n).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (PureQuotationSyntax.formula (input.instantiateTop replacement) w q))))))))).close

theorem source_instantiateAtCodes {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateAtCodesSentence (bound := bound) (free := free) input replacement w a b A t n q R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula input w n) (Context.add (PureQuotationSyntax.term replacement w t) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PureQuotationSyntax.term replacement w t) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inl rfl)
  exact NativeTopQuotationAtCodes.instantiate_at_codes hZ input replacement w a b A t n q R S h0 h1 h2 h3 h4 h5

theorem instantiateAtCodes_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateAtCodesSentence (bound := bound) (free := free) input replacement w a b A t n q R S)) := TheoryTransport.sentence (source_instantiateAtCodes (bound := bound) (free := free) input replacement w a b A t n q R S)

theorem native_instantiateAtCodes {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateAtCodesSentence (bound := bound) (free := free) input replacement w a b A t n q R S)) := ZFReplay.replay (instantiateAtCodes_kernel_certificate (bound := bound) (free := free) input replacement w a b A t n q R S)

def instantiateIffSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((PureQuotationSyntax.term replacement w t).imp ((PureQuotationSyntax.formula input w n).imp ((successor A a).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (PureQuotationSyntax.formula (input.instantiateTop replacement) w q))))))))).close

theorem source_instantiateIff {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateIffSentence (bound := bound) (free := free) input replacement w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor A a) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (PureQuotationSyntax.term replacement w t) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureQuotationSyntax.term replacement w t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor A a) := .hyp (Or.inl rfl)
  exact NativeTopQuotationCorrespondence.instantiate_iff hZ input replacement w a b A t n q h0 h1 h2 h3 h4 h5

theorem instantiateIff_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateIffSentence (bound := bound) (free := free) input replacement w a b A t n q)) := TheoryTransport.sentence (source_instantiateIff (bound := bound) (free := free) input replacement w a b A t n q)

theorem native_instantiateIff {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateIffSentence (bound := bound) (free := free) input replacement w a b A t n q)) := ZFReplay.replay (instantiateIff_kernel_certificate (bound := bound) (free := free) input replacement w a b A t n q)

def instantiateOriginalIffSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((PureQuotationSyntax.term replacement w t).imp ((PureQuotationSyntax.formula input w n).imp ((successor A a).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (OriginalTreeQuotationSyntax.tree (PureSyntaxOperations.instantiateTree (PureSyntaxQuotation.termTree replacement) (PureSyntaxQuotation.formulaTree input)) w q))))))))).close

theorem source_instantiateOriginalIff {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateOriginalIffSentence (bound := bound) (free := free) input replacement w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor A a) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (PureQuotationSyntax.term replacement w t) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureQuotationSyntax.term replacement w t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor A a) := .hyp (Or.inl rfl)
  exact NativeTopQuotationOriginal.instantiate_original_iff hZ input replacement w a b A t n q h0 h1 h2 h3 h4 h5

theorem instantiateOriginalIff_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateOriginalIffSentence (bound := bound) (free := free) input replacement w a b A t n q)) := TheoryTransport.sentence (source_instantiateOriginalIff (bound := bound) (free := free) input replacement w a b A t n q)

theorem native_instantiateOriginalIff {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateOriginalIffSentence (bound := bound) (free := free) input replacement w a b A t n q)) := ZFReplay.replay (instantiateOriginalIff_kernel_certificate (bound := bound) (free := free) input replacement w a b A t n q)

def instantiateAtCandidateSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((PureQuotationSyntax.term replacement w t).imp ((PureQuotationSyntax.formula input w n).imp ((successor A a).imp ((PureQuotationSyntax.formula (input.instantiateTop replacement) w q).imp ((NativeTopQuotationValueSyntax.instantiateValue input replacement w a b A t n q))))))))).close

theorem source_instantiateAtCandidate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateAtCandidateSentence (bound := bound) (free := free) input replacement w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula (input.instantiateTop replacement) w q) (Context.add (successor A a) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (PureQuotationSyntax.term replacement w t) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (PureQuotationSyntax.term replacement w t) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PureQuotationSyntax.formula (input.instantiateTop replacement) w q) := .hyp (Or.inl rfl)
  exact NativeTopQuotationValue.instantiate_at_candidate hZ input replacement w a b A t n q h0 h1 h2 h3 h4 h5 h6

theorem instantiateAtCandidate_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateAtCandidateSentence (bound := bound) (free := free) input replacement w a b A t n q)) := TheoryTransport.sentence (source_instantiateAtCandidate (bound := bound) (free := free) input replacement w a b A t n q)

theorem native_instantiateAtCandidate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateAtCandidateSentence (bound := bound) (free := free) input replacement w a b A t n q)) := ZFReplay.replay (instantiateAtCandidate_kernel_certificate (bound := bound) (free := free) input replacement w a b A t n q)

def instantiateFiberSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((PureQuotationSyntax.term replacement w t).imp ((PureQuotationSyntax.formula input w n).imp ((successor A a).imp ((NativeTopQuotationValueSyntax.instantiateFiber input replacement w a b A t n)))))))).close

theorem source_instantiateFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateFiberSentence (bound := bound) (free := free) input replacement w a b A t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor A a) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (PureQuotationSyntax.term replacement w t) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureQuotationSyntax.term replacement w t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor A a) := .hyp (Or.inl rfl)
  exact NativeTopQuotationValue.instantiate_actual_fiber hZ input replacement w a b A t n h0 h1 h2 h3 h4 h5

theorem instantiateFiber_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateFiberSentence (bound := bound) (free := free) input replacement w a b A t n)) := TheoryTransport.sentence (source_instantiateFiber (bound := bound) (free := free) input replacement w a b A t n)

theorem native_instantiateFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free) (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateFiberSentence (bound := bound) (free := free) input replacement w a b A t n)) := ZFReplay.replay (instantiateFiber_kernel_certificate (bound := bound) (free := free) input replacement w a b A t n)

def abstractAtCodesSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp ((PureQuotationSyntax.formula input w n).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (PureQuotationSyntax.formula (input.abstractFreeTop) w q)))))))).close

theorem source_abstractAtCodes {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractAtCodesSentence (bound := bound) (free := free) input w a b A B n q R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula input w n) (Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inl rfl)
  exact NativeTopQuotationAtCodes.abstract_at_codes hZ input w a b A B n q R S h0 h1 h2 h3 h4

theorem abstractAtCodes_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractAtCodesSentence (bound := bound) (free := free) input w a b A B n q R S)) := TheoryTransport.sentence (source_abstractAtCodes (bound := bound) (free := free) input w a b A B n q R S)

theorem native_abstractAtCodes {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractAtCodesSentence (bound := bound) (free := free) input w a b A B n q R S)) := ZFReplay.replay (abstractAtCodes_kernel_certificate (bound := bound) (free := free) input w a b A B n q R S)

def abstractIffSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((PureQuotationSyntax.formula input w n).imp ((successor A a).imp ((successor B b).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (PureQuotationSyntax.formula (input.abstractFreeTop) w q))))))))).close

theorem source_abstractIff {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractIffSentence (bound := bound) (free := free) input w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (successor A a) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact NativeTopQuotationCorrespondence.abstract_iff hZ input w a b A B n q h0 h1 h2 h3 h4 h5

theorem abstractIff_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractIffSentence (bound := bound) (free := free) input w a b A B n q)) := TheoryTransport.sentence (source_abstractIff (bound := bound) (free := free) input w a b A B n q)

theorem native_abstractIff {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractIffSentence (bound := bound) (free := free) input w a b A B n q)) := ZFReplay.replay (abstractIff_kernel_certificate (bound := bound) (free := free) input w a b A B n q)

def abstractOriginalIffSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((PureQuotationSyntax.formula input w n).imp ((successor A a).imp ((successor B b).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.SyntaxSubstitution.abstractTop (PureSyntaxQuotation.formulaTree input)) w q))))))))).close

theorem source_abstractOriginalIff {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractOriginalIffSentence (bound := bound) (free := free) input w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (successor A a) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact NativeTopQuotationOriginal.abstract_original_iff hZ input w a b A B n q h0 h1 h2 h3 h4 h5

theorem abstractOriginalIff_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractOriginalIffSentence (bound := bound) (free := free) input w a b A B n q)) := TheoryTransport.sentence (source_abstractOriginalIff (bound := bound) (free := free) input w a b A B n q)

theorem native_abstractOriginalIff {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractOriginalIffSentence (bound := bound) (free := free) input w a b A B n q)) := ZFReplay.replay (abstractOriginalIff_kernel_certificate (bound := bound) (free := free) input w a b A B n q)

def abstractAtCandidateSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((PureQuotationSyntax.formula input w n).imp ((successor A a).imp ((successor B b).imp ((PureQuotationSyntax.formula (input.abstractFreeTop) w q).imp ((NativeTopQuotationValueSyntax.abstractValue input w a b A B n q))))))))).close

theorem source_abstractAtCandidate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractAtCandidateSentence (bound := bound) (free := free) input w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula (input.abstractFreeTop) w q) (Context.add (successor B b) (Context.add (successor A a) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (successor B b) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PureQuotationSyntax.formula (input.abstractFreeTop) w q) := .hyp (Or.inl rfl)
  exact NativeTopQuotationValue.abstract_at_candidate hZ input w a b A B n q h0 h1 h2 h3 h4 h5 h6

theorem abstractAtCandidate_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractAtCandidateSentence (bound := bound) (free := free) input w a b A B n q)) := TheoryTransport.sentence (source_abstractAtCandidate (bound := bound) (free := free) input w a b A B n q)

theorem native_abstractAtCandidate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractAtCandidateSentence (bound := bound) (free := free) input w a b A B n q)) := ZFReplay.replay (abstractAtCandidate_kernel_certificate (bound := bound) (free := free) input w a b A B n q)

def abstractFiberSentence {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral bound.length a).imp ((SyntaxNumeralSyntax.numeral free.length b).imp ((PureQuotationSyntax.formula input w n).imp ((successor A a).imp ((successor B b).imp ((NativeTopQuotationValueSyntax.abstractFiber input w a b A B n)))))))).close

theorem source_abstractFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractFiberSentence (bound := bound) (free := free) input w a b A B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B b) (Context.add (successor A a) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (SyntaxNumeralSyntax.numeral free.length b) (Context.add (SyntaxNumeralSyntax.numeral bound.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor A a) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (successor B b) := .hyp (Or.inl rfl)
  exact NativeTopQuotationValue.abstract_actual_fiber hZ input w a b A B n h0 h1 h2 h3 h4 h5

theorem abstractFiber_kernel_certificate {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractFiberSentence (bound := bound) (free := free) input w a b A B n)) := TheoryTransport.sentence (source_abstractFiber (bound := bound) (free := free) input w a b A B n)

theorem native_abstractFiber {m} {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free)) (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractFiberSentence (bound := bound) (free := free) input w a b A B n)) := ZFReplay.replay (abstractFiber_kernel_certificate (bound := bound) (free := free) input w a b A B n)

end PPAC.Migration.Internal.ObjectNativeTopQuotation
