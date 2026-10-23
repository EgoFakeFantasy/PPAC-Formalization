import PPAC.Migration.Internal.StrictLookupValue

/-! 严格内部查表、精确成功/拒绝域及同一自由替换表binder稳定性的原核证书。 -/
namespace PPAC.Migration.Internal.ObjectStrictLookup
open Source SourceAlgebra SourceLogic OmegaSyntax

def binderFreeCodeStableSentence {m} (w I J R S a b c d A C M K H L : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R S a b c d).imp ((SyntaxFreeSubstSyntax.codeConversion w b d L J).imp ((SyntaxMapLiftSyntax.codedLift w a c I A C M).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((Formula.equal H L))))))).close

theorem source_binderFreeCodeStable {m} (w I J R S a b c d A C M K H L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderFreeCodeStableSentence w I J R S a b c d A C M K H L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (SyntaxMapLiftSyntax.codedLift w a c I A C M) (Context.add (SyntaxFreeSubstSyntax.codeConversion w b d L J) (Context.add (IndexTermImageCodeSyntax.environment w I J R S a b c d) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R S a b c d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w b d L J) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c I A C M) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inl rfl)
  exact FreeSubstProgramBinder.free_code_stable hZ w I J R S a b c d A C M K H L h0 h1 h2 h3 h4

theorem binderFreeCodeStable_kernel_certificate {m} (w I J R S a b c d A C M K H L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderFreeCodeStableSentence w I J R S a b c d A C M K H L)) := TheoryTransport.sentence (source_binderFreeCodeStable w I J R S a b c d A C M K H L)

theorem native_binderFreeCodeStable {m} (w I J R S a b c d A C M K H L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderFreeCodeStableSentence w I J R S a b c d A C M K H L)) := ZFReplay.replay (binderFreeCodeStable_kernel_certificate w I J R S a b c d A C M K H L)

def binderLiftedEnvironmentSentence {m} (w b a c L I J R u v M K H : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R L b a b c).imp ((SyntaxIdentityMapSyntax.identityCode w b I).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L J).imp ((SyntaxMapLiftSyntax.codedLift w b b I u v M).imp ((SyntaxCodedMixedBinderSyntax.lifted w R L b a b c u v K H).imp (((Formula.equal u v).conj ((SyntaxIdentityMapSyntax.identityCode w u M).conj ((Formula.equal H L).conj (IndexTermImageCodeSyntax.environment w M J K L u a u c))))))))))).close

theorem source_binderLiftedEnvironment {m} (w b a c L I J R u v M K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderLiftedEnvironmentSentence w b a c L I J R u v M K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R L b a b c u v K H) (Context.add (SyntaxMapLiftSyntax.codedLift w b b I u v M) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L J) (Context.add (SyntaxIdentityMapSyntax.identityCode w b I) (Context.add (IndexTermImageCodeSyntax.environment w I J R L b a b c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R L b a b c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L J) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMapLiftSyntax.codedLift w b b I u v M) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R L b a b c u v K H) := .hyp (Or.inl rfl)
  exact FreeSubstProgramBinder.lifted_environment hZ w b a c L I J R u v M K H h0 h1 h2 h3 h4 h5

theorem binderLiftedEnvironment_kernel_certificate {m} (w b a c L I J R u v M K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderLiftedEnvironmentSentence w b a c L I J R u v M K H)) := TheoryTransport.sentence (source_binderLiftedEnvironment w b a c L I J R u v M K H)

theorem native_binderLiftedEnvironment {m} (w b a c L I J R u v M K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderLiftedEnvironmentSentence w b a c L I J R u v M K H)) := ZFReplay.replay (binderLiftedEnvironment_kernel_certificate w b a c L I J R u v M K H)

def binderChildExecutionSentence {m} (w b a c L I J R u v M K H x q : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.environment w I J R L b a b c).imp ((SyntaxIdentityMapSyntax.identityCode w b I).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L J).imp ((SyntaxMapLiftSyntax.codedLift w b b I u v M).imp ((SyntaxCodedMixedBinderSyntax.lifted w R L b a b c u v K H).imp ((FormulaTransformExecutionSyntax.executed w K H u a v c x q).imp ((FreeSubstProgramSyntax.executed w u a c L x q))))))))).close

theorem source_binderChildExecution {m} (w b a c L I J R u v M K H x q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderChildExecutionSentence w b a c L I J R u v M K H x q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformExecutionSyntax.executed w K H u a v c x q) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R L b a b c u v K H) (Context.add (SyntaxMapLiftSyntax.codedLift w b b I u v M) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L J) (Context.add (SyntaxIdentityMapSyntax.identityCode w b I) (Context.add (IndexTermImageCodeSyntax.environment w I J R L b a b c) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (IndexTermImageCodeSyntax.environment w I J R L b a b c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L J) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxMapLiftSyntax.codedLift w b b I u v M) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R L b a b c u v K H) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (FormulaTransformExecutionSyntax.executed w K H u a v c x q) := .hyp (Or.inl rfl)
  exact FreeSubstProgramBinder.child_execution hZ w b a c L I J R u v M K H x q h0 h1 h2 h3 h4 h5 h6

theorem binderChildExecution_kernel_certificate {m} (w b a c L I J R u v M K H x q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderChildExecutionSentence w b a c L I J R u v M K H x q)) := TheoryTransport.sentence (source_binderChildExecution w b a c L I J R u v M K H x q)

theorem native_binderChildExecution {m} (w b a c L I J R u v M K H x q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderChildExecutionSentence w b a c L I J R u v M K H x q)) := ZFReplay.replay (binderChildExecution_kernel_certificate w b a c L I J R u v M K H x q)

def lookupZeroSelectedSentence {m} (w n z y : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((StrictLookupSyntax.returned w n z y).iff (StructuralListProjectionSyntax.selected true w n y))))).close

theorem source_lookupZeroSelected {m} (w n z y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupZeroSelectedSentence w n z y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact StrictLookupRules.zero_selected hZ w n z y h0 h1

theorem lookupZeroSelected_kernel_certificate {m} (w n z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupZeroSelectedSentence w n z y)) := TheoryTransport.sentence (source_lookupZeroSelected w n z y)

theorem native_lookupZeroSelected {m} (w n z y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupZeroSelectedSentence w n z y)) := ZFReplay.replay (lookupZeroSelected_kernel_certificate w n z y)

def lookupConsSuccessorSentence {m} (w h t n r s y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((Formula.mem r w).imp ((successor s r).imp ((StructuralListSyntax.consCode w h t n).imp (((StrictLookupSyntax.returned w n s y).iff (StrictLookupSyntax.returned w t r y))))))))).close

theorem source_lookupConsSuccessor {m} (w h t n r s y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupConsSuccessorSentence w h t n r s y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h t n) (Context.add (successor s r) (Context.add (Formula.mem r w) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (successor s r) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inl rfl)
  exact StrictLookupRules.successor_iff hZ w h t n r s y h0 h1 h2 h3 h4 h5

theorem lookupConsSuccessor_kernel_certificate {m} (w h t n r s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupConsSuccessorSentence w h t n r s y)) := TheoryTransport.sentence (source_lookupConsSuccessor w h t n r s y)

theorem native_lookupConsSuccessor {m} (w h t n r s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupConsSuccessorSentence w h t n r s y)) := ZFReplay.replay (lookupConsSuccessor_kernel_certificate w h t n r s y)

def lookupOuterRejectedSentence {m} (w n i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp (((StructuralListProjectionSyntax.hasCons true w n).neg).imp ((StrictLookupSyntax.rejected w n i))))).close

theorem source_lookupOuterRejected {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupOuterRejectedSentence w n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((StructuralListProjectionSyntax.hasCons true w n).neg) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((StructuralListProjectionSyntax.hasCons true w n).neg) := .hyp (Or.inl rfl)
  exact StrictLookupFailure.no_cons_rejected hZ w n i h0 h1 h2

theorem lookupOuterRejected_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupOuterRejectedSentence w n i)) := TheoryTransport.sentence (source_lookupOuterRejected w n i)

theorem native_lookupOuterRejected {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupOuterRejectedSentence w n i)) := ZFReplay.replay (lookupOuterRejected_kernel_certificate w n i)

def lookupNilRejectedSentence {m} (w n i : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((StructuralListSyntax.nilCode w n).imp ((StrictLookupSyntax.rejected w n i))))).close

theorem source_lookupNilRejected {m} (w n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupNilRejectedSentence w n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.nilCode w n) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w n) := .hyp (Or.inl rfl)
  exact StrictLookupFailure.nil_rejected hZ w n i h0 h1 h2

theorem lookupNilRejected_kernel_certificate {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupNilRejectedSentence w n i)) := TheoryTransport.sentence (source_lookupNilRejected w n i)

theorem native_lookupNilRejected {m} (w n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupNilRejectedSentence w n i)) := ZFReplay.replay (lookupNilRejected_kernel_certificate w n i)

def lookupConsZeroReturnsSentence {m} (w h t n z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem t w).imp ((StructuralListSyntax.consCode w h t n).imp ((empty z).imp ((StrictLookupSyntax.returned w n z h))))))).close

theorem source_lookupConsZeroReturns {m} (w h t n z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupConsZeroReturnsSentence w h t n z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (StructuralListSyntax.consCode w h t n) (Context.add (Formula.mem t w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h t n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact StrictLookupFailure.cons_zero_returns hZ w h t n z h0 h1 h2 h3 h4

theorem lookupConsZeroReturns_kernel_certificate {m} (w h t n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupConsZeroReturnsSentence w h t n z)) := TheoryTransport.sentence (source_lookupConsZeroReturns w h t n z)

theorem native_lookupConsZeroReturns {m} (w h t n z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupConsZeroReturnsSentence w h t n z)) := ZFReplay.replay (lookupConsZeroReturns_kernel_certificate w h t n z)

def lookupEmptySinkSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((empty n).imp ((StructuralListProjectionSyntax.iteration false w n i y).imp ((empty y)))))).close

theorem source_lookupEmptySink {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupEmptySinkSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListProjectionSyntax.iteration false w n i y) (Context.add (empty n) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListProjectionSyntax.iteration false w n i y) := .hyp (Or.inl rfl)
  exact StrictLookupSinkInduction.empty_iteration hZ w n i y h0 h1 h2 h3

theorem lookupEmptySink_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupEmptySinkSentence w n i y)) := TheoryTransport.sentence (source_lookupEmptySink w n i y)

theorem native_lookupEmptySink {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupEmptySinkSentence w n i y)) := ZFReplay.replay (lookupEmptySink_kernel_certificate w n i y)

def lookupExactDomainSentence {m} (w n r i y : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListLengthSyntax.hasLength w n r).imp ((Formula.mem i w).imp (((StrictLookupSyntax.returned w n i y).iff ((Formula.mem i r).conj (StructuralListFieldSyntax.field w n i y))))))).close

theorem source_lookupExactDomain {m} (w n r i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupExactDomainSentence w n r i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (StructuralListLengthSyntax.hasLength w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListLengthSyntax.hasLength w n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact StrictLookupDomainInduction.at_length hZ w n r i y h0 h1 h2

theorem lookupExactDomain_kernel_certificate {m} (w n r i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupExactDomainSentence w n r i y)) := TheoryTransport.sentence (source_lookupExactDomain w n r i y)

theorem native_lookupExactDomain {m} (w n r i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupExactDomainSentence w n r i y)) := ZFReplay.replay (lookupExactDomain_kernel_certificate w n r i y)

def lookupCheckedDomainSentence {m} (w n r i y : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListLengthSyntax.hasLength w n r).imp ((Formula.mem i w).imp (((StrictLookupSyntax.checked w n i y).iff ((Formula.mem i r).conj (StructuralListFieldSyntax.field w n i y))))))).close

theorem source_lookupCheckedDomain {m} (w n r i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupCheckedDomainSentence w n r i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (StructuralListLengthSyntax.hasLength w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListLengthSyntax.hasLength w n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact StrictLookupValue.checked_iff_domain hZ w n r i y h0 h1 h2

theorem lookupCheckedDomain_kernel_certificate {m} (w n r i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupCheckedDomainSentence w n r i y)) := TheoryTransport.sentence (source_lookupCheckedDomain w n r i y)

theorem native_lookupCheckedDomain {m} (w n r i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupCheckedDomainSentence w n r i y)) := ZFReplay.replay (lookupCheckedDomain_kernel_certificate w n r i y)

def lookupUniqueSentence {m} (w n i y z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((StrictLookupSyntax.returned w n i y).imp ((StrictLookupSyntax.returned w n i z).imp ((Formula.equal y z)))))).close

theorem source_lookupUnique {m} (w n i y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupUniqueSentence w n i y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StrictLookupSyntax.returned w n i z) (Context.add (StrictLookupSyntax.returned w n i y) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StrictLookupSyntax.returned w n i y) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StrictLookupSyntax.returned w n i z) := .hyp (Or.inl rfl)
  exact StrictLookupValue.unique hZ w n i y z h0 h1 h2 h3

theorem lookupUnique_kernel_certificate {m} (w n i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupUniqueSentence w n i y z)) := TheoryTransport.sentence (source_lookupUnique w n i y z)

theorem native_lookupUnique {m} (w n i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupUniqueSentence w n i y z)) := ZFReplay.replay (lookupUnique_kernel_certificate w n i y z)

def lookupUniqueOutputSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((StrictLookupSyntax.returned w n i y).imp ((StrictLookupValueSyntax.uniqueOutput w n i y))))).close

theorem source_lookupUniqueOutput {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupUniqueOutputSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StrictLookupSyntax.returned w n i y) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StrictLookupSyntax.returned w n i y) := .hyp (Or.inl rfl)
  exact StrictLookupValue.unique_output hZ w n i y h0 h1 h2

theorem lookupUniqueOutput_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupUniqueOutputSentence w n i y)) := TheoryTransport.sentence (source_lookupUniqueOutput w n i y)

theorem native_lookupUniqueOutput {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupUniqueOutputSentence w n i y)) := ZFReplay.replay (lookupUniqueOutput_kernel_certificate w n i y)

def lookupAtCandidateSentence {m} (w n i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((StrictLookupSyntax.returned w n i y).imp ((StrictLookupValueSyntax.value w n i y))))).close

theorem source_lookupAtCandidate {m} (w n i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupAtCandidateSentence w n i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StrictLookupSyntax.returned w n i y) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StrictLookupSyntax.returned w n i y) := .hyp (Or.inl rfl)
  exact StrictLookupValue.at_candidate hZ w n i y h0 h1 h2

theorem lookupAtCandidate_kernel_certificate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupAtCandidateSentence w n i y)) := TheoryTransport.sentence (source_lookupAtCandidate w n i y)

theorem native_lookupAtCandidate {m} (w n i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupAtCandidateSentence w n i y)) := ZFReplay.replay (lookupAtCandidate_kernel_certificate w n i y)

def lookupActualFiberSentence {m} (w n r i : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListLengthSyntax.hasLength w n r).imp ((Formula.mem i r).imp ((StrictLookupValueSyntax.fiber w n i))))).close

theorem source_lookupActualFiber {m} (w n r i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupActualFiberSentence w n r i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i r) (Context.add (StructuralListLengthSyntax.hasLength w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListLengthSyntax.hasLength w n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i r) := .hyp (Or.inl rfl)
  exact StrictLookupValue.actual_fiber hZ w n r i h0 h1 h2

theorem lookupActualFiber_kernel_certificate {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupActualFiberSentence w n r i)) := TheoryTransport.sentence (source_lookupActualFiber w n r i)

theorem native_lookupActualFiber {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupActualFiberSentence w n r i)) := ZFReplay.replay (lookupActualFiber_kernel_certificate w n r i)

def lookupFiberIffRangeSentence {m} (w n r i : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListLengthSyntax.hasLength w n r).imp ((Formula.mem i w).imp (((StrictLookupValueSyntax.fiber w n i).iff (.mem i r)))))).close

theorem source_lookupFiberIffRange {m} (w n r i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupFiberIffRangeSentence w n r i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (StructuralListLengthSyntax.hasLength w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListLengthSyntax.hasLength w n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact StrictLookupValue.fiber_iff_bound hZ w n r i h0 h1 h2

theorem lookupFiberIffRange_kernel_certificate {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupFiberIffRangeSentence w n r i)) := TheoryTransport.sentence (source_lookupFiberIffRange w n r i)

theorem native_lookupFiberIffRange {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupFiberIffRangeSentence w n r i)) := ZFReplay.replay (lookupFiberIffRange_kernel_certificate w n r i)

def lookupHasOutputIffRangeSentence {m} (w n r i : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListLengthSyntax.hasLength w n r).imp ((Formula.mem i w).imp (((StrictLookupSyntax.hasOutput w n i).iff (.mem i r)))))).close

theorem source_lookupHasOutputIffRange {m} (w n r i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupHasOutputIffRangeSentence w n r i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (StructuralListLengthSyntax.hasLength w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListLengthSyntax.hasLength w n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact StrictLookupValue.has_output_iff_bound hZ w n r i h0 h1 h2

theorem lookupHasOutputIffRange_kernel_certificate {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupHasOutputIffRangeSentence w n r i)) := TheoryTransport.sentence (source_lookupHasOutputIffRange w n r i)

theorem native_lookupHasOutputIffRange {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupHasOutputIffRangeSentence w n r i)) := ZFReplay.replay (lookupHasOutputIffRange_kernel_certificate w n r i)

def lookupRejectedIffNotRangeSentence {m} (w n r i : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListLengthSyntax.hasLength w n r).imp ((Formula.mem i w).imp (((StrictLookupSyntax.rejected w n i).iff (Formula.mem i r).neg))))).close

theorem source_lookupRejectedIffNotRange {m} (w n r i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupRejectedIffNotRangeSentence w n r i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (StructuralListLengthSyntax.hasLength w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListLengthSyntax.hasLength w n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact StrictLookupValue.rejected_iff_not_bound hZ w n r i h0 h1 h2

theorem lookupRejectedIffNotRange_kernel_certificate {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupRejectedIffNotRangeSentence w n r i)) := TheoryTransport.sentence (source_lookupRejectedIffNotRange w n r i)

theorem native_lookupRejectedIffNotRange {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupRejectedIffNotRangeSentence w n r i)) := ZFReplay.replay (lookupRejectedIffNotRange_kernel_certificate w n r i)

def lookupOutOfBoundsRejectedSentence {m} (w n r i : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListLengthSyntax.hasLength w n r).imp ((Formula.mem i w).imp (((Formula.mem i r).neg).imp ((StrictLookupSyntax.rejected w n i)))))).close

theorem source_lookupOutOfBoundsRejected {m} (w n r i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupOutOfBoundsRejectedSentence w n r i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem i r).neg) (Context.add (Formula.mem i w) (Context.add (StructuralListLengthSyntax.hasLength w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (StructuralListLengthSyntax.hasLength w n r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ ((Formula.mem i r).neg) := .hyp (Or.inl rfl)
  exact StrictLookupValue.out_of_bounds_rejected hZ w n r i h0 h1 h2 h3

theorem lookupOutOfBoundsRejected_kernel_certificate {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupOutOfBoundsRejectedSentence w n r i)) := TheoryTransport.sentence (source_lookupOutOfBoundsRejected w n r i)

theorem native_lookupOutOfBoundsRejected {m} (w n r i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupOutOfBoundsRejectedSentence w n r i)) := ZFReplay.replay (lookupOutOfBoundsRejected_kernel_certificate w n r i)

def lookupInRangeFieldIffSentence {m} (w n r i y : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListLengthSyntax.hasLength w n r).imp ((Formula.mem i r).imp (((StrictLookupSyntax.returned w n i y).iff (StructuralListFieldSyntax.field w n i y)))))).close

theorem source_lookupInRangeFieldIff {m} (w n r i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupInRangeFieldIffSentence w n r i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i r) (Context.add (StructuralListLengthSyntax.hasLength w n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (StructuralListLengthSyntax.hasLength w n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem i r) := .hyp (Or.inl rfl)
  exact StrictLookupValue.in_range_field_iff hZ w n r i y h0 h1 h2

theorem lookupInRangeFieldIff_kernel_certificate {m} (w n r i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupInRangeFieldIffSentence w n r i y)) := TheoryTransport.sentence (source_lookupInRangeFieldIff w n r i y)

theorem native_lookupInRangeFieldIff {m} (w n r i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupInRangeFieldIffSentence w n r i y)) := ZFReplay.replay (lookupInRangeFieldIff_kernel_certificate w n r i y)

def lookupFreeImageAtEdgeSentence {m} (w a c L J r i j q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L J).imp ((SyntaxMapCodeSyntax.encoded w r a c J).imp ((GraphSyntax.edge r i j).imp (((StrictLookupSyntax.returned w L i q).iff (SyntaxVariableSyntax.code false w j q))))))).close

theorem source_lookupFreeImageAtEdge {m} (w a c L J r i j q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (lookupFreeImageAtEdgeSentence w a c L J r i j q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (GraphSyntax.edge r i j) (Context.add (SyntaxMapCodeSyntax.encoded w r a c J) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L J) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L J) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c J) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (GraphSyntax.edge r i j) := .hyp (Or.inl rfl)
  exact StrictLookupValue.free_image_at_edge hZ w a c L J r i j q h0 h1 h2 h3

theorem lookupFreeImageAtEdge_kernel_certificate {m} (w a c L J r i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (lookupFreeImageAtEdgeSentence w a c L J r i j q)) := TheoryTransport.sentence (source_lookupFreeImageAtEdge w a c L J r i j q)

theorem native_lookupFreeImageAtEdge {m} (w a c L J r i j q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (lookupFreeImageAtEdgeSentence w a c L J r i j q)) := ZFReplay.replay (lookupFreeImageAtEdge_kernel_certificate w a c L J r i j q)

end PPAC.Migration.Internal.ObjectStrictLookup
