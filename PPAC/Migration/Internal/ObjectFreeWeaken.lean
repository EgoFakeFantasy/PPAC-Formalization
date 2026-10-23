import PPAC.Migration.Internal.OriginalScalarValues

/-! 原模式0自由加强实际后继值、完整成功域及四变量分支统一对象接口的原核证书。 -/
namespace PPAC.Migration.Internal.ObjectFreeWeaken
open Source SourceAlgebra SourceLogic OmegaSyntax

def actualSuccessorVariableValueSentence {m} (w idx : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem idx w).imp ((FreeWeakenValueSyntax.hasShifted w idx)))).close

theorem source_actualSuccessorVariableValue {m} (w idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualSuccessorVariableValueSentence w idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem idx w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem idx w) := .hyp (Or.inl rfl)
  exact FreeWeakenValue.exists_shifted hZ w idx h0 h1

theorem actualSuccessorVariableValue_kernel_certificate {m} (w idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualSuccessorVariableValueSentence w idx)) := TheoryTransport.sentence (source_actualSuccessorVariableValue w idx)

theorem native_actualSuccessorVariableValue {m} (w idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualSuccessorVariableValueSentence w idx)) := ZFReplay.replay (actualSuccessorVariableValue_kernel_certificate w idx)

def successorVariableValueExactDomainSentence {m} (w idx : Fin m) : Source.Sentence := ((omega w).imp (((FreeWeakenValueSyntax.hasShifted w idx).iff (Formula.mem idx w)))).close

theorem source_successorVariableValueExactDomain {m} (w idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (successorVariableValueExactDomainSentence w idx) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeWeakenValue.has_shifted_iff_natural hZ w idx h0

theorem successorVariableValueExactDomain_kernel_certificate {m} (w idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (successorVariableValueExactDomainSentence w idx)) := TheoryTransport.sentence (source_successorVariableValueExactDomain w idx)

theorem native_successorVariableValueExactDomain {m} (w idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (successorVariableValueExactDomainSentence w idx)) := ZFReplay.replay (successorVariableValueExactDomain_kernel_certificate w idx)

def successorVariableValueAtActualSuccessorSentence {m} (w idx y s : Fin m) : Source.Sentence := ((successor s idx).imp (((FreeWeakenValueSyntax.shifted w idx y).iff (SyntaxVariableSyntax.code false w s y)))).close

theorem source_successorVariableValueAtActualSuccessor {m} (w idx y s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (successorVariableValueAtActualSuccessorSentence w idx y s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (successor s idx) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (successor s idx) := .hyp (Or.inl rfl)
  exact FreeWeakenValue.at_successor hZ w idx y s h0

theorem successorVariableValueAtActualSuccessor_kernel_certificate {m} (w idx y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (successorVariableValueAtActualSuccessorSentence w idx y s)) := TheoryTransport.sentence (source_successorVariableValueAtActualSuccessor w idx y s)

theorem native_successorVariableValueAtActualSuccessor {m} (w idx y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (successorVariableValueAtActualSuccessorSentence w idx y s)) := ZFReplay.replay (successorVariableValueAtActualSuccessor_kernel_certificate w idx y s)

def successorVariableValueNaturalSentence {m} (w idx y : Fin m) : Source.Sentence := ((omega w).imp ((FreeWeakenValueSyntax.shifted w idx y).imp ((Formula.mem y w)))).close

theorem source_successorVariableValueNatural {m} (w idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (successorVariableValueNaturalSentence w idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeWeakenValueSyntax.shifted w idx y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeWeakenValueSyntax.shifted w idx y) := .hyp (Or.inl rfl)
  exact FreeWeakenValue.natural hZ w idx y h0 h1

theorem successorVariableValueNatural_kernel_certificate {m} (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (successorVariableValueNaturalSentence w idx y)) := TheoryTransport.sentence (source_successorVariableValueNatural w idx y)

theorem native_successorVariableValueNatural {m} (w idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (successorVariableValueNaturalSentence w idx y)) := ZFReplay.replay (successorVariableValueNatural_kernel_certificate w idx y)

def successorVariableValueUniqueSentence {m} (w idx y z : Fin m) : Source.Sentence := ((omega w).imp ((FreeWeakenValueSyntax.shifted w idx y).imp ((FreeWeakenValueSyntax.shifted w idx z).imp ((Formula.equal y z))))).close

theorem source_successorVariableValueUnique {m} (w idx y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (successorVariableValueUniqueSentence w idx y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeWeakenValueSyntax.shifted w idx z) (Context.add (FreeWeakenValueSyntax.shifted w idx y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FreeWeakenValueSyntax.shifted w idx y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FreeWeakenValueSyntax.shifted w idx z) := .hyp (Or.inl rfl)
  exact FreeWeakenValue.unique hZ w idx y z h0 h1 h2

theorem successorVariableValueUnique_kernel_certificate {m} (w idx y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (successorVariableValueUniqueSentence w idx y z)) := TheoryTransport.sentence (source_successorVariableValueUnique w idx y z)

theorem native_successorVariableValueUnique {m} (w idx y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (successorVariableValueUniqueSentence w idx y z)) := ZFReplay.replay (successorVariableValueUnique_kernel_certificate w idx y z)

def originalFreeWeakenMatrixSoundSentence {m} (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp ((HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken w r R env).imp ((FreeWeakenValueSyntax.shifted w idx (xs 4)))))))).close

theorem source_originalFreeWeakenMatrixSound {m} (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeWeakenMatrixSoundSentence env xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken w r R env) (Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (HornRuleSyntax.matrix YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken w r R env) := .hyp (Or.inl rfl)
  exact OriginalFreeWeakenSound.matrix_shifted hZ w r R idx env xs h0 h1 h2 h3 h4

theorem originalFreeWeakenMatrixSound_kernel_certificate {m} (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeWeakenMatrixSoundSentence env xs w r R idx)) := TheoryTransport.sentence (source_originalFreeWeakenMatrixSound env xs w r R idx)

theorem native_originalFreeWeakenMatrixSound {m} (env : Fin 3 → Fin m) (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeWeakenMatrixSoundSentence env xs w r R idx)) := ZFReplay.replay (originalFreeWeakenMatrixSound_kernel_certificate env xs w r R idx)

def originalFreeWeakenApplicationSoundSentence {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken w r R).imp ((FreeWeakenValueSyntax.shifted w idx (xs 4))))))).close

theorem source_originalFreeWeakenApplicationSound {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeWeakenApplicationSoundSentence xs w r R idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken w r R) (Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectSyntaxTransform.freeWeaken w r R) := .hyp (Or.inl rfl)
  exact OriginalFreeWeakenSound.application_shifted hZ w r R idx xs h0 h1 h2 h3

theorem originalFreeWeakenApplicationSound_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeWeakenApplicationSoundSentence xs w r R idx)) := TheoryTransport.sentence (source_originalFreeWeakenApplicationSound xs w r R idx)

theorem native_originalFreeWeakenApplicationSound {m} (xs : Fin 5 → Fin m) (w r R idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeWeakenApplicationSoundSentence xs w r R idx)) := ZFReplay.replay (originalFreeWeakenApplicationSound_kernel_certificate xs w r R idx)

def originalFreeWeakenTraceValueIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 0 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (FreeWeakenValueSyntax.shifted w idx (xs 4)))))))).close

theorem source_originalFreeWeakenTraceValueIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeWeakenTraceValueIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 0 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalFreeWeaken.trace_iff_shifted hZ w r idx xs h0 h1 h2 h3

theorem originalFreeWeakenTraceValueIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeWeakenTraceValueIffSentence xs w r idx)) := TheoryTransport.sentence (source_originalFreeWeakenTraceValueIff xs w r idx)

theorem native_originalFreeWeakenTraceValueIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeWeakenTraceValueIffSentence xs w r idx)) := ZFReplay.replay (originalFreeWeakenTraceValueIff_kernel_certificate xs w r idx)

def originalFreeWeakenPowerTraceValueIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 0 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornLookupPowerCondition.condition w r).iff (FreeWeakenValueSyntax.shifted w idx (xs 4)))))))).close

theorem source_originalFreeWeakenPowerTraceValueIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeWeakenPowerTraceValueIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 0 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalFreeWeaken.power_trace_iff_shifted hZ w r idx xs h0 h1 h2 h3

theorem originalFreeWeakenPowerTraceValueIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeWeakenPowerTraceValueIffSentence xs w r idx)) := TheoryTransport.sentence (source_originalFreeWeakenPowerTraceValueIff xs w r idx)

theorem native_originalFreeWeakenPowerTraceValueIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeWeakenPowerTraceValueIffSentence xs w r idx)) := ZFReplay.replay (originalFreeWeakenPowerTraceValueIff_kernel_certificate xs w r idx)

def originalFreeWeakenTraceCandidateRejectionIffSentence {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral 0 (xs 0)).imp ((SyntaxVariableSyntax.code false w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).neg.iff (FreeWeakenValueSyntax.shifted w idx (xs 4)).neg)))))).close

theorem source_originalFreeWeakenTraceCandidateRejectionIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFreeWeakenTraceCandidateRejectionIffSentence xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral 0 (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 0 (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code false w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalFreeWeaken.rejected_iff hZ w r idx xs h0 h1 h2 h3

theorem originalFreeWeakenTraceCandidateRejectionIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFreeWeakenTraceCandidateRejectionIffSentence xs w r idx)) := TheoryTransport.sentence (source_originalFreeWeakenTraceCandidateRejectionIff xs w r idx)

theorem native_originalFreeWeakenTraceCandidateRejectionIff {m} (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFreeWeakenTraceCandidateRejectionIffSentence xs w r idx)) := ZFReplay.replay (originalFreeWeakenTraceCandidateRejectionIff_kernel_certificate xs w r idx)

def actualOriginalFreeWeakenRootSentence {m} (w d p x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((Formula.mem p w).imp ((Formula.mem x w).imp ((Formula.mem y w).imp ((FreeWeakenResultSyntax.existsRoot w d p x y))))))).close

theorem source_actualOriginalFreeWeakenRoot {m} (w d p x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualOriginalFreeWeakenRootSentence w d p x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem y w) (Context.add (Formula.mem x w) (Context.add (Formula.mem p w) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem y w) := .hyp (Or.inl rfl)
  exact FreeWeakenResultRows.exists_root hZ w d p x y h0 h1 h2 h3 h4

theorem actualOriginalFreeWeakenRoot_kernel_certificate {m} (w d p x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualOriginalFreeWeakenRootSentence w d p x y)) := TheoryTransport.sentence (source_actualOriginalFreeWeakenRoot w d p x y)

theorem native_actualOriginalFreeWeakenRoot {m} (w d p x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualOriginalFreeWeakenRootSentence w d p x y)) := ZFReplay.replay (actualOriginalFreeWeakenRoot_kernel_certificate w d p x y)

def allInternalFreeWeakenReturnedIffSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp (((FreeWeakenResultSyntax.returned w d p x idx y).iff ((FreeWeakenResultSyntax.guard w d p x idx).conj (FreeWeakenValueSyntax.shifted w idx y))))).close

theorem source_allInternalFreeWeakenReturnedIff {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeWeakenReturnedIffSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeWeakenResult.returned_iff hZ w d p x idx y h0

theorem allInternalFreeWeakenReturnedIff_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeWeakenReturnedIffSentence w d p x idx y)) := TheoryTransport.sentence (source_allInternalFreeWeakenReturnedIff w d p x idx y)

theorem native_allInternalFreeWeakenReturnedIff {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeWeakenReturnedIffSentence w d p x idx y)) := ZFReplay.replay (allInternalFreeWeakenReturnedIff_kernel_certificate w d p x idx y)

def validFreeWeakenReturnedValueIffSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp ((FreeWeakenResultSyntax.guard w d p x idx).imp (((FreeWeakenResultSyntax.returned w d p x idx y).iff (FreeWeakenValueSyntax.shifted w idx y))))).close

theorem source_validFreeWeakenReturnedValueIff {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (validFreeWeakenReturnedValueIffSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeWeakenResultSyntax.guard w d p x idx) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeWeakenResultSyntax.guard w d p x idx) := .hyp (Or.inl rfl)
  exact FreeWeakenResult.under_guard_iff hZ w d p x idx y h0 h1

theorem validFreeWeakenReturnedValueIff_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (validFreeWeakenReturnedValueIffSentence w d p x idx y)) := TheoryTransport.sentence (source_validFreeWeakenReturnedValueIff w d p x idx y)

theorem native_validFreeWeakenReturnedValueIff {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (validFreeWeakenReturnedValueIffSentence w d p x idx y)) := ZFReplay.replay (validFreeWeakenReturnedValueIff_kernel_certificate w d p x idx y)

def validFreeWeakenAtActualSuccessorIffSentence {m} (w d p x idx y s : Fin m) : Source.Sentence := ((omega w).imp ((FreeWeakenResultSyntax.guard w d p x idx).imp ((successor s idx).imp (((FreeWeakenResultSyntax.returned w d p x idx y).iff (SyntaxVariableSyntax.code false w s y)))))).close

theorem source_validFreeWeakenAtActualSuccessorIff {m} (w d p x idx y s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (validFreeWeakenAtActualSuccessorIffSentence w d p x idx y s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor s idx) (Context.add (FreeWeakenResultSyntax.guard w d p x idx) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FreeWeakenResultSyntax.guard w d p x idx) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor s idx) := .hyp (Or.inl rfl)
  exact FreeWeakenResult.at_successor_iff hZ w d p x idx y s h0 h1 h2

theorem validFreeWeakenAtActualSuccessorIff_kernel_certificate {m} (w d p x idx y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (validFreeWeakenAtActualSuccessorIffSentence w d p x idx y s)) := TheoryTransport.sentence (source_validFreeWeakenAtActualSuccessorIff w d p x idx y s)

theorem native_validFreeWeakenAtActualSuccessorIff {m} (w d p x idx y s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (validFreeWeakenAtActualSuccessorIffSentence w d p x idx y s)) := ZFReplay.replay (validFreeWeakenAtActualSuccessorIff_kernel_certificate w d p x idx y s)

def allInternalFreeWeakenCandidateRejectionIffSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp (((FreeWeakenResultSyntax.returned w d p x idx y).neg.iff ((FreeWeakenResultSyntax.guard w d p x idx).conj (FreeWeakenValueSyntax.shifted w idx y)).neg))).close

theorem source_allInternalFreeWeakenCandidateRejectionIff {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeWeakenCandidateRejectionIffSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeWeakenResult.rejected_iff hZ w d p x idx y h0

theorem allInternalFreeWeakenCandidateRejectionIff_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeWeakenCandidateRejectionIffSentence w d p x idx y)) := TheoryTransport.sentence (source_allInternalFreeWeakenCandidateRejectionIff w d p x idx y)

theorem native_allInternalFreeWeakenCandidateRejectionIff {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeWeakenCandidateRejectionIffSentence w d p x idx y)) := ZFReplay.replay (allInternalFreeWeakenCandidateRejectionIff_kernel_certificate w d p x idx y)

def allInternalFreeWeakenHasOutputIffSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp (((FreeWeakenResultSyntax.hasOutput w d p x idx).iff (FreeWeakenResultSyntax.guard w d p x idx)))).close

theorem source_allInternalFreeWeakenHasOutputIff {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeWeakenHasOutputIffSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.has_output_iff hZ w d p x idx h0

theorem allInternalFreeWeakenHasOutputIff_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeWeakenHasOutputIffSentence w d p x idx)) := TheoryTransport.sentence (source_allInternalFreeWeakenHasOutputIff w d p x idx)

theorem native_allInternalFreeWeakenHasOutputIff {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeWeakenHasOutputIffSentence w d p x idx)) := ZFReplay.replay (allInternalFreeWeakenHasOutputIff_kernel_certificate w d p x idx)

def allInternalFreeWeakenNoOutputIffSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp (((FreeWeakenResultSyntax.noOutput w d p x idx).iff (FreeWeakenResultSyntax.guard w d p x idx).neg))).close

theorem source_allInternalFreeWeakenNoOutputIff {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeWeakenNoOutputIffSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.no_output_iff hZ w d p x idx h0

theorem allInternalFreeWeakenNoOutputIff_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeWeakenNoOutputIffSentence w d p x idx)) := TheoryTransport.sentence (source_allInternalFreeWeakenNoOutputIff w d p x idx)

theorem native_allInternalFreeWeakenNoOutputIff {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeWeakenNoOutputIffSentence w d p x idx)) := ZFReplay.replay (allInternalFreeWeakenNoOutputIff_kernel_certificate w d p x idx)

def validFreeWeakenActualOutputSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp ((FreeWeakenResultSyntax.guard w d p x idx).imp ((FreeWeakenResultSyntax.hasOutput w d p x idx)))).close

theorem source_validFreeWeakenActualOutput {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (validFreeWeakenActualOutputSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeWeakenResultSyntax.guard w d p x idx) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeWeakenResultSyntax.guard w d p x idx) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.total_on_guard hZ w d p x idx h0 h1

theorem validFreeWeakenActualOutput_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (validFreeWeakenActualOutputSentence w d p x idx)) := TheoryTransport.sentence (source_validFreeWeakenActualOutput w d p x idx)

theorem native_validFreeWeakenActualOutput {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (validFreeWeakenActualOutputSentence w d p x idx)) := ZFReplay.replay (validFreeWeakenActualOutput_kernel_certificate w d p x idx)

def invalidFreeWeakenGuardNoOutputSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp (((FreeWeakenResultSyntax.guard w d p x idx).neg).imp ((FreeWeakenResultSyntax.noOutput w d p x idx)))).close

theorem source_invalidFreeWeakenGuardNoOutput {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (invalidFreeWeakenGuardNoOutputSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FreeWeakenResultSyntax.guard w d p x idx).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FreeWeakenResultSyntax.guard w d p x idx).neg) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.invalid_guard_no_output hZ w d p x idx h0 h1

theorem invalidFreeWeakenGuardNoOutput_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (invalidFreeWeakenGuardNoOutputSentence w d p x idx)) := TheoryTransport.sentence (source_invalidFreeWeakenGuardNoOutput w d p x idx)

theorem native_invalidFreeWeakenGuardNoOutput {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (invalidFreeWeakenGuardNoOutputSentence w d p x idx)) := ZFReplay.replay (invalidFreeWeakenGuardNoOutput_kernel_certificate w d p x idx)

def nonNaturalFreeWeakenParameterNoOutputSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem p w).neg).imp ((FreeWeakenResultSyntax.noOutput w d p x idx)))).close

theorem source_nonNaturalFreeWeakenParameterNoOutput {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nonNaturalFreeWeakenParameterNoOutputSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem p w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem p w).neg) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.invalid_parameter_no_output hZ w d p x idx h0 h1

theorem nonNaturalFreeWeakenParameterNoOutput_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nonNaturalFreeWeakenParameterNoOutputSentence w d p x idx)) := TheoryTransport.sentence (source_nonNaturalFreeWeakenParameterNoOutput w d p x idx)

theorem native_nonNaturalFreeWeakenParameterNoOutput {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nonNaturalFreeWeakenParameterNoOutputSentence w d p x idx)) := ZFReplay.replay (nonNaturalFreeWeakenParameterNoOutput_kernel_certificate w d p x idx)

def nonNaturalFreeWeakenDepthNoOutputSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem d w).neg).imp ((FreeWeakenResultSyntax.noOutput w d p x idx)))).close

theorem source_nonNaturalFreeWeakenDepthNoOutput {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nonNaturalFreeWeakenDepthNoOutputSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem d w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem d w).neg) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.invalid_depth_no_output hZ w d p x idx h0 h1

theorem nonNaturalFreeWeakenDepthNoOutput_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nonNaturalFreeWeakenDepthNoOutputSentence w d p x idx)) := TheoryTransport.sentence (source_nonNaturalFreeWeakenDepthNoOutput w d p x idx)

theorem native_nonNaturalFreeWeakenDepthNoOutput {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nonNaturalFreeWeakenDepthNoOutputSentence w d p x idx)) := ZFReplay.replay (nonNaturalFreeWeakenDepthNoOutput_kernel_certificate w d p x idx)

def invalidFreeWeakenInputNoOutputSentence {m} (w d p x idx : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxVariableSyntax.code false w idx x).neg).imp ((FreeWeakenResultSyntax.noOutput w d p x idx)))).close

theorem source_invalidFreeWeakenInputNoOutput {m} (w d p x idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (invalidFreeWeakenInputNoOutputSentence w d p x idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxVariableSyntax.code false w idx x).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((SyntaxVariableSyntax.code false w idx x).neg) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.invalid_input_no_output hZ w d p x idx h0 h1

theorem invalidFreeWeakenInputNoOutput_kernel_certificate {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (invalidFreeWeakenInputNoOutputSentence w d p x idx)) := TheoryTransport.sentence (source_invalidFreeWeakenInputNoOutput w d p x idx)

theorem native_invalidFreeWeakenInputNoOutput {m} (w d p x idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (invalidFreeWeakenInputNoOutputSentence w d p x idx)) := ZFReplay.replay (invalidFreeWeakenInputNoOutput_kernel_certificate w d p x idx)

def allInternalFreeWeakenOutputNaturalSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp ((FreeWeakenResultSyntax.returned w d p x idx y).imp ((Formula.mem y w)))).close

theorem source_allInternalFreeWeakenOutputNatural {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeWeakenOutputNaturalSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeWeakenResultSyntax.returned w d p x idx y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeWeakenResultSyntax.returned w d p x idx y) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.output_natural hZ w d p x idx y h0 h1

theorem allInternalFreeWeakenOutputNatural_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeWeakenOutputNaturalSentence w d p x idx y)) := TheoryTransport.sentence (source_allInternalFreeWeakenOutputNatural w d p x idx y)

theorem native_allInternalFreeWeakenOutputNatural {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeWeakenOutputNaturalSentence w d p x idx y)) := ZFReplay.replay (allInternalFreeWeakenOutputNatural_kernel_certificate w d p x idx y)

def nonNaturalFreeWeakenOutputRejectedSentence {m} (w d p x idx y : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem y w).neg).imp (((FreeWeakenResultSyntax.returned w d p x idx y).neg)))).close

theorem source_nonNaturalFreeWeakenOutputRejected {m} (w d p x idx y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nonNaturalFreeWeakenOutputRejectedSentence w d p x idx y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem y w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem y w).neg) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.invalid_output_rejected hZ w d p x idx y h0 h1

theorem nonNaturalFreeWeakenOutputRejected_kernel_certificate {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nonNaturalFreeWeakenOutputRejectedSentence w d p x idx y)) := TheoryTransport.sentence (source_nonNaturalFreeWeakenOutputRejected w d p x idx y)

theorem native_nonNaturalFreeWeakenOutputRejected {m} (w d p x idx y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nonNaturalFreeWeakenOutputRejectedSentence w d p x idx y)) := ZFReplay.replay (nonNaturalFreeWeakenOutputRejected_kernel_certificate w d p x idx y)

def allInternalFreeWeakenOutputUniqueSentence {m} (w d p x idx y z : Fin m) : Source.Sentence := ((omega w).imp ((FreeWeakenResultSyntax.returned w d p x idx y).imp ((FreeWeakenResultSyntax.returned w d p x idx z).imp ((Formula.equal y z))))).close

theorem source_allInternalFreeWeakenOutputUnique {m} (w d p x idx y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allInternalFreeWeakenOutputUniqueSentence w d p x idx y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeWeakenResultSyntax.returned w d p x idx z) (Context.add (FreeWeakenResultSyntax.returned w d p x idx y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FreeWeakenResultSyntax.returned w d p x idx y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FreeWeakenResultSyntax.returned w d p x idx z) := .hyp (Or.inl rfl)
  exact FreeWeakenOutcome.unique hZ w d p x idx y z h0 h1 h2

theorem allInternalFreeWeakenOutputUnique_kernel_certificate {m} (w d p x idx y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allInternalFreeWeakenOutputUniqueSentence w d p x idx y z)) := TheoryTransport.sentence (source_allInternalFreeWeakenOutputUnique w d p x idx y z)

theorem native_allInternalFreeWeakenOutputUnique {m} (w d p x idx y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allInternalFreeWeakenOutputUniqueSentence w d p x idx y z)) := ZFReplay.replay (allInternalFreeWeakenOutputUnique_kernel_certificate w d p x idx y z)

def allFourOriginalVariableTraceValueIffSentence {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).iff (OriginalScalarValues.valueSpec three bound w (xs 2) (xs 3) idx (xs 4)))))))).close

theorem source_allFourOriginalVariableTraceValueIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allFourOriginalVariableTraceValueIffSentence three bound xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalScalarValues.trace_iff_value hZ three bound w r idx xs h0 h1 h2 h3

theorem allFourOriginalVariableTraceValueIff_kernel_certificate {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allFourOriginalVariableTraceValueIffSentence three bound xs w r idx)) := TheoryTransport.sentence (source_allFourOriginalVariableTraceValueIff three bound xs w r idx)

theorem native_allFourOriginalVariableTraceValueIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allFourOriginalVariableTraceValueIffSentence three bound xs w r idx)) := ZFReplay.replay (allFourOriginalVariableTraceValueIff_kernel_certificate three bound xs w r idx)

def allFourOriginalVariablePowerTraceValueIffSentence {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornLookupPowerCondition.condition w r).iff (OriginalScalarValues.valueSpec three bound w (xs 2) (xs 3) idx (xs 4)))))))).close

theorem source_allFourOriginalVariablePowerTraceValueIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allFourOriginalVariablePowerTraceValueIffSentence three bound xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalScalarValues.power_trace_iff_value hZ three bound w r idx xs h0 h1 h2 h3

theorem allFourOriginalVariablePowerTraceValueIff_kernel_certificate {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allFourOriginalVariablePowerTraceValueIffSentence three bound xs w r idx)) := TheoryTransport.sentence (source_allFourOriginalVariablePowerTraceValueIff three bound xs w r idx)

theorem native_allFourOriginalVariablePowerTraceValueIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allFourOriginalVariablePowerTraceValueIffSentence three bound xs w r idx)) := ZFReplay.replay (allFourOriginalVariablePowerTraceValueIff_kernel_certificate three bound xs w r idx)

def allFourOriginalVariableCandidateRejectionIffSentence {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 1 w xs r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)).imp ((SyntaxVariableSyntax.code bound w idx (xs 3)).imp (((HornLookupConditionSyntax.condition w r).neg.iff (OriginalScalarValues.valueSpec three bound w (xs 2) (xs 3) idx (xs 4)).neg)))))).close

theorem source_allFourOriginalVariableCandidateRejectionIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allFourOriginalVariableCandidateRejectionIffSentence three bound xs w r idx) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code bound w idx (xs 3)) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) (Context.add (SyntaxNodeSyntax.constructor 5 1 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w xs r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (xs 0)) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxVariableSyntax.code bound w idx (xs 3)) := .hyp (Or.inl rfl)
  exact OriginalScalarValues.rejected_iff hZ three bound w r idx xs h0 h1 h2 h3

theorem allFourOriginalVariableCandidateRejectionIff_kernel_certificate {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allFourOriginalVariableCandidateRejectionIffSentence three bound xs w r idx)) := TheoryTransport.sentence (source_allFourOriginalVariableCandidateRejectionIff three bound xs w r idx)

theorem native_allFourOriginalVariableCandidateRejectionIff {m} (three bound : Bool) (xs : Fin 5 → Fin m) (w r idx : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allFourOriginalVariableCandidateRejectionIffSentence three bound xs w r idx)) := ZFReplay.replay (allFourOriginalVariableCandidateRejectionIff_kernel_certificate three bound xs w r idx)

end PPAC.Migration.Internal.ObjectFreeWeaken
