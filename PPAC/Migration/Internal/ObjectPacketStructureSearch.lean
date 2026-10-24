import PPAC.Migration.Internal.PacketStructureSearchLaws

/-! All original structural search bounds discharged and exact actual typed recursion for all internal candidates; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketStructureSearch
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetStructureSearchAllOriginalAssignmentNaturalitySentence {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureApplicationSyntax.localCase b w V r env).imp ((HornExprSyntax.environmentNat (PacketStructureApplicationSyntax.rule b).arity w env)))).close

theorem source_packetStructureSearchAllOriginalAssignmentNaturality {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchAllOriginalAssignmentNaturalitySentence b env w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureApplicationSyntax.localCase b w V r env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureApplicationSyntax.localCase b w V r env) := .hyp (Or.inl rfl)
  exact PacketStructureSearchEnvironment.local_natural hZ b w V r env h0 h1

theorem packetStructureSearchAllOriginalAssignmentNaturality_kernel_certificate {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchAllOriginalAssignmentNaturalitySentence b env w V r)) := TheoryTransport.sentence (source_packetStructureSearchAllOriginalAssignmentNaturality b env w V r)

theorem native_packetStructureSearchAllOriginalAssignmentNaturality {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchAllOriginalAssignmentNaturalitySentence b env w V r)) := ZFReplay.replay (packetStructureSearchAllOriginalAssignmentNaturality_kernel_certificate b env w V r)

def packetStructureSearchAllOriginalAssignmentBoundsSentence {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp ((PacketStructureApplicationSyntax.localCase b w V r env).imp ((HornExprBounds.environmentBound (PacketStructureApplicationSyntax.rule b).arity r env))))).close

theorem source_packetStructureSearchAllOriginalAssignmentBounds {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchAllOriginalAssignmentBoundsSentence b env w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureApplicationSyntax.localCase b w V r env) (Context.add (PacketTraceCore.value w V) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketStructureApplicationSyntax.localCase b w V r env) := .hyp (Or.inl rfl)
  exact PacketStructureSearchBounds.local_bounds hZ b w V r env h0 h1 h2

theorem packetStructureSearchAllOriginalAssignmentBounds_kernel_certificate {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchAllOriginalAssignmentBoundsSentence b env w V r)) := TheoryTransport.sentence (source_packetStructureSearchAllOriginalAssignmentBounds b env w V r)

theorem native_packetStructureSearchAllOriginalAssignmentBounds {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchAllOriginalAssignmentBoundsSentence b env w V r)) := ZFReplay.replay (packetStructureSearchAllOriginalAssignmentBounds_kernel_certificate b env w V r)

def packetStructureSearchActualAffineTailOnlyOmegaSentence {m} (w V d q n : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp ((PacketTokenSyntax.tagEntry 1 w V d q n).imp ((NaturalAdditionBounds.below q n))))).close

theorem source_packetStructureSearchActualAffineTailOnlyOmega {m} (w V d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchActualAffineTailOnlyOmegaSentence w V d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenSyntax.tagEntry 1 w V d q n) (Context.add (PacketTraceCore.value w V) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTokenSyntax.tagEntry 1 w V d q n) := .hyp (Or.inl rfl)
  exact PacketStructureSearchArithmetic.affine_tail hZ w V d q n h0 h1 h2

theorem packetStructureSearchActualAffineTailOnlyOmega_kernel_certificate {m} (w V d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchActualAffineTailOnlyOmegaSentence w V d q n)) := TheoryTransport.sentence (source_packetStructureSearchActualAffineTailOnlyOmega w V d q n)

theorem native_packetStructureSearchActualAffineTailOnlyOmega {m} (w V d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchActualAffineTailOnlyOmegaSentence w V d q n)) := ZFReplay.replay (packetStructureSearchActualAffineTailOnlyOmega_kernel_certificate w V d q n)

def packetStructureSearchFourOriginalApplicationsIffSentence {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp (((HornApplicationSyntax.application (PacketStructureApplicationSyntax.rule b) w r V).iff (PacketStructureApplicationSyntax.outcome b w V r))))).close

theorem source_packetStructureSearchFourOriginalApplicationsIff {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchFourOriginalApplicationsIffSentence b w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketStructureSearchApplication.application_iff hZ b w V r h0 h1

theorem packetStructureSearchFourOriginalApplicationsIff_kernel_certificate {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchFourOriginalApplicationsIffSentence b w V r)) := TheoryTransport.sentence (source_packetStructureSearchFourOriginalApplicationsIff b w V r)

theorem native_packetStructureSearchFourOriginalApplicationsIff {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchFourOriginalApplicationsIffSentence b w V r)) := ZFReplay.replay (packetStructureSearchFourOriginalApplicationsIff_kernel_certificate b w V r)

def packetStructureSearchActualRootConditionRecursionIffSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp ((PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r).imp (((PacketTraceSyntax.condition w r).iff (PacketStructureRootSyntax.criterion f w V xs)))))).close

theorem source_packetStructureSearchActualRootConditionRecursionIff {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchActualRootConditionRecursionIffSentence f xs w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r) (Context.add (PacketTraceCore.value w V) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r) := .hyp (Or.inl rfl)
  exact PacketStructureSearchEquation.condition_iff_criterion hZ f w V r xs h0 h1 h2

theorem packetStructureSearchActualRootConditionRecursionIff_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchActualRootConditionRecursionIffSentence f xs w V r)) := TheoryTransport.sentence (source_packetStructureSearchActualRootConditionRecursionIff f xs w V r)

theorem native_packetStructureSearchActualRootConditionRecursionIff {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchActualRootConditionRecursionIffSentence f xs w V r)) := ZFReplay.replay (packetStructureSearchActualRootConditionRecursionIff_kernel_certificate f xs w V r)

def packetStructureSearchTypedActualAcceptanceBackwardSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat (PacketStructureDispatchData.width f) w xs).imp ((PacketStructureAcceptedSyntax.criterion f w xs).imp ((PacketStructureAcceptedSyntax.accepted (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs))))).close

theorem source_packetStructureSearchTypedActualAcceptanceBackward {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchTypedActualAcceptanceBackwardSentence f xs w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureAcceptedSyntax.criterion f w xs) (Context.add (HornExprSyntax.environmentNat (PacketStructureDispatchData.width f) w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat (PacketStructureDispatchData.width f) w xs) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketStructureAcceptedSyntax.criterion f w xs) := .hyp (Or.inl rfl)
  exact PacketStructureSearchAccepted.backward hZ f w xs h0 h1 h2

theorem packetStructureSearchTypedActualAcceptanceBackward_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchTypedActualAcceptanceBackwardSentence f xs w)) := TheoryTransport.sentence (source_packetStructureSearchTypedActualAcceptanceBackward f xs w)

theorem native_packetStructureSearchTypedActualAcceptanceBackward {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchTypedActualAcceptanceBackwardSentence f xs w)) := ZFReplay.replay (packetStructureSearchTypedActualAcceptanceBackward_kernel_certificate f xs w)

def packetStructureSearchActualAcceptanceTypedRecursionIffSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp (((PacketStructureAcceptedSyntax.accepted (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs).iff ((HornExprSyntax.environmentNat (PacketStructureDispatchData.width f) w xs).conj (PacketStructureAcceptedSyntax.criterion f w xs))))).close

theorem source_packetStructureSearchActualAcceptanceTypedRecursionIff {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchActualAcceptanceTypedRecursionIffSentence f xs w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureSearchAccepted.accepted_iff hZ f w xs h0

theorem packetStructureSearchActualAcceptanceTypedRecursionIff_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchActualAcceptanceTypedRecursionIffSentence f xs w)) := TheoryTransport.sentence (source_packetStructureSearchActualAcceptanceTypedRecursionIff f xs w)

theorem native_packetStructureSearchActualAcceptanceTypedRecursionIff {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchActualAcceptanceTypedRecursionIffSentence f xs w)) := ZFReplay.replay (packetStructureSearchActualAcceptanceTypedRecursionIff_kernel_certificate f xs w)

def packetStructureSearchActualTreeTypedRecursionIffSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp (((PacketStructureAcceptedSyntax.tree w n t a).iff ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three n t a)).conj (PacketStructureAcceptedSyntax.treeCase w n t a))))).close

theorem source_packetStructureSearchActualTreeTypedRecursionIff {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchActualTreeTypedRecursionIffSentence w n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureSearchLaws.tree_iff hZ w n t a h0

theorem packetStructureSearchActualTreeTypedRecursionIff_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchActualTreeTypedRecursionIffSentence w n t a)) := TheoryTransport.sentence (source_packetStructureSearchActualTreeTypedRecursionIff w n t a)

theorem native_packetStructureSearchActualTreeTypedRecursionIff {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchActualTreeTypedRecursionIffSentence w n t a)) := ZFReplay.replay (packetStructureSearchActualTreeTypedRecursionIff_kernel_certificate w n t a)

def packetStructureSearchActualForestTypedRecursionIffSentence {m} (w n l t a : Fin m) : Source.Sentence := ((omega w).imp (((PacketStructureAcceptedSyntax.forest w n l t a).iff ((HornExprSyntax.environmentNat 4 w (PacketStructureSyntax.four n l t a)).conj ((PacketStructureRootSyntax.nilCase n l t a).disj (PacketStructureAcceptedSyntax.consCase w n l t a)))))).close

theorem source_packetStructureSearchActualForestTypedRecursionIff {m} (w n l t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchActualForestTypedRecursionIffSentence w n l t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureSearchLaws.forest_iff hZ w n l t a h0

theorem packetStructureSearchActualForestTypedRecursionIff_kernel_certificate {m} (w n l t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchActualForestTypedRecursionIffSentence w n l t a)) := TheoryTransport.sentence (source_packetStructureSearchActualForestTypedRecursionIff w n l t a)

theorem native_packetStructureSearchActualForestTypedRecursionIff {m} (w n l t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchActualForestTypedRecursionIffSentence w n l t a)) := ZFReplay.replay (packetStructureSearchActualForestTypedRecursionIff_kernel_certificate w n l t a)

def packetStructureSearchActualPacketTypedRecursionIffSentence {m} (w a n : Fin m) : Source.Sentence := ((omega w).imp (((PacketStructureAcceptedSyntax.packet w a n).iff ((HornExprSyntax.environmentNat 2 w (SyntaxAtomSyntax.two a n)).conj (PacketStructureAcceptedSyntax.packetCase w a n))))).close

theorem source_packetStructureSearchActualPacketTypedRecursionIff {m} (w a n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchActualPacketTypedRecursionIffSentence w a n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureSearchLaws.packet_iff hZ w a n h0

theorem packetStructureSearchActualPacketTypedRecursionIff_kernel_certificate {m} (w a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchActualPacketTypedRecursionIffSentence w a n)) := TheoryTransport.sentence (source_packetStructureSearchActualPacketTypedRecursionIff w a n)

theorem native_packetStructureSearchActualPacketTypedRecursionIff {m} (w a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchActualPacketTypedRecursionIffSentence w a n)) := ZFReplay.replay (packetStructureSearchActualPacketTypedRecursionIff_kernel_certificate w a n)

def packetStructureSearchAllInternalRootConditionIffSentence {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp ((PacketStructureSearchLawSyntax.allRoot f w V)))).close

theorem source_packetStructureSearchAllInternalRootConditionIff {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchAllInternalRootConditionIffSentence f w V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketStructureSearchLaws.all_root hZ f w V h0 h1

theorem packetStructureSearchAllInternalRootConditionIff_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchAllInternalRootConditionIffSentence f w V)) := TheoryTransport.sentence (source_packetStructureSearchAllInternalRootConditionIff f w V)

theorem native_packetStructureSearchAllInternalRootConditionIff {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchAllInternalRootConditionIffSentence f w V)) := ZFReplay.replay (packetStructureSearchAllInternalRootConditionIff_kernel_certificate f w V)

def packetStructureSearchAllInternalActualTypedRecursionSentence {m} (f : PacketStructureDispatchData.Family) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSearchLawSyntax.allActual f w))).close

theorem source_packetStructureSearchAllInternalActualTypedRecursion {m} (f : PacketStructureDispatchData.Family) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchAllInternalActualTypedRecursionSentence f w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureSearchLaws.all_actual hZ f w h0

theorem packetStructureSearchAllInternalActualTypedRecursion_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchAllInternalActualTypedRecursionSentence f w)) := TheoryTransport.sentence (source_packetStructureSearchAllInternalActualTypedRecursion f w)

theorem native_packetStructureSearchAllInternalActualTypedRecursion {m} (f : PacketStructureDispatchData.Family) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchAllInternalActualTypedRecursionSentence f w)) := ZFReplay.replay (packetStructureSearchAllInternalActualTypedRecursion_kernel_certificate f w)

def packetStructureSearchAllThreeActualTypedRecursionLawsSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSearchLawSyntax.allSystem w))).close

theorem source_packetStructureSearchAllThreeActualTypedRecursionLaws {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchAllThreeActualTypedRecursionLawsSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureSearchLaws.all_system hZ w h0

theorem packetStructureSearchAllThreeActualTypedRecursionLaws_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchAllThreeActualTypedRecursionLawsSentence w)) := TheoryTransport.sentence (source_packetStructureSearchAllThreeActualTypedRecursionLaws w)

theorem native_packetStructureSearchAllThreeActualTypedRecursionLaws {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchAllThreeActualTypedRecursionLawsSentence w)) := ZFReplay.replay (packetStructureSearchAllThreeActualTypedRecursionLaws_kernel_certificate w)

def packetStructureSearchCanonicalRootSystemExistsOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSearchLawSyntax.existsCanonical w))).close

theorem source_packetStructureSearchCanonicalRootSystemExistsOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureSearchCanonicalRootSystemExistsOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureSearchLaws.exists_canonical hZ w h0

theorem packetStructureSearchCanonicalRootSystemExistsOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureSearchCanonicalRootSystemExistsOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetStructureSearchCanonicalRootSystemExistsOnlyOmega w)

theorem native_packetStructureSearchCanonicalRootSystemExistsOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureSearchCanonicalRootSystemExistsOnlyOmegaSentence w)) := ZFReplay.replay (packetStructureSearchCanonicalRootSystemExistsOnlyOmega_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketStructureSearch
