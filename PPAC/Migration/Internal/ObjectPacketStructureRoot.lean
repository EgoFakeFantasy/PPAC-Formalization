import PPAC.Migration.Internal.PacketStructureRootLaws

/-! All original structural root fields normalized and actual independent recursion follows from omega and acceptance; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketStructureRoot
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetStructureRootTreeFieldsIffSentence {m} (w V n t a r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSyntax.treeRow w n t a r).imp (((PacketStructureApplicationSyntax.outcome .tree w V r).iff (PacketStructureRootSyntax.treeCase w V n t a))))).close

theorem source_packetStructureRootTreeFieldsIff {m} (w V n t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootTreeFieldsIffSentence w V n t a r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureSyntax.treeRow w n t a r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureSyntax.treeRow w n t a r) := .hyp (Or.inl rfl)
  exact PacketStructureRootTree.root_iff hZ w V n t a r h0 h1

theorem packetStructureRootTreeFieldsIff_kernel_certificate {m} (w V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootTreeFieldsIffSentence w V n t a r)) := TheoryTransport.sentence (source_packetStructureRootTreeFieldsIff w V n t a r)

theorem native_packetStructureRootTreeFieldsIff {m} (w V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootTreeFieldsIffSentence w V n t a r)) := ZFReplay.replay (packetStructureRootTreeFieldsIff_kernel_certificate w V n t a r)

def packetStructureRootForestNilFieldsIffSentence {m} (w V n l t a r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSyntax.forestRow w n l t a r).imp (((PacketStructureApplicationSyntax.outcome .nil w V r).iff (PacketStructureRootSyntax.nilCase n l t a))))).close

theorem source_packetStructureRootForestNilFieldsIff {m} (w V n l t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootForestNilFieldsIffSentence w V n l t a r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureSyntax.forestRow w n l t a r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureSyntax.forestRow w n l t a r) := .hyp (Or.inl rfl)
  exact PacketStructureRootNil.root_iff hZ w V n l t a r h0 h1

theorem packetStructureRootForestNilFieldsIff_kernel_certificate {m} (w V n l t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootForestNilFieldsIffSentence w V n l t a r)) := TheoryTransport.sentence (source_packetStructureRootForestNilFieldsIff w V n l t a r)

theorem native_packetStructureRootForestNilFieldsIff {m} (w V n l t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootForestNilFieldsIffSentence w V n l t a r)) := ZFReplay.replay (packetStructureRootForestNilFieldsIff_kernel_certificate w V n l t a r)

def packetStructureRootForestConsFieldsIffSentence {m} (w V n l t a r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSyntax.forestRow w n l t a r).imp (((PacketStructureApplicationSyntax.outcome .cons w V r).iff (PacketStructureRootSyntax.consCase w V n l t a))))).close

theorem source_packetStructureRootForestConsFieldsIff {m} (w V n l t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootForestConsFieldsIffSentence w V n l t a r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureSyntax.forestRow w n l t a r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureSyntax.forestRow w n l t a r) := .hyp (Or.inl rfl)
  exact PacketStructureRootCons.root_iff hZ w V n l t a r h0 h1

theorem packetStructureRootForestConsFieldsIff_kernel_certificate {m} (w V n l t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootForestConsFieldsIffSentence w V n l t a r)) := TheoryTransport.sentence (source_packetStructureRootForestConsFieldsIff w V n l t a r)

theorem native_packetStructureRootForestConsFieldsIff {m} (w V n l t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootForestConsFieldsIffSentence w V n l t a r)) := ZFReplay.replay (packetStructureRootForestConsFieldsIff_kernel_certificate w V n l t a r)

def packetStructureRootPacketFieldsIffSentence {m} (w V a n r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSyntax.packetRow w a n r).imp (((PacketStructureApplicationSyntax.outcome .packet w V r).iff (PacketStructureRootSyntax.packetCase w V a n))))).close

theorem source_packetStructureRootPacketFieldsIff {m} (w V a n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootPacketFieldsIffSentence w V a n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureSyntax.packetRow w a n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureSyntax.packetRow w a n r) := .hyp (Or.inl rfl)
  exact PacketStructureRootPacket.root_iff hZ w V a n r h0 h1

theorem packetStructureRootPacketFieldsIff_kernel_certificate {m} (w V a n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootPacketFieldsIffSentence w V a n r)) := TheoryTransport.sentence (source_packetStructureRootPacketFieldsIff w V a n r)

theorem native_packetStructureRootPacketFieldsIff {m} (w V a n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootPacketFieldsIffSentence w V a n r)) := ZFReplay.replay (packetStructureRootPacketFieldsIff_kernel_certificate w V a n r)

def packetStructureRootAllActualOutcomesNormalizedSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r).imp (((PacketStructureDispatch.results false f w V r).iff (PacketStructureRootSyntax.criterion f w V xs))))).close

theorem source_packetStructureRootAllActualOutcomesNormalized {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootAllActualOutcomesNormalizedSentence f xs w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r) := .hyp (Or.inl rfl)
  exact PacketStructureRootEquation.outcomes_iff hZ f w V r xs h0 h1

theorem packetStructureRootAllActualOutcomesNormalized_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootAllActualOutcomesNormalizedSentence f xs w V r)) := TheoryTransport.sentence (source_packetStructureRootAllActualOutcomesNormalized f xs w V r)

theorem native_packetStructureRootAllActualOutcomesNormalized {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootAllActualOutcomesNormalizedSentence f xs w V r)) := ZFReplay.replay (packetStructureRootAllActualOutcomesNormalized_kernel_certificate f xs w V r)

def packetStructureRootCanonicalEntryActualAcceptanceIffSentence {m} (k tag : Nat) (xs : Fin k → Fin m) (w V : Fin m) : Source.Sentence := ((PacketTraceCore.value w V).imp (((PacketStructureSyntax.entry k tag w V xs).iff (PacketStructureAcceptedSyntax.accepted k tag w xs)))).close

theorem source_packetStructureRootCanonicalEntryActualAcceptanceIff {m} (k tag : Nat) (xs : Fin k → Fin m) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootCanonicalEntryActualAcceptanceIffSentence k tag xs w V) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketStructureCanonicalCases.entry_iff k tag w V xs h0

theorem packetStructureRootCanonicalEntryActualAcceptanceIff_kernel_certificate {m} (k tag : Nat) (xs : Fin k → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootCanonicalEntryActualAcceptanceIffSentence k tag xs w V)) := TheoryTransport.sentence (source_packetStructureRootCanonicalEntryActualAcceptanceIff k tag xs w V)

theorem native_packetStructureRootCanonicalEntryActualAcceptanceIff {m} (k tag : Nat) (xs : Fin k → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootCanonicalEntryActualAcceptanceIffSentence k tag xs w V)) := ZFReplay.replay (packetStructureRootCanonicalEntryActualAcceptanceIff_kernel_certificate k tag xs w V)

def packetStructureRootCanonicalCriterionActualRecursiveCasesIffSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V : Fin m) : Source.Sentence := ((PacketTraceCore.value w V).imp (((PacketStructureRootSyntax.criterion f w V xs).iff (PacketStructureAcceptedSyntax.criterion f w xs)))).close

theorem source_packetStructureRootCanonicalCriterionActualRecursiveCasesIff {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootCanonicalCriterionActualRecursiveCasesIffSentence f xs w V) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketStructureCanonicalCases.criterion_iff f w V xs h0

theorem packetStructureRootCanonicalCriterionActualRecursiveCasesIff_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootCanonicalCriterionActualRecursiveCasesIffSentence f xs w V)) := TheoryTransport.sentence (source_packetStructureRootCanonicalCriterionActualRecursiveCasesIff f xs w V)

theorem native_packetStructureRootCanonicalCriterionActualRecursiveCasesIff {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootCanonicalCriterionActualRecursiveCasesIffSentence f xs w V)) := ZFReplay.replay (packetStructureRootCanonicalCriterionActualRecursiveCasesIff_kernel_certificate f xs w V)

def packetStructureRootConditionNormalizedForwardSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp ((PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r).imp ((PacketTraceSyntax.condition w r).imp ((PacketStructureRootSyntax.criterion f w V xs)))))).close

theorem source_packetStructureRootConditionNormalizedForward {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootConditionNormalizedForwardSentence f xs w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceSyntax.condition w r) (Context.add (PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r) (Context.add (PacketTraceCore.value w V) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketTraceSyntax.condition w r) := .hyp (Or.inl rfl)
  exact PacketStructureRootEquation.condition_forward hZ f w V r xs h0 h1 h2 h3

theorem packetStructureRootConditionNormalizedForward_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootConditionNormalizedForwardSentence f xs w V r)) := TheoryTransport.sentence (source_packetStructureRootConditionNormalizedForward f xs w V r)

theorem native_packetStructureRootConditionNormalizedForward {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootConditionNormalizedForwardSentence f xs w V r)) := ZFReplay.replay (packetStructureRootConditionNormalizedForward_kernel_certificate f xs w V r)

def packetStructureRootActualRecursiveCasesWithoutCanonicalSetSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r).imp ((PacketTraceSyntax.condition w r).imp ((PacketStructureAcceptedSyntax.criterion f w xs))))).close

theorem source_packetStructureRootActualRecursiveCasesWithoutCanonicalSet {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootActualRecursiveCasesWithoutCanonicalSetSentence f xs w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceSyntax.condition w r) (Context.add (PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTraceSyntax.condition w r) := .hyp (Or.inl rfl)
  exact PacketStructureAcceptedForward.root_forward hZ f w r xs h0 h1 h2

theorem packetStructureRootActualRecursiveCasesWithoutCanonicalSet_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootActualRecursiveCasesWithoutCanonicalSetSentence f xs w r)) := TheoryTransport.sentence (source_packetStructureRootActualRecursiveCasesWithoutCanonicalSet f xs w r)

theorem native_packetStructureRootActualRecursiveCasesWithoutCanonicalSet {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootActualRecursiveCasesWithoutCanonicalSetSentence f xs w r)) := ZFReplay.replay (packetStructureRootActualRecursiveCasesWithoutCanonicalSet_kernel_certificate f xs w r)

def packetStructureRootActualAcceptedRecursiveCasesOnlyOmegaSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureAcceptedSyntax.accepted (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs).imp ((PacketStructureAcceptedSyntax.criterion f w xs)))).close

theorem source_packetStructureRootActualAcceptedRecursiveCasesOnlyOmega {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootActualAcceptedRecursiveCasesOnlyOmegaSentence f xs w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureAcceptedSyntax.accepted (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureAcceptedSyntax.accepted (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs) := .hyp (Or.inl rfl)
  exact PacketStructureAcceptedForward.accepted_forward hZ f w xs h0 h1

theorem packetStructureRootActualAcceptedRecursiveCasesOnlyOmega_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootActualAcceptedRecursiveCasesOnlyOmegaSentence f xs w)) := TheoryTransport.sentence (source_packetStructureRootActualAcceptedRecursiveCasesOnlyOmega f xs w)

theorem native_packetStructureRootActualAcceptedRecursiveCasesOnlyOmega {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootActualAcceptedRecursiveCasesOnlyOmegaSentence f xs w)) := ZFReplay.replay (packetStructureRootActualAcceptedRecursiveCasesOnlyOmega_kernel_certificate f xs w)

def packetStructureRootActualAcceptedAllFieldsNaturalSentence {m} (k tag : Nat) (xs : Fin k → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureAcceptedSyntax.accepted k tag w xs).imp ((HornExprSyntax.environmentNat k w xs)))).close

theorem source_packetStructureRootActualAcceptedAllFieldsNatural {m} (k tag : Nat) (xs : Fin k → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootActualAcceptedAllFieldsNaturalSentence k tag xs w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureAcceptedSyntax.accepted k tag w xs) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureAcceptedSyntax.accepted k tag w xs) := .hyp (Or.inl rfl)
  exact PacketStructureAcceptedForward.accepted_environment hZ k tag w xs h0 h1

theorem packetStructureRootActualAcceptedAllFieldsNatural_kernel_certificate {m} (k tag : Nat) (xs : Fin k → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootActualAcceptedAllFieldsNaturalSentence k tag xs w)) := TheoryTransport.sentence (source_packetStructureRootActualAcceptedAllFieldsNatural k tag xs w)

theorem native_packetStructureRootActualAcceptedAllFieldsNatural {m} (k tag : Nat) (xs : Fin k → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootActualAcceptedAllFieldsNaturalSentence k tag xs w)) := ZFReplay.replay (packetStructureRootActualAcceptedAllFieldsNatural_kernel_certificate k tag xs w)

def packetStructureRootAllInternalOutcomeFieldNormalizationSentence {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureRootLawSyntax.allRootLaw f w V))).close

theorem source_packetStructureRootAllInternalOutcomeFieldNormalization {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootAllInternalOutcomeFieldNormalizationSentence f w V) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureRootLaws.all_root_law hZ f w V h0

theorem packetStructureRootAllInternalOutcomeFieldNormalization_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootAllInternalOutcomeFieldNormalizationSentence f w V)) := TheoryTransport.sentence (source_packetStructureRootAllInternalOutcomeFieldNormalization f w V)

theorem native_packetStructureRootAllInternalOutcomeFieldNormalization {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootAllInternalOutcomeFieldNormalizationSentence f w V)) := ZFReplay.replay (packetStructureRootAllInternalOutcomeFieldNormalization_kernel_certificate f w V)

def packetStructureRootAllInternalAcceptedRecursionSentence {m} (f : PacketStructureDispatchData.Family) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureRootLawSyntax.allAcceptedLaw f w))).close

theorem source_packetStructureRootAllInternalAcceptedRecursion {m} (f : PacketStructureDispatchData.Family) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootAllInternalAcceptedRecursionSentence f w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureRootLaws.all_accepted_law hZ f w h0

theorem packetStructureRootAllInternalAcceptedRecursion_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootAllInternalAcceptedRecursionSentence f w)) := TheoryTransport.sentence (source_packetStructureRootAllInternalAcceptedRecursion f w)

theorem native_packetStructureRootAllInternalAcceptedRecursion {m} (f : PacketStructureDispatchData.Family) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootAllInternalAcceptedRecursionSentence f w)) := ZFReplay.replay (packetStructureRootAllInternalAcceptedRecursion_kernel_certificate f w)

def packetStructureRootActualTreeForwardSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureAcceptedSyntax.tree w n t a).imp ((PacketStructureAcceptedSyntax.treeCase w n t a)))).close

theorem source_packetStructureRootActualTreeForward {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootActualTreeForwardSentence w n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureAcceptedSyntax.tree w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureAcceptedSyntax.tree w n t a) := .hyp (Or.inl rfl)
  exact PacketStructureRootLaws.tree_forward hZ w n t a h0 h1

theorem packetStructureRootActualTreeForward_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootActualTreeForwardSentence w n t a)) := TheoryTransport.sentence (source_packetStructureRootActualTreeForward w n t a)

theorem native_packetStructureRootActualTreeForward {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootActualTreeForwardSentence w n t a)) := ZFReplay.replay (packetStructureRootActualTreeForward_kernel_certificate w n t a)

def packetStructureRootActualForestForwardSentence {m} (w n l t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureAcceptedSyntax.forest w n l t a).imp (((PacketStructureRootSyntax.nilCase n l t a).disj (PacketStructureAcceptedSyntax.consCase w n l t a))))).close

theorem source_packetStructureRootActualForestForward {m} (w n l t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootActualForestForwardSentence w n l t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureAcceptedSyntax.forest w n l t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureAcceptedSyntax.forest w n l t a) := .hyp (Or.inl rfl)
  exact PacketStructureRootLaws.forest_forward hZ w n l t a h0 h1

theorem packetStructureRootActualForestForward_kernel_certificate {m} (w n l t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootActualForestForwardSentence w n l t a)) := TheoryTransport.sentence (source_packetStructureRootActualForestForward w n l t a)

theorem native_packetStructureRootActualForestForward {m} (w n l t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootActualForestForwardSentence w n l t a)) := ZFReplay.replay (packetStructureRootActualForestForward_kernel_certificate w n l t a)

def packetStructureRootActualPacketForwardSentence {m} (w a n : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureAcceptedSyntax.packet w a n).imp ((PacketStructureAcceptedSyntax.packetCase w a n)))).close

theorem source_packetStructureRootActualPacketForward {m} (w a n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootActualPacketForwardSentence w a n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureAcceptedSyntax.packet w a n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureAcceptedSyntax.packet w a n) := .hyp (Or.inl rfl)
  exact PacketStructureRootLaws.packet_forward hZ w a n h0 h1

theorem packetStructureRootActualPacketForward_kernel_certificate {m} (w a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootActualPacketForwardSentence w a n)) := TheoryTransport.sentence (source_packetStructureRootActualPacketForward w a n)

theorem native_packetStructureRootActualPacketForward {m} (w a n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootActualPacketForwardSentence w a n)) := ZFReplay.replay (packetStructureRootActualPacketForward_kernel_certificate w a n)

def packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureRootLawSyntax.allSystem w))).close

theorem source_packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureRootLaws.all_system hZ w h0

theorem packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmega w)

theorem native_packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmegaSentence w)) := ZFReplay.replay (packetStructureRootAllThreeAcceptedRecursionLawsOnlyOmega_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketStructureRoot
