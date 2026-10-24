import PPAC.Migration.Internal.PacketTraceCore

/-! Actual ten-rule Packet relational trace, all-internal unfolding and affine root dispatch; original Basic AST translation and complete arithmetic/byte bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketClosedTrace
open Source SourceAlgebra SourceLogic OmegaSyntax

def closedTraceMemberHasActualStepSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r : Fin m) : Source.Sentence := ((HornClosedTraceSyntax.closed rules w R).imp ((Formula.mem r R).imp ((HornStepSyntax.step rules w r R)))).close

theorem source_closedTraceMemberHasActualStep {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceMemberHasActualStepSentence rules w R r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem r R) (Context.add (HornClosedTraceSyntax.closed rules w R) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (HornClosedTraceSyntax.closed rules w R) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem r R) := .hyp (Or.inl rfl)
  exact HornClosedTraceSyntax.closed_at rules w R r h0 h1

theorem closedTraceMemberHasActualStep_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceMemberHasActualStepSentence rules w R r)) := TheoryTransport.sentence (source_closedTraceMemberHasActualStep rules w R r)

theorem native_closedTraceMemberHasActualStep {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceMemberHasActualStepSentence rules w R r)) := ZFReplay.replay (closedTraceMemberHasActualStep_kernel_certificate rules w R r)

def closedTraceInsertPreservesClosureSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r S : Fin m) : Source.Sentence := ((HornClosedTraceSyntax.closed rules w R).imp ((HornStepSyntax.step rules w r R).imp ((InsertSyntax.insert S R r).imp ((HornClosedTraceSyntax.closed rules w S))))).close

theorem source_closedTraceInsertPreservesClosure {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceInsertPreservesClosureSentence rules w R r S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (InsertSyntax.insert S R r) (Context.add (HornStepSyntax.step rules w r R) (Context.add (HornClosedTraceSyntax.closed rules w R) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (HornClosedTraceSyntax.closed rules w R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornStepSyntax.step rules w r R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (InsertSyntax.insert S R r) := .hyp (Or.inl rfl)
  exact HornClosedTraceExtension.closed rules w R r S h0 h1 h2

theorem closedTraceInsertPreservesClosure_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceInsertPreservesClosureSentence rules w R r S)) := TheoryTransport.sentence (source_closedTraceInsertPreservesClosure rules w R r S)

theorem native_closedTraceInsertPreservesClosure {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceInsertPreservesClosureSentence rules w R r S)) := ZFReplay.replay (closedTraceInsertPreservesClosure_kernel_certificate rules w R r S)

def closedTraceInsertAcceptsActualRootSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r : Fin m) : Source.Sentence := ((RestrictionSyntax.subset R w).imp ((Formula.mem r w).imp ((HornClosedTraceSyntax.closed rules w R).imp ((HornStepSyntax.step rules w r R).imp ((HornClosedTraceSyntax.condition rules w r)))))).close

theorem source_closedTraceInsertAcceptsActualRoot {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceInsertAcceptsActualRootSentence rules w R r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornStepSyntax.step rules w r R) (Context.add (HornClosedTraceSyntax.closed rules w R) (Context.add (Formula.mem r w) (Context.add (RestrictionSyntax.subset R w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornClosedTraceSyntax.closed rules w R) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornStepSyntax.step rules w r R) := .hyp (Or.inl rfl)
  exact HornClosedTraceExtension.condition rules hZ w R r h0 h1 h2 h3

theorem closedTraceInsertAcceptsActualRoot_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceInsertAcceptsActualRootSentence rules w R r)) := TheoryTransport.sentence (source_closedTraceInsertAcceptsActualRoot rules w R r)

theorem native_closedTraceInsertAcceptsActualRoot {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w R r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceInsertAcceptsActualRootSentence rules w R r)) := ZFReplay.replay (closedTraceInsertAcceptsActualRoot_kernel_certificate rules w R r)

def closedTraceAcceptedRootSetExistsSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w : Fin m) : Source.Sentence := ((HornClosedTraceValueSyntax.existsValue rules w)).close

theorem source_closedTraceAcceptedRootSetExists {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceAcceptedRootSetExistsSentence rules w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact HornClosedTraceValue.exists_value rules hZ w

theorem closedTraceAcceptedRootSetExists_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceAcceptedRootSetExistsSentence rules w)) := TheoryTransport.sentence (source_closedTraceAcceptedRootSetExists rules w)

theorem native_closedTraceAcceptedRootSetExists {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceAcceptedRootSetExistsSentence rules w)) := ZFReplay.replay (closedTraceAcceptedRootSetExists_kernel_certificate rules w)

def closedTraceAcceptedRootMembershipIffSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V r : Fin m) : Source.Sentence := ((HornClosedTraceValueSyntax.value rules w V).imp (((Formula.mem r V).iff (HornClosedTraceSyntax.condition rules w r)))).close

theorem source_closedTraceAcceptedRootMembershipIff {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceAcceptedRootMembershipIffSentence rules w V r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (HornClosedTraceValueSyntax.value rules w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (HornClosedTraceValueSyntax.value rules w V) := .hyp (Or.inl rfl)
  exact HornClosedTraceValue.member_iff rules w V r h0

theorem closedTraceAcceptedRootMembershipIff_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceAcceptedRootMembershipIffSentence rules w V r)) := TheoryTransport.sentence (source_closedTraceAcceptedRootMembershipIff rules w V r)

theorem native_closedTraceAcceptedRootMembershipIff {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceAcceptedRootMembershipIffSentence rules w V r)) := ZFReplay.replay (closedTraceAcceptedRootMembershipIff_kernel_certificate rules w V r)

def closedTraceContainsEveryInternalSubtraceSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V R : Fin m) : Source.Sentence := ((HornClosedTraceValueSyntax.value rules w V).imp ((RestrictionSyntax.subset R w).imp ((HornClosedTraceSyntax.closed rules w R).imp ((RestrictionSyntax.subset R V))))).close

theorem source_closedTraceContainsEveryInternalSubtrace {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceContainsEveryInternalSubtraceSentence rules w V R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornClosedTraceSyntax.closed rules w R) (Context.add (RestrictionSyntax.subset R w) (Context.add (HornClosedTraceValueSyntax.value rules w V) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (HornClosedTraceValueSyntax.value rules w V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornClosedTraceSyntax.closed rules w R) := .hyp (Or.inl rfl)
  exact HornClosedTraceValue.subtrace_included rules w V R h0 h1 h2

theorem closedTraceContainsEveryInternalSubtrace_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceContainsEveryInternalSubtraceSentence rules w V R)) := TheoryTransport.sentence (source_closedTraceContainsEveryInternalSubtrace rules w V R)

theorem native_closedTraceContainsEveryInternalSubtrace {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceContainsEveryInternalSubtraceSentence rules w V R)) := ZFReplay.replay (closedTraceContainsEveryInternalSubtrace_kernel_certificate rules w V R)

def closedTraceAcceptedRootSetClosedSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V : Fin m) : Source.Sentence := ((HornClosedTraceValueSyntax.value rules w V).imp ((HornClosedTraceSyntax.closed rules w V))).close

theorem source_closedTraceAcceptedRootSetClosed {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceAcceptedRootSetClosedSentence rules w V) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (HornClosedTraceValueSyntax.value rules w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (HornClosedTraceValueSyntax.value rules w V) := .hyp (Or.inl rfl)
  exact HornClosedTraceValueClosed.closed rules w V h0

theorem closedTraceAcceptedRootSetClosed_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceAcceptedRootSetClosedSentence rules w V)) := TheoryTransport.sentence (source_closedTraceAcceptedRootSetClosed rules w V)

theorem native_closedTraceAcceptedRootSetClosed {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceAcceptedRootSetClosedSentence rules w V)) := ZFReplay.replay (closedTraceAcceptedRootSetClosed_kernel_certificate rules w V)

def closedTraceAllCandidateUnfoldIffSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((HornClosedTraceValueSyntax.value rules w V).imp (((HornClosedTraceSyntax.condition rules w r).iff (HornStepSyntax.step rules w r V))))).close

theorem source_closedTraceAllCandidateUnfoldIff {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceAllCandidateUnfoldIffSentence rules w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornClosedTraceValueSyntax.value rules w V) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornClosedTraceValueSyntax.value rules w V) := .hyp (Or.inl rfl)
  exact HornClosedTraceProperties.unfold_iff rules hZ w V r h0 h1

theorem closedTraceAllCandidateUnfoldIff_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceAllCandidateUnfoldIffSentence rules w V r)) := TheoryTransport.sentence (source_closedTraceAllCandidateUnfoldIff rules w V r)

theorem native_closedTraceAllCandidateUnfoldIff {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceAllCandidateUnfoldIffSentence rules w V r)) := ZFReplay.replay (closedTraceAllCandidateUnfoldIff_kernel_certificate rules w V r)

def closedTraceAllCandidateSystemExistsSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornClosedTraceSystemSyntax.existsSystem rules w))).close

theorem source_closedTraceAllCandidateSystemExists {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceAllCandidateSystemExistsSentence rules w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact HornClosedTraceProperties.exists_system rules hZ w h0

theorem closedTraceAllCandidateSystemExists_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceAllCandidateSystemExistsSentence rules w)) := TheoryTransport.sentence (source_closedTraceAllCandidateSystemExists rules w)

theorem native_closedTraceAllCandidateSystemExists {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceAllCandidateSystemExistsSentence rules w)) := ZFReplay.replay (closedTraceAllCandidateSystemExists_kernel_certificate rules w)

def closedTraceRejectNonNaturalRootSentence {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w r : Fin m) : Source.Sentence := (((Formula.mem r w).neg).imp (((HornClosedTraceSyntax.condition rules w r).neg))).close

theorem source_closedTraceRejectNonNaturalRoot {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (closedTraceRejectNonNaturalRootSentence rules w r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem r w).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((Formula.mem r w).neg) := .hyp (Or.inl rfl)
  exact HornClosedTraceProperties.reject_non_natural rules w r h0

theorem closedTraceRejectNonNaturalRoot_kernel_certificate {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (closedTraceRejectNonNaturalRootSentence rules w r)) := TheoryTransport.sentence (source_closedTraceRejectNonNaturalRoot rules w r)

theorem native_closedTraceRejectNonNaturalRoot {m} (rules : List YesMetaZFC.Automation.ObjectHorn.Rule) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (closedTraceRejectNonNaturalRootSentence rules w r)) := ZFReplay.replay (closedTraceRejectNonNaturalRoot_kernel_certificate rules w r)

def packetActualTenRuleAcceptedRootSetExistsSentence {m} (w : Fin m) : Source.Sentence := ((HornClosedTraceValueSyntax.existsValue YesMetaZFC.Automation.ObjectPacket.rules w)).close

theorem source_packetActualTenRuleAcceptedRootSetExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetActualTenRuleAcceptedRootSetExistsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact PacketTraceCore.exists_value hZ w

theorem packetActualTenRuleAcceptedRootSetExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetActualTenRuleAcceptedRootSetExistsSentence w)) := TheoryTransport.sentence (source_packetActualTenRuleAcceptedRootSetExists w)

theorem native_packetActualTenRuleAcceptedRootSetExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetActualTenRuleAcceptedRootSetExistsSentence w)) := ZFReplay.replay (packetActualTenRuleAcceptedRootSetExists_kernel_certificate w)

def packetActualTenRuleAcceptedRootSetClosedSentence {m} (w V : Fin m) : Source.Sentence := ((PacketTraceCore.value w V).imp ((PacketTraceSyntax.closed w V))).close

theorem source_packetActualTenRuleAcceptedRootSetClosed {m} (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetActualTenRuleAcceptedRootSetClosedSentence w V) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketTraceCore.closed w V h0

theorem packetActualTenRuleAcceptedRootSetClosed_kernel_certificate {m} (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetActualTenRuleAcceptedRootSetClosedSentence w V)) := TheoryTransport.sentence (source_packetActualTenRuleAcceptedRootSetClosed w V)

theorem native_packetActualTenRuleAcceptedRootSetClosed {m} (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetActualTenRuleAcceptedRootSetClosedSentence w V)) := ZFReplay.replay (packetActualTenRuleAcceptedRootSetClosed_kernel_certificate w V)

def packetActualTenRuleConditionUnfoldIffSentence {m} (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp (((PacketTraceSyntax.condition w r).iff (PacketTraceSyntax.step w r V))))).close

theorem source_packetActualTenRuleConditionUnfoldIff {m} (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetActualTenRuleConditionUnfoldIffSentence w V r) := by
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
  exact PacketTraceCore.unfold_iff hZ w V r h0 h1

theorem packetActualTenRuleConditionUnfoldIff_kernel_certificate {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetActualTenRuleConditionUnfoldIffSentence w V r)) := TheoryTransport.sentence (source_packetActualTenRuleConditionUnfoldIff w V r)

theorem native_packetActualTenRuleConditionUnfoldIff {m} (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetActualTenRuleConditionUnfoldIffSentence w V r)) := ZFReplay.replay (packetActualTenRuleConditionUnfoldIff_kernel_certificate w V r)

def packetActualTenRuleTraceSystemExistsSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((HornClosedTraceSystemSyntax.existsSystem YesMetaZFC.Automation.ObjectPacket.rules w))).close

theorem source_packetActualTenRuleTraceSystemExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetActualTenRuleTraceSystemExistsSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTraceCore.exists_system hZ w h0

theorem packetActualTenRuleTraceSystemExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetActualTenRuleTraceSystemExistsSentence w)) := TheoryTransport.sentence (source_packetActualTenRuleTraceSystemExists w)

theorem native_packetActualTenRuleTraceSystemExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetActualTenRuleTraceSystemExistsSentence w)) := ZFReplay.replay (packetActualTenRuleTraceSystemExists_kernel_certificate w)

def packetAffineForeignRuleRejectedSentence {m} (wide : Bool) (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (_hk : rule ∈ PacketAffineDispatchData.others wide) (w d t n r R : Fin m) : Source.Sentence := ((omega w).imp ((PacketHornAffineSyntax.row wide w d t n r).imp ((HornApplicationSyntax.application rule w r R).imp ((Formula.bot))))).close

theorem source_packetAffineForeignRuleRejected {m} (wide : Bool) (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hk : rule ∈ PacketAffineDispatchData.others wide) (w d t n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineForeignRuleRejectedSentence wide rule hk w d t n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application rule w r R) (Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornApplicationSyntax.application rule w r R) := .hyp (Or.inl rfl)
  exact PacketAffineDispatch.application_contradiction hZ wide rule hk w d t n r R h0 h1 h2

theorem packetAffineForeignRuleRejected_kernel_certificate {m} (wide : Bool) (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hk : rule ∈ PacketAffineDispatchData.others wide) (w d t n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineForeignRuleRejectedSentence wide rule hk w d t n r R)) := TheoryTransport.sentence (source_packetAffineForeignRuleRejected wide rule hk w d t n r R)

theorem native_packetAffineForeignRuleRejected {m} (wide : Bool) (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (hk : rule ∈ PacketAffineDispatchData.others wide) (w d t n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineForeignRuleRejectedSentence wide rule hk w d t n r R)) := ZFReplay.replay (packetAffineForeignRuleRejected_kernel_certificate wide rule hk w d t n r R)

def packetAffineActualTenRuleDispatchSentence {m} (wide : Bool) (w d t n r R : Fin m) : Source.Sentence := ((omega w).imp ((PacketHornAffineSyntax.row wide w d t n r).imp ((PacketTraceSyntax.step w r R).imp (((HornApplicationSyntax.application (PacketAffineRuleData.baseRule wide) w r R).disj (HornApplicationSyntax.application (PacketAffineRuleData.stepRule wide) w r R)))))).close

theorem source_packetAffineActualTenRuleDispatch {m} (wide : Bool) (w d t n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineActualTenRuleDispatchSentence wide w d t n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceSyntax.step w r R) (Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTraceSyntax.step w r R) := .hyp (Or.inl rfl)
  exact PacketAffineDispatch.dispatch hZ wide w d t n r R h0 h1 h2

theorem packetAffineActualTenRuleDispatch_kernel_certificate {m} (wide : Bool) (w d t n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineActualTenRuleDispatchSentence wide w d t n r R)) := TheoryTransport.sentence (source_packetAffineActualTenRuleDispatch wide w d t n r R)

theorem native_packetAffineActualTenRuleDispatch {m} (wide : Bool) (w d t n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineActualTenRuleDispatchSentence wide w d t n r R)) := ZFReplay.replay (packetAffineActualTenRuleDispatch_kernel_certificate wide w d t n r R)

def packetAffineActualTenRuleStepIffOutcomesSentence {m} (wide : Bool) (w B d t n r R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketHornAffineSyntax.row wide w d t n r).imp (((PacketTraceSyntax.step w r R).iff ((PacketAffineApplicationSyntax.baseOutcome wide w B r).disj (PacketAffineApplicationSyntax.stepOutcome wide w B R r))))))).close

theorem source_packetAffineActualTenRuleStepIffOutcomes {m} (wide : Bool) (w B d t n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineActualTenRuleStepIffOutcomesSentence wide w B d t n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inl rfl)
  exact PacketAffineDispatch.step_iff_outcomes hZ wide w B d t n r R h0 h1 h2

theorem packetAffineActualTenRuleStepIffOutcomes_kernel_certificate {m} (wide : Bool) (w B d t n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineActualTenRuleStepIffOutcomesSentence wide w B d t n r R)) := TheoryTransport.sentence (source_packetAffineActualTenRuleStepIffOutcomes wide w B d t n r R)

theorem native_packetAffineActualTenRuleStepIffOutcomes {m} (wide : Bool) (w B d t n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineActualTenRuleStepIffOutcomesSentence wide w B d t n r R)) := ZFReplay.replay (packetAffineActualTenRuleStepIffOutcomes_kernel_certificate wide w B d t n r R)

def packetAffineConditionIffActualOutcomesSentence {m} (wide : Bool) (w B V d t n r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketTraceCore.value w V).imp ((PacketHornAffineSyntax.row wide w d t n r).imp (((PacketTraceSyntax.condition w r).iff ((PacketAffineApplicationSyntax.baseOutcome wide w B r).disj (PacketAffineApplicationSyntax.stepOutcome wide w B V r)))))))).close

theorem source_packetAffineConditionIffActualOutcomes {m} (wide : Bool) (w B V d t n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineConditionIffActualOutcomesSentence wide w B V d t n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inl rfl)
  exact PacketTraceCore.affine_condition_iff_outcomes hZ wide w B V d t n r h0 h1 h2 h3

theorem packetAffineConditionIffActualOutcomes_kernel_certificate {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineConditionIffActualOutcomesSentence wide w B V d t n r)) := TheoryTransport.sentence (source_packetAffineConditionIffActualOutcomes wide w B V d t n r)

theorem native_packetAffineConditionIffActualOutcomes {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineConditionIffActualOutcomesSentence wide w B V d t n r)) := ZFReplay.replay (packetAffineConditionIffActualOutcomes_kernel_certificate wide w B V d t n r)

def packetAffineBaseConditionAcceptedSentence {m} (wide : Bool) (w B r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineApplicationSyntax.baseOutcome wide w B r).imp ((PacketTraceSyntax.condition w r))))).close

theorem source_packetAffineBaseConditionAccepted {m} (wide : Bool) (w B r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineBaseConditionAcceptedSentence wide w B r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineApplicationSyntax.baseOutcome wide w B r) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineApplicationSyntax.baseOutcome wide w B r) := .hyp (Or.inl rfl)
  exact PacketTraceCore.base_accept hZ wide w B r h0 h1 h2

theorem packetAffineBaseConditionAccepted_kernel_certificate {m} (wide : Bool) (w B r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineBaseConditionAcceptedSentence wide w B r)) := TheoryTransport.sentence (source_packetAffineBaseConditionAccepted wide w B r)

theorem native_packetAffineBaseConditionAccepted {m} (wide : Bool) (w B r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineBaseConditionAcceptedSentence wide w B r)) := ZFReplay.replay (packetAffineBaseConditionAccepted_kernel_certificate wide w B r)

def packetAffineSuccessorConditionAcceptedSentence {m} (wide : Bool) (w B d t a s n q r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketHornAffineSyntax.row wide w d t a q).imp ((PacketTraceSyntax.condition w q).imp ((successor s t).imp ((NaturalAdditionSyntax.sum w a B n).imp ((PacketHornAffineSyntax.row wide w d s n r).imp ((PacketTraceSyntax.condition w r))))))))).close

theorem source_packetAffineSuccessorConditionAccepted {m} (wide : Bool) (w B d t a s n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineSuccessorConditionAcceptedSentence wide w B d t a s n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d s n r) (Context.add (NaturalAdditionSyntax.sum w a B n) (Context.add (successor s t) (Context.add (PacketTraceSyntax.condition w q) (Context.add (PacketHornAffineSyntax.row wide w d t a q) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (PacketHornAffineSyntax.row wide w d t a q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (PacketTraceSyntax.condition w q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (successor s t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (NaturalAdditionSyntax.sum w a B n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketHornAffineSyntax.row wide w d s n r) := .hyp (Or.inl rfl)
  exact PacketTraceCore.step_accept hZ wide w B d t a s n q r h0 h1 h2 h3 h4 h5 h6

theorem packetAffineSuccessorConditionAccepted_kernel_certificate {m} (wide : Bool) (w B d t a s n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineSuccessorConditionAcceptedSentence wide w B d t a s n q r)) := TheoryTransport.sentence (source_packetAffineSuccessorConditionAccepted wide w B d t a s n q r)

theorem native_packetAffineSuccessorConditionAccepted {m} (wide : Bool) (w B d t a s n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineSuccessorConditionAcceptedSentence wide w B d t a s n q r)) := ZFReplay.replay (packetAffineSuccessorConditionAccepted_kernel_certificate wide w B d t a s n q r)

end PPAC.Migration.Internal.ObjectPacketClosedTrace
