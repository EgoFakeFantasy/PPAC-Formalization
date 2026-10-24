import PPAC.Migration.Internal.PacketStructureSystem

/-! Original structural matrices, exact bounded applications and forward root unfolding for every internal candidate; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketStructure
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetStructureTreeExactMatrixSentence {m} (env : Fin 7 → Fin m) (w V r n : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp ((StructuralNodeSyntax.raw w (env 0) (env 1) n).imp (((HornRuleSyntax.matrix PacketStructureRuleData.treeRule w r V env).iff (PacketStructureSyntax.treeAt w V r n env)))))).close

theorem source_packetStructureTreeExactMatrix {m} (env : Fin 7 → Fin m) (w V r n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTreeExactMatrixSentence env w V r n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w (env 0) (env 1) n) (Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (StructuralNodeSyntax.raw w (env 0) (env 1) n) := .hyp (Or.inl rfl)
  exact PacketStructureMatrix.tree_at hZ w V r n env h0 h1 h2

theorem packetStructureTreeExactMatrix_kernel_certificate {m} (env : Fin 7 → Fin m) (w V r n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTreeExactMatrixSentence env w V r n)) := TheoryTransport.sentence (source_packetStructureTreeExactMatrix env w V r n)

theorem native_packetStructureTreeExactMatrix {m} (env : Fin 7 → Fin m) (w V r n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTreeExactMatrixSentence env w V r n)) := ZFReplay.replay (packetStructureTreeExactMatrix_kernel_certificate env w V r n)

def packetStructureForestNilExactMatrixSentence {m} (env : Fin 1 → Fin m) (w V r z e : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((empty z).imp ((successor e z).imp (((HornRuleSyntax.matrix PacketStructureRuleData.nilRule w r V env).iff (PacketStructureSyntax.nilAt w r z e env))))))).close

theorem source_packetStructureForestNilExactMatrix {m} (env : Fin 1 → Fin m) (w V r z e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureForestNilExactMatrixSentence env w V r z e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor e z) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor e z) := .hyp (Or.inl rfl)
  exact PacketStructureMatrix.nil_at hZ w r z e env V h0 h1 h2 h3

theorem packetStructureForestNilExactMatrix_kernel_certificate {m} (env : Fin 1 → Fin m) (w V r z e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureForestNilExactMatrixSentence env w V r z e)) := TheoryTransport.sentence (source_packetStructureForestNilExactMatrix env w V r z e)

theorem native_packetStructureForestNilExactMatrix {m} (env : Fin 1 → Fin m) (w V r z e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureForestNilExactMatrixSentence env w V r z e)) := ZFReplay.replay (packetStructureForestNilExactMatrix_kernel_certificate env w V r z e)

def packetStructureForestConsExactMatrixSentence {m} (env : Fin 6 → Fin m) (w V r n s : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((StructuralListSyntax.consCode w (env 0) (env 1) n).imp ((successor s (env 2)).imp (((HornRuleSyntax.matrix PacketStructureRuleData.consRule w r V env).iff (PacketStructureSyntax.consAt w V r n s env))))))).close

theorem source_packetStructureForestConsExactMatrix {m} (env : Fin 6 → Fin m) (w V r n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureForestConsExactMatrixSentence env w V r n s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor s (env 2)) (Context.add (StructuralListSyntax.consCode w (env 0) (env 1) n) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (StructuralListSyntax.consCode w (env 0) (env 1) n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor s (env 2)) := .hyp (Or.inl rfl)
  exact PacketStructureMatrix.cons_at hZ w V r n s env h0 h1 h2 h3

theorem packetStructureForestConsExactMatrix_kernel_certificate {m} (env : Fin 6 → Fin m) (w V r n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureForestConsExactMatrixSentence env w V r n s)) := TheoryTransport.sentence (source_packetStructureForestConsExactMatrix env w V r n s)

theorem native_packetStructureForestConsExactMatrix {m} (env : Fin 6 → Fin m) (w V r n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureForestConsExactMatrixSentence env w V r n s)) := ZFReplay.replay (packetStructureForestConsExactMatrix_kernel_certificate env w V r n s)

def packetStructurePacketExactMatrixSentence {m} (env : Fin 3 → Fin m) (w V r e : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral 1 e).imp (((HornRuleSyntax.matrix PacketStructureRuleData.packetRule w r V env).iff (PacketStructureSyntax.packetAt w V r e env)))))).close

theorem source_packetStructurePacketExactMatrix {m} (env : Fin 3 → Fin m) (w V r e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructurePacketExactMatrixSentence env w V r e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 e) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 e) := .hyp (Or.inl rfl)
  exact PacketStructureMatrix.packet_at hZ w V r e env h0 h1 h2

theorem packetStructurePacketExactMatrix_kernel_certificate {m} (env : Fin 3 → Fin m) (w V r e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructurePacketExactMatrixSentence env w V r e)) := TheoryTransport.sentence (source_packetStructurePacketExactMatrix env w V r e)

theorem native_packetStructurePacketExactMatrix {m} (env : Fin 3 → Fin m) (w V r e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructurePacketExactMatrixSentence env w V r e)) := ZFReplay.replay (packetStructurePacketExactMatrix_kernel_certificate env w V r e)

def packetStructureAllFourCompleteLocalMatricesSentence {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat (PacketStructureApplicationSyntax.rule b).arity w env).imp (((HornRuleSyntax.matrix (PacketStructureApplicationSyntax.rule b) w r V env).iff (PacketStructureApplicationSyntax.localCase b w V r env))))).close

theorem source_packetStructureAllFourCompleteLocalMatrices {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureAllFourCompleteLocalMatricesSentence b env w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat (PacketStructureApplicationSyntax.rule b).arity w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat (PacketStructureApplicationSyntax.rule b).arity w env) := .hyp (Or.inl rfl)
  exact PacketStructureApplication.local_iff hZ b w V r env h0 h1

theorem packetStructureAllFourCompleteLocalMatrices_kernel_certificate {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureAllFourCompleteLocalMatricesSentence b env w V r)) := TheoryTransport.sentence (source_packetStructureAllFourCompleteLocalMatrices b env w V r)

theorem native_packetStructureAllFourCompleteLocalMatrices {m} (b : PacketStructureApplicationSyntax.Branch) (env : Fin (PacketStructureApplicationSyntax.rule b).arity → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureAllFourCompleteLocalMatricesSentence b env w V r)) := ZFReplay.replay (packetStructureAllFourCompleteLocalMatrices_kernel_certificate b env w V r)

def packetStructureOriginalBoundedApplicationsIffSentence {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : Source.Sentence := ((omega w).imp (((HornApplicationSyntax.application (PacketStructureApplicationSyntax.rule b) w r V).iff (PacketStructureApplicationSyntax.boundedOutcome b w V r)))).close

theorem source_packetStructureOriginalBoundedApplicationsIff {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureOriginalBoundedApplicationsIffSentence b w V r) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureApplication.bounded_iff hZ b w V r h0

theorem packetStructureOriginalBoundedApplicationsIff_kernel_certificate {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureOriginalBoundedApplicationsIffSentence b w V r)) := TheoryTransport.sentence (source_packetStructureOriginalBoundedApplicationsIff b w V r)

theorem native_packetStructureOriginalBoundedApplicationsIff {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureOriginalBoundedApplicationsIffSentence b w V r)) := ZFReplay.replay (packetStructureOriginalBoundedApplicationsIff_kernel_certificate b w V r)

def packetStructureOriginalApplicationForwardSentence {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((HornApplicationSyntax.application (PacketStructureApplicationSyntax.rule b) w r V).imp ((PacketStructureApplicationSyntax.outcome b w V r)))).close

theorem source_packetStructureOriginalApplicationForward {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureOriginalApplicationForwardSentence b w V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application (PacketStructureApplicationSyntax.rule b) w r V) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornApplicationSyntax.application (PacketStructureApplicationSyntax.rule b) w r V) := .hyp (Or.inl rfl)
  exact PacketStructureApplication.forward hZ b w V r h0 h1

theorem packetStructureOriginalApplicationForward_kernel_certificate {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureOriginalApplicationForwardSentence b w V r)) := TheoryTransport.sentence (source_packetStructureOriginalApplicationForward b w V r)

theorem native_packetStructureOriginalApplicationForward {m} (b : PacketStructureApplicationSyntax.Branch) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureOriginalApplicationForwardSentence b w V r)) := ZFReplay.replay (packetStructureOriginalApplicationForward_kernel_certificate b w V r)

def packetStructureOriginalThreeTagDispatchSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r).imp (((PacketTraceSyntax.step w r V).iff (PacketStructureDispatch.applications f w V r))))).close

theorem source_packetStructureOriginalThreeTagDispatch {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureOriginalThreeTagDispatchSentence f xs w V r) := by
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
  exact PacketStructureDispatch.step_iff_applications hZ f w V r xs h0 h1

theorem packetStructureOriginalThreeTagDispatch_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureOriginalThreeTagDispatchSentence f xs w V r)) := TheoryTransport.sentence (source_packetStructureOriginalThreeTagDispatch f xs w V r)

theorem native_packetStructureOriginalThreeTagDispatch {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureOriginalThreeTagDispatchSentence f xs w V r)) := ZFReplay.replay (packetStructureOriginalThreeTagDispatch_kernel_certificate f xs w V r)

def packetStructureActualConditionBoundedIffSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp ((PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r).imp (((PacketTraceSyntax.condition w r).iff (PacketStructureDispatch.results true f w V r)))))).close

theorem source_packetStructureActualConditionBoundedIff {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureActualConditionBoundedIffSentence f xs w V r) := by
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
  exact PacketStructureDispatch.condition_iff_bounded hZ f w V r xs h0 h1 h2

theorem packetStructureActualConditionBoundedIff_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureActualConditionBoundedIffSentence f xs w V r)) := TheoryTransport.sentence (source_packetStructureActualConditionBoundedIff f xs w V r)

theorem native_packetStructureActualConditionBoundedIff {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureActualConditionBoundedIffSentence f xs w V r)) := ZFReplay.replay (packetStructureActualConditionBoundedIff_kernel_certificate f xs w V r)

def packetStructureActualConditionForwardSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp ((PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r).imp ((PacketTraceSyntax.condition w r).imp ((PacketStructureDispatch.results false f w V r)))))).close

theorem source_packetStructureActualConditionForward {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureActualConditionForwardSentence f xs w V r) := by
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
  exact PacketStructureDispatch.condition_forward hZ f w V r xs h0 h1 h2 h3

theorem packetStructureActualConditionForward_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureActualConditionForwardSentence f xs w V r)) := TheoryTransport.sentence (source_packetStructureActualConditionForward f xs w V r)

theorem native_packetStructureActualConditionForward {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureActualConditionForwardSentence f xs w V r)) := ZFReplay.replay (packetStructureActualConditionForward_kernel_certificate f xs w V r)

def packetStructureActualRootLawSentence {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp ((PacketStructureSyntax.row (PacketStructureDispatchData.width f) (PacketStructureDispatchData.tag f) w xs r).imp ((PacketStructureSystemSyntax.rootLaw f w V r))))).close

theorem source_packetStructureActualRootLaw {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureActualRootLawSentence f xs w V r) := by
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
  exact PacketStructureSystem.root_law hZ f w V r xs h0 h1 h2

theorem packetStructureActualRootLaw_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureActualRootLawSentence f xs w V r)) := TheoryTransport.sentence (source_packetStructureActualRootLaw f xs w V r)

theorem native_packetStructureActualRootLaw {m} (f : PacketStructureDispatchData.Family) (xs : Fin (PacketStructureDispatchData.width f) → Fin m) (w V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureActualRootLawSentence f xs w V r)) := ZFReplay.replay (packetStructureActualRootLaw_kernel_certificate f xs w V r)

def packetStructureAllInternalRootLawsSentence {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : Source.Sentence := ((omega w).imp ((PacketTraceCore.value w V).imp ((PacketStructureSystemSyntax.allLaw f w V)))).close

theorem source_packetStructureAllInternalRootLaws {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureAllInternalRootLawsSentence f w V) := by
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
  exact PacketStructureSystem.all_law hZ f w V h0 h1

theorem packetStructureAllInternalRootLaws_kernel_certificate {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureAllInternalRootLawsSentence f w V)) := TheoryTransport.sentence (source_packetStructureAllInternalRootLaws f w V)

theorem native_packetStructureAllInternalRootLaws {m} (f : PacketStructureDispatchData.Family) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureAllInternalRootLawsSentence f w V)) := ZFReplay.replay (packetStructureAllInternalRootLaws_kernel_certificate f w V)

def packetStructureActualSystemExistsOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureSystemSyntax.existsSystem w))).close

theorem source_packetStructureActualSystemExistsOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureActualSystemExistsOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureSystem.exists_system hZ w h0

theorem packetStructureActualSystemExistsOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureActualSystemExistsOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetStructureActualSystemExistsOnlyOmega w)

theorem native_packetStructureActualSystemExistsOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureActualSystemExistsOnlyOmegaSentence w)) := ZFReplay.replay (packetStructureActualSystemExistsOnlyOmega_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketStructure
