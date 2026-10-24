import PPAC.Migration.Internal.PacketStructureTailLaws

/-! Actual tree and forest tail bounds by original joint internal subcode induction, all IH discharged; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketStructureTail
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetStructureTailActualRawPayloadStrictSubcodeSentence {m} (w tag p n l t u v a : Fin m) : Source.Sentence := ((omega w).imp ((StructuralNodeSyntax.raw w tag p n).imp ((PacketStructureAcceptedSyntax.forest w p l t u).imp ((PacketTokenAcceptedSyntax.accepted w tag v a).imp ((Formula.mem p n)))))).close

theorem source_packetStructureTailActualRawPayloadStrictSubcode {m} (w tag p n l t u v a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailActualRawPayloadStrictSubcodeSentence w tag p n l t u v a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w tag v a) (Context.add (PacketStructureAcceptedSyntax.forest w p l t u) (Context.add (StructuralNodeSyntax.raw w tag p n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (StructuralNodeSyntax.raw w tag p n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketStructureAcceptedSyntax.forest w p l t u) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketTokenAcceptedSyntax.accepted w tag v a) := .hyp (Or.inl rfl)
  exact PacketStructureTailChildren.raw_payload hZ w tag p n l t u v a h0 h1 h2 h3

theorem packetStructureTailActualRawPayloadStrictSubcode_kernel_certificate {m} (w tag p n l t u v a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailActualRawPayloadStrictSubcodeSentence w tag p n l t u v a)) := TheoryTransport.sentence (source_packetStructureTailActualRawPayloadStrictSubcode w tag p n l t u v a)

theorem native_packetStructureTailActualRawPayloadStrictSubcode {m} (w tag p n l t u v a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailActualRawPayloadStrictSubcodeSentence w tag p n l t u v a)) := ZFReplay.replay (packetStructureTailActualRawPayloadStrictSubcode_kernel_certificate w tag p n l t u v a)

def packetStructureTailActualConsChildrenStrictSubcodesSentence {m} (w h q n k t u a : Fin m) : Source.Sentence := ((omega w).imp ((StructuralListSyntax.consCode w h q n).imp ((PacketStructureAcceptedSyntax.forest w q k t u).imp ((PacketStructureAcceptedSyntax.tree w h u a).imp (((Formula.mem h n).conj (Formula.mem q n))))))).close

theorem source_packetStructureTailActualConsChildrenStrictSubcodes {m} (w h q n k t u a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailActualConsChildrenStrictSubcodesSentence w h q n k t u a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureAcceptedSyntax.tree w h u a) (Context.add (PacketStructureAcceptedSyntax.forest w q k t u) (Context.add (StructuralListSyntax.consCode w h q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (StructuralListSyntax.consCode w h q n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketStructureAcceptedSyntax.forest w q k t u) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketStructureAcceptedSyntax.tree w h u a) := .hyp (Or.inl rfl)
  exact PacketStructureTailChildren.cons_children hZ w h q n k t u a h0 h1 h2 h3

theorem packetStructureTailActualConsChildrenStrictSubcodes_kernel_certificate {m} (w h q n k t u a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailActualConsChildrenStrictSubcodesSentence w h q n k t u a)) := TheoryTransport.sentence (source_packetStructureTailActualConsChildrenStrictSubcodes w h q n k t u a)

theorem native_packetStructureTailActualConsChildrenStrictSubcodes {m} (w h q n k t u a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailActualConsChildrenStrictSubcodesSentence w h q n k t u a)) := ZFReplay.replay (packetStructureTailActualConsChildrenStrictSubcodes_kernel_certificate w h q n k t u a)

def packetStructureTailTreePointFromJointChildIHSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureTailSyntax.hypothesis w n).imp ((PacketStructureAcceptedSyntax.tree w n t a).imp ((NaturalAdditionBounds.below t a))))).close

theorem source_packetStructureTailTreePointFromJointChildIH {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailTreePointFromJointChildIHSentence w n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureAcceptedSyntax.tree w n t a) (Context.add (PacketStructureTailSyntax.hypothesis w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketStructureTailSyntax.hypothesis w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketStructureAcceptedSyntax.tree w n t a) := .hyp (Or.inl rfl)
  exact PacketStructureTailPoint.tree_point hZ w n t a h0 h1 h2

theorem packetStructureTailTreePointFromJointChildIH_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailTreePointFromJointChildIHSentence w n t a)) := TheoryTransport.sentence (source_packetStructureTailTreePointFromJointChildIH w n t a)

theorem native_packetStructureTailTreePointFromJointChildIH {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailTreePointFromJointChildIHSentence w n t a)) := ZFReplay.replay (packetStructureTailTreePointFromJointChildIH_kernel_certificate w n t a)

def packetStructureTailForestPointFromJointChildIHSentence {m} (w n l t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureTailSyntax.hypothesis w n).imp ((PacketStructureAcceptedSyntax.forest w n l t a).imp ((NaturalAdditionBounds.below t a))))).close

theorem source_packetStructureTailForestPointFromJointChildIH {m} (w n l t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailForestPointFromJointChildIHSentence w n l t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureAcceptedSyntax.forest w n l t a) (Context.add (PacketStructureTailSyntax.hypothesis w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketStructureTailSyntax.hypothesis w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketStructureAcceptedSyntax.forest w n l t a) := .hyp (Or.inl rfl)
  exact PacketStructureTailPoint.forest_point hZ w n l t a h0 h1 h2

theorem packetStructureTailForestPointFromJointChildIH_kernel_certificate {m} (w n l t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailForestPointFromJointChildIHSentence w n l t a)) := TheoryTransport.sentence (source_packetStructureTailForestPointFromJointChildIH w n l t a)

theorem native_packetStructureTailForestPointFromJointChildIH {m} (w n l t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailForestPointFromJointChildIHSentence w n l t a)) := ZFReplay.replay (packetStructureTailForestPointFromJointChildIH_kernel_certificate w n l t a)

def packetStructureTailJointPointSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureTailSyntax.hypothesis w n).imp ((PacketStructureTailSyntax.property w n)))).close

theorem source_packetStructureTailJointPoint {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailJointPointSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketStructureTailSyntax.hypothesis w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketStructureTailSyntax.hypothesis w n) := .hyp (Or.inl rfl)
  exact PacketStructureTailInduction.point hZ w n h0 h1

theorem packetStructureTailJointPoint_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailJointPointSentence w n)) := TheoryTransport.sentence (source_packetStructureTailJointPoint w n)

theorem native_packetStructureTailJointPoint {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailJointPointSentence w n)) := ZFReplay.replay (packetStructureTailJointPoint_kernel_certificate w n)

def packetStructureTailJointObjectProgressiveSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((BoundedInduction.progressive PacketStructureTailSyntax.matrix (fun _ : Fin 1 => w) w))).close

theorem source_packetStructureTailJointObjectProgressive {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailJointObjectProgressiveSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureTailInduction.progressive hZ w h0

theorem packetStructureTailJointObjectProgressive_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailJointObjectProgressiveSentence w)) := TheoryTransport.sentence (source_packetStructureTailJointObjectProgressive w)

theorem native_packetStructureTailJointObjectProgressive {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailJointObjectProgressiveSentence w)) := ZFReplay.replay (packetStructureTailJointObjectProgressive_kernel_certificate w)

def packetStructureTailAllInternalJointIHDischargedSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (PacketStructureTailSyntax.property w.castSucc (Fin.last m)))))).close

theorem source_packetStructureTailAllInternalJointIHDischarged {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailAllInternalJointIHDischargedSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureTailInduction.all_property hZ w h0

theorem packetStructureTailAllInternalJointIHDischarged_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailAllInternalJointIHDischargedSentence w)) := TheoryTransport.sentence (source_packetStructureTailAllInternalJointIHDischarged w)

theorem native_packetStructureTailAllInternalJointIHDischarged {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailAllInternalJointIHDischargedSentence w)) := ZFReplay.replay (packetStructureTailAllInternalJointIHDischarged_kernel_certificate w)

def packetStructureTailActualTreeBelowOutputSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureAcceptedSyntax.tree w n t a).imp ((NaturalAdditionBounds.below t a)))).close

theorem source_packetStructureTailActualTreeBelowOutput {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailActualTreeBelowOutputSentence w n t a) := by
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
  exact PacketStructureTailBounds.tree_tail hZ w n t a h0 h1

theorem packetStructureTailActualTreeBelowOutput_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailActualTreeBelowOutputSentence w n t a)) := TheoryTransport.sentence (source_packetStructureTailActualTreeBelowOutput w n t a)

theorem native_packetStructureTailActualTreeBelowOutput {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailActualTreeBelowOutputSentence w n t a)) := ZFReplay.replay (packetStructureTailActualTreeBelowOutput_kernel_certificate w n t a)

def packetStructureTailActualForestBelowOutputSentence {m} (w n l t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureAcceptedSyntax.forest w n l t a).imp ((NaturalAdditionBounds.below t a)))).close

theorem source_packetStructureTailActualForestBelowOutput {m} (w n l t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailActualForestBelowOutputSentence w n l t a) := by
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
  exact PacketStructureTailBounds.forest_tail hZ w n l t a h0 h1

theorem packetStructureTailActualForestBelowOutput_kernel_certificate {m} (w n l t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailActualForestBelowOutputSentence w n l t a)) := TheoryTransport.sentence (source_packetStructureTailActualForestBelowOutput w n l t a)

theorem native_packetStructureTailActualForestBelowOutput {m} (w n l t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailActualForestBelowOutputSentence w n l t a)) := ZFReplay.replay (packetStructureTailActualForestBelowOutput_kernel_certificate w n l t a)

def packetStructureTailActualTreeContainedSentence {m} (w n t a r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureAcceptedSyntax.tree w n t a).imp ((Formula.mem r w).imp ((NaturalAdditionBounds.below a r).imp ((NaturalAdditionBounds.below t r)))))).close

theorem source_packetStructureTailActualTreeContained {m} (w n t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailActualTreeContainedSentence w n t a r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionBounds.below a r) (Context.add (Formula.mem r w) (Context.add (PacketStructureAcceptedSyntax.tree w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketStructureAcceptedSyntax.tree w n t a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (NaturalAdditionBounds.below a r) := .hyp (Or.inl rfl)
  exact PacketStructureTailBounds.tree_contained hZ w n t a r h0 h1 h2 h3

theorem packetStructureTailActualTreeContained_kernel_certificate {m} (w n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailActualTreeContainedSentence w n t a r)) := TheoryTransport.sentence (source_packetStructureTailActualTreeContained w n t a r)

theorem native_packetStructureTailActualTreeContained {m} (w n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailActualTreeContainedSentence w n t a r)) := ZFReplay.replay (packetStructureTailActualTreeContained_kernel_certificate w n t a r)

def packetStructureTailActualForestContainedSentence {m} (w n l t a r : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureAcceptedSyntax.forest w n l t a).imp ((Formula.mem r w).imp ((NaturalAdditionBounds.below a r).imp ((NaturalAdditionBounds.below t r)))))).close

theorem source_packetStructureTailActualForestContained {m} (w n l t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailActualForestContainedSentence w n l t a r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionBounds.below a r) (Context.add (Formula.mem r w) (Context.add (PacketStructureAcceptedSyntax.forest w n l t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketStructureAcceptedSyntax.forest w n l t a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (NaturalAdditionBounds.below a r) := .hyp (Or.inl rfl)
  exact PacketStructureTailBounds.forest_contained hZ w n l t a r h0 h1 h2 h3

theorem packetStructureTailActualForestContained_kernel_certificate {m} (w n l t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailActualForestContainedSentence w n l t a r)) := TheoryTransport.sentence (source_packetStructureTailActualForestContained w n l t a r)

theorem native_packetStructureTailActualForestContained {m} (w n l t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailActualForestContainedSentence w n l t a r)) := ZFReplay.replay (packetStructureTailActualForestContained_kernel_certificate w n l t a r)

def packetStructureTailAllInternalTreeLawSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureTailLawSyntax.allTree w))).close

theorem source_packetStructureTailAllInternalTreeLaw {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailAllInternalTreeLawSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureTailLaws.all_tree hZ w h0

theorem packetStructureTailAllInternalTreeLaw_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailAllInternalTreeLawSentence w)) := TheoryTransport.sentence (source_packetStructureTailAllInternalTreeLaw w)

theorem native_packetStructureTailAllInternalTreeLaw {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailAllInternalTreeLawSentence w)) := ZFReplay.replay (packetStructureTailAllInternalTreeLaw_kernel_certificate w)

def packetStructureTailAllInternalForestLawSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureTailLawSyntax.allForest w))).close

theorem source_packetStructureTailAllInternalForestLaw {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailAllInternalForestLawSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureTailLaws.all_forest hZ w h0

theorem packetStructureTailAllInternalForestLaw_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailAllInternalForestLawSentence w)) := TheoryTransport.sentence (source_packetStructureTailAllInternalForestLaw w)

theorem native_packetStructureTailAllInternalForestLaw {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailAllInternalForestLawSentence w)) := ZFReplay.replay (packetStructureTailAllInternalForestLaw_kernel_certificate w)

def packetStructureTailAllInternalCoupledLawsOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketStructureTailLawSyntax.allLaw w))).close

theorem source_packetStructureTailAllInternalCoupledLawsOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetStructureTailAllInternalCoupledLawsOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketStructureTailLaws.all_law hZ w h0

theorem packetStructureTailAllInternalCoupledLawsOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetStructureTailAllInternalCoupledLawsOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetStructureTailAllInternalCoupledLawsOnlyOmega w)

theorem native_packetStructureTailAllInternalCoupledLawsOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetStructureTailAllInternalCoupledLawsOnlyOmegaSentence w)) := ZFReplay.replay (packetStructureTailAllInternalCoupledLawsOnlyOmega_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketStructureTail
