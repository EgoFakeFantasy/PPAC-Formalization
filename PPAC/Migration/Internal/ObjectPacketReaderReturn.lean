import PPAC.Migration.Internal.PacketReaderReturnRunNormalize

/-! Actual EOF/rejection option returns, exact reversed payload, whole actual-run return existence and object uniqueness. Original reader initialization, full program bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketReaderReturn
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetReaderReturnActualNoneExistsSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.ex ((Formula.mem (Fin.last m) w.castSucc).conj (PacketReaderReturnSyntax.none w.castSucc (Fin.last m)))))).close

theorem source_packetReaderReturnActualNoneExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnActualNoneExistsSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketReaderReturnPayload.none_exists hZ w h0

theorem packetReaderReturnActualNoneExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnActualNoneExistsSentence w)) := TheoryTransport.sentence (source_packetReaderReturnActualNoneExists w)

theorem native_packetReaderReturnActualNoneExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnActualNoneExistsSentence w)) := ZFReplay.replay (packetReaderReturnActualNoneExists_kernel_certificate w)

def packetReaderReturnActualSomeExistsSentence {m} (w r : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem r w).imp ((.ex ((Formula.mem (Fin.last m) w.castSucc).conj (PacketReaderReturnSyntax.some w.castSucc r.castSucc (Fin.last m))))))).close

theorem source_packetReaderReturnActualSomeExists {m} (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnActualSomeExistsSentence w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem r w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem r w) := .hyp (Or.inl rfl)
  exact PacketReaderReturnPayload.some_exists hZ w r h0 h1

theorem packetReaderReturnActualSomeExists_kernel_certificate {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnActualSomeExistsSentence w r)) := TheoryTransport.sentence (source_packetReaderReturnActualSomeExists w r)

theorem native_packetReaderReturnActualSomeExists {m} (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnActualSomeExistsSentence w r)) := ZFReplay.replay (packetReaderReturnActualSomeExists_kernel_certificate w r)

def packetReaderReturnActualNoneUniqueSentence {m} (w p q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.none w p).imp ((PacketReaderReturnSyntax.none w q).imp ((Formula.equal p q))))).close

theorem source_packetReaderReturnActualNoneUnique {m} (w p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnActualNoneUniqueSentence w p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.none w q) (Context.add (PacketReaderReturnSyntax.none w p) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderReturnSyntax.none w p) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderReturnSyntax.none w q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnPayload.none_unique hZ w p q h0 h1 h2

theorem packetReaderReturnActualNoneUnique_kernel_certificate {m} (w p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnActualNoneUniqueSentence w p q)) := TheoryTransport.sentence (source_packetReaderReturnActualNoneUnique w p q)

theorem native_packetReaderReturnActualNoneUnique {m} (w p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnActualNoneUniqueSentence w p q)) := ZFReplay.replay (packetReaderReturnActualNoneUnique_kernel_certificate w p q)

def packetReaderReturnActualSomeUniqueSentence {m} (w r p q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.some w r p).imp ((PacketReaderReturnSyntax.some w r q).imp ((Formula.equal p q))))).close

theorem source_packetReaderReturnActualSomeUnique {m} (w r p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnActualSomeUniqueSentence w r p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w r q) (Context.add (PacketReaderReturnSyntax.some w r p) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderReturnSyntax.some w r p) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderReturnSyntax.some w r q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnPayload.some_unique hZ w r p q h0 h1 h2

theorem packetReaderReturnActualSomeUnique_kernel_certificate {m} (w r p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnActualSomeUniqueSentence w r p q)) := TheoryTransport.sentence (source_packetReaderReturnActualSomeUnique w r p q)

theorem native_packetReaderReturnActualSomeUnique {m} (w r p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnActualSomeUniqueSentence w r p q)) := ZFReplay.replay (packetReaderReturnActualSomeUnique_kernel_certificate w r p q)

def packetReaderReturnActualSomePayloadUniqueSentence {m} (w r s q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.some w r q).imp ((PacketReaderReturnSyntax.some w s q).imp ((Formula.equal r s))))).close

theorem source_packetReaderReturnActualSomePayloadUnique {m} (w r s q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnActualSomePayloadUniqueSentence w r s q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w s q) (Context.add (PacketReaderReturnSyntax.some w r q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderReturnSyntax.some w r q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderReturnSyntax.some w s q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnPayload.some_payload_unique hZ w r s q h0 h1 h2

theorem packetReaderReturnActualSomePayloadUnique_kernel_certificate {m} (w r s q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnActualSomePayloadUniqueSentence w r s q)) := TheoryTransport.sentence (source_packetReaderReturnActualSomePayloadUnique w r s q)

theorem native_packetReaderReturnActualSomePayloadUnique {m} (w r s q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnActualSomePayloadUniqueSentence w r s q)) := ZFReplay.replay (packetReaderReturnActualSomePayloadUnique_kernel_certificate w r s q)

def packetReaderReturnActualOptionsDisjointSentence {m} (w r q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.none w q).imp ((PacketReaderReturnSyntax.some w r q).imp ((Formula.bot))))).close

theorem source_packetReaderReturnActualOptionsDisjoint {m} (w r q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnActualOptionsDisjointSentence w r q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w r q) (Context.add (PacketReaderReturnSyntax.none w q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderReturnSyntax.none w q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderReturnSyntax.some w r q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnPayload.disjoint hZ w r q h0 h1 h2

theorem packetReaderReturnActualOptionsDisjoint_kernel_certificate {m} (w r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnActualOptionsDisjointSentence w r q)) := TheoryTransport.sentence (source_packetReaderReturnActualOptionsDisjoint w r q)

theorem native_packetReaderReturnActualOptionsDisjoint {m} (w r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnActualOptionsDisjointSentence w r q)) := ZFReplay.replay (packetReaderReturnActualOptionsDisjoint_kernel_certificate w r q)

def packetReaderReturnEOFActualReverseReturnExistsSentence {m} (w B z o L v s a : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderInputSyntax.eofSuccess w z o L v s a).imp ((PacketReaderReturnSyntax.existsResult w B z o L v s a)))).close

theorem source_packetReaderReturnEOFActualReverseReturnExists {m} (w B z o L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnEOFActualReverseReturnExistsSentence w B z o L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderInputSyntax.eofSuccess w z o L v s a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderInputSyntax.eofSuccess w z o L v s a) := .hyp (Or.inl rfl)
  exact PacketReaderReturnExistence.success_exists hZ w B z o L v s a h0 h1

theorem packetReaderReturnEOFActualReverseReturnExists_kernel_certificate {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnEOFActualReverseReturnExistsSentence w B z o L v s a)) := TheoryTransport.sentence (source_packetReaderReturnEOFActualReverseReturnExists w B z o L v s a)

theorem native_packetReaderReturnEOFActualReverseReturnExists {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnEOFActualReverseReturnExistsSentence w B z o L v s a)) := ZFReplay.replay (packetReaderReturnEOFActualReverseReturnExists_kernel_certificate w B z o L v s a)

def packetReaderReturnActualRejectionReturnExistsSentence {m} (w B z o L v s a : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.rejection w B z o L v s a).imp ((PacketReaderReturnSyntax.existsResult w B z o L v s a)))).close

theorem source_packetReaderReturnActualRejectionReturnExists {m} (w B z o L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnActualRejectionReturnExistsSentence w B z o L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.rejection w B z o L v s a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderReturnSyntax.rejection w B z o L v s a) := .hyp (Or.inl rfl)
  exact PacketReaderReturnExistence.failure_exists hZ w B z o L v s a h0 h1

theorem packetReaderReturnActualRejectionReturnExists_kernel_certificate {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnActualRejectionReturnExistsSentence w B z o L v s a)) := TheoryTransport.sentence (source_packetReaderReturnActualRejectionReturnExists w B z o L v s a)

theorem native_packetReaderReturnActualRejectionReturnExists {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnActualRejectionReturnExistsSentence w B z o L v s a)) := ZFReplay.replay (packetReaderReturnActualRejectionReturnExists_kernel_certificate w B z o L v s a)

def packetReaderReturnLocalDomainExactlyOriginalTerminalSentence {m} (w B z o L v s a : Fin m) : Source.Sentence := ((omega w).imp (((PacketReaderReturnSyntax.existsResult w B z o L v s a).iff (PacketReaderTerminalSyntax.raw w B z o L v s a)))).close

theorem source_packetReaderReturnLocalDomainExactlyOriginalTerminal {m} (w B z o L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnLocalDomainExactlyOriginalTerminalSentence w B z o L v s a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketReaderReturnExistence.exact_domain hZ w B z o L v s a h0

theorem packetReaderReturnLocalDomainExactlyOriginalTerminal_kernel_certificate {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnLocalDomainExactlyOriginalTerminalSentence w B z o L v s a)) := TheoryTransport.sentence (source_packetReaderReturnLocalDomainExactlyOriginalTerminal w B z o L v s a)

theorem native_packetReaderReturnLocalDomainExactlyOriginalTerminal {m} (w B z o L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnLocalDomainExactlyOriginalTerminalSentence w B z o L v s a)) := ZFReplay.replay (packetReaderReturnLocalDomainExactlyOriginalTerminal_kernel_certificate w B z o L v s a)

def packetReaderReturnLocalCandidateUniqueSentence {m} (w B z o L v s a p q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.result w B z o L v s a p).imp ((PacketReaderReturnSyntax.result w B z o L v s a q).imp ((Formula.equal p q))))).close

theorem source_packetReaderReturnLocalCandidateUnique {m} (w B z o L v s a p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnLocalCandidateUniqueSentence w B z o L v s a p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.result w B z o L v s a q) (Context.add (PacketReaderReturnSyntax.result w B z o L v s a p) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderReturnSyntax.result w B z o L v s a p) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderReturnSyntax.result w B z o L v s a q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnUnique.unique hZ w B z o L v s a p q h0 h1 h2

theorem packetReaderReturnLocalCandidateUnique_kernel_certificate {m} (w B z o L v s a p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnLocalCandidateUniqueSentence w B z o L v s a p q)) := TheoryTransport.sentence (source_packetReaderReturnLocalCandidateUnique w B z o L v s a p q)

theorem native_packetReaderReturnLocalCandidateUnique {m} (w B z o L v s a p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnLocalCandidateUniqueSentence w B z o L v s a p q)) := ZFReplay.replay (packetReaderReturnLocalCandidateUnique_kernel_certificate w B z o L v s a p q)

def packetReaderReturnExactSomeActualReverseSentence {m} (w B z o L v s a r q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.some w r q).imp (((PacketReaderReturnSyntax.result w B z o L v s a q).iff ((PacketReaderInputSyntax.eofSuccess w z o L v s a).conj (StructuralListReverseSyntax.reverses w a r)))))).close

theorem source_packetReaderReturnExactSomeActualReverse {m} (w B z o L v s a r q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnExactSomeActualReverseSentence w B z o L v s a r q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w r q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderReturnSyntax.some w r q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnNormalize.at_some hZ w B z o L v s a r q h0 h1

theorem packetReaderReturnExactSomeActualReverse_kernel_certificate {m} (w B z o L v s a r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnExactSomeActualReverseSentence w B z o L v s a r q)) := TheoryTransport.sentence (source_packetReaderReturnExactSomeActualReverse w B z o L v s a r q)

theorem native_packetReaderReturnExactSomeActualReverse {m} (w B z o L v s a r q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnExactSomeActualReverseSentence w B z o L v s a r q)) := ZFReplay.replay (packetReaderReturnExactSomeActualReverse_kernel_certificate w B z o L v s a r q)

def packetReaderReturnExactNoneOriginalRejectionSentence {m} (w B z o L v s a q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.none w q).imp (((PacketReaderReturnSyntax.result w B z o L v s a q).iff (PacketReaderReturnSyntax.rejection w B z o L v s a))))).close

theorem source_packetReaderReturnExactNoneOriginalRejection {m} (w B z o L v s a q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnExactNoneOriginalRejectionSentence w B z o L v s a q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.none w q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderReturnSyntax.none w q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnNormalize.at_none hZ w B z o L v s a q h0 h1

theorem packetReaderReturnExactNoneOriginalRejection_kernel_certificate {m} (w B z o L v s a q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnExactNoneOriginalRejectionSentence w B z o L v s a q)) := TheoryTransport.sentence (source_packetReaderReturnExactNoneOriginalRejection w B z o L v s a q)

theorem native_packetReaderReturnExactNoneOriginalRejection {m} (w B z o L v s a q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnExactNoneOriginalRejectionSentence w B z o L v s a q)) := ZFReplay.replay (packetReaderReturnExactNoneOriginalRejection_kernel_certificate w B z o L v s a q)

def packetReaderReturnLocalValueNaturalSentence {m} (w B z o L v s a q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnSyntax.result w B z o L v s a q).imp ((Formula.mem q w)))).close

theorem source_packetReaderReturnLocalValueNatural {m} (w B z o L v s a q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnLocalValueNaturalSentence w B z o L v s a q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.result w B z o L v s a q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderReturnSyntax.result w B z o L v s a q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnNormalize.natural hZ w B z o L v s a q h0 h1

theorem packetReaderReturnLocalValueNatural_kernel_certificate {m} (w B z o L v s a q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnLocalValueNaturalSentence w B z o L v s a q)) := TheoryTransport.sentence (source_packetReaderReturnLocalValueNatural w B z o L v s a q)

theorem native_packetReaderReturnLocalValueNatural {m} (w B z o L v s a q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnLocalValueNaturalSentence w B z o L v s a q)) := ZFReplay.replay (packetReaderReturnLocalValueNatural_kernel_certificate w B z o L v s a q)

def packetReaderReturnCodedNormalizeAtActualSourceSentence {m} (w B z o n q L v s a : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderStateSyntax.code w L v s a n).imp (((PacketReaderReturnCodedSyntax.coded w B z o n q).iff (PacketReaderReturnSyntax.result w B z o L v s a q))))).close

theorem source_packetReaderReturnCodedNormalizeAtActualSource {m} (w B z o n q L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnCodedNormalizeAtActualSourceSentence w B z o n q L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w L v s a n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderStateSyntax.code w L v s a n) := .hyp (Or.inl rfl)
  exact PacketReaderReturnCoded.at_source hZ w B z o n q L v s a h0 h1

theorem packetReaderReturnCodedNormalizeAtActualSource_kernel_certificate {m} (w B z o n q L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnCodedNormalizeAtActualSourceSentence w B z o n q L v s a)) := TheoryTransport.sentence (source_packetReaderReturnCodedNormalizeAtActualSource w B z o n q L v s a)

theorem native_packetReaderReturnCodedNormalizeAtActualSource {m} (w B z o n q L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnCodedNormalizeAtActualSourceSentence w B z o n q L v s a)) := ZFReplay.replay (packetReaderReturnCodedNormalizeAtActualSource_kernel_certificate w B z o n q L v s a)

def packetReaderReturnCodedExistsOnOriginalObservationSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderTerminalSyntax.observation w B z o n).imp ((PacketReaderReturnCodedSyntax.existsCoded w B z o n)))).close

theorem source_packetReaderReturnCodedExistsOnOriginalObservation {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnCodedExistsOnOriginalObservationSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderTerminalSyntax.observation w B z o n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderTerminalSyntax.observation w B z o n) := .hyp (Or.inl rfl)
  exact PacketReaderReturnCoded.exists_from_observation hZ w B z o n h0 h1

theorem packetReaderReturnCodedExistsOnOriginalObservation_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnCodedExistsOnOriginalObservationSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderReturnCodedExistsOnOriginalObservation w B z o n)

theorem native_packetReaderReturnCodedExistsOnOriginalObservation {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnCodedExistsOnOriginalObservationSentence w B z o n)) := ZFReplay.replay (packetReaderReturnCodedExistsOnOriginalObservation_kernel_certificate w B z o n)

def packetReaderReturnCodedCandidateUniqueSentence {m} (w B z o n p q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnCodedSyntax.coded w B z o n p).imp ((PacketReaderReturnCodedSyntax.coded w B z o n q).imp ((Formula.equal p q))))).close

theorem source_packetReaderReturnCodedCandidateUnique {m} (w B z o n p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnCodedCandidateUniqueSentence w B z o n p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnCodedSyntax.coded w B z o n q) (Context.add (PacketReaderReturnCodedSyntax.coded w B z o n p) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketReaderReturnCodedSyntax.coded w B z o n p) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderReturnCodedSyntax.coded w B z o n q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnCoded.unique hZ w B z o n p q h0 h1 h2

theorem packetReaderReturnCodedCandidateUnique_kernel_certificate {m} (w B z o n p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnCodedCandidateUniqueSentence w B z o n p q)) := TheoryTransport.sentence (source_packetReaderReturnCodedCandidateUnique w B z o n p q)

theorem native_packetReaderReturnCodedCandidateUnique {m} (w B z o n p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnCodedCandidateUniqueSentence w B z o n p q)) := ZFReplay.replay (packetReaderReturnCodedCandidateUnique_kernel_certificate w B z o n p q)

def packetReaderReturnCodedDomainExactlyOriginalObservationSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp (((PacketReaderReturnCodedSyntax.existsCoded w B z o n).iff (PacketReaderTerminalSyntax.observation w B z o n)))).close

theorem source_packetReaderReturnCodedDomainExactlyOriginalObservation {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnCodedDomainExactlyOriginalObservationSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketReaderReturnCoded.exact_domain hZ w B z o n h0

theorem packetReaderReturnCodedDomainExactlyOriginalObservation_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnCodedDomainExactlyOriginalObservationSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderReturnCodedDomainExactlyOriginalObservation w B z o n)

theorem native_packetReaderReturnCodedDomainExactlyOriginalObservation {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnCodedDomainExactlyOriginalObservationSentence w B z o n)) := ZFReplay.replay (packetReaderReturnCodedDomainExactlyOriginalObservation_kernel_certificate w B z o n)

def packetReaderReturnCodedValueNaturalSentence {m} (w B z o n q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnCodedSyntax.coded w B z o n q).imp ((Formula.mem q w)))).close

theorem source_packetReaderReturnCodedValueNatural {m} (w B z o n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnCodedValueNaturalSentence w B z o n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnCodedSyntax.coded w B z o n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderReturnCodedSyntax.coded w B z o n q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnCoded.natural hZ w B z o n q h0 h1

theorem packetReaderReturnCodedValueNatural_kernel_certificate {m} (w B z o n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnCodedValueNaturalSentence w B z o n q)) := TheoryTransport.sentence (source_packetReaderReturnCodedValueNatural w B z o n q)

theorem native_packetReaderReturnCodedValueNatural {m} (w B z o n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnCodedValueNaturalSentence w B z o n q)) := ZFReplay.replay (packetReaderReturnCodedValueNatural_kernel_certificate w B z o n q)

def packetReaderReturnEveryActualCarrierHasRealRunReturnSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderReturnCodedSyntax.existsRun w B z o n))))))).close

theorem source_packetReaderReturnEveryActualCarrierHasRealRunReturn {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnEveryActualCarrierHasRealRunReturnSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderReturnRunExistence.exists_run hZ w B z o n h0 h1 h2 h3 h4

theorem packetReaderReturnEveryActualCarrierHasRealRunReturn_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnEveryActualCarrierHasRealRunReturnSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderReturnEveryActualCarrierHasRealRunReturn w B z o n)

theorem native_packetReaderReturnEveryActualCarrierHasRealRunReturn {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnEveryActualCarrierHasRealRunReturnSentence w B z o n)) := ZFReplay.replay (packetReaderReturnEveryActualCarrierHasRealRunReturn_kernel_certificate w B z o n)

def packetReaderReturnRunDomainExactlyActualCarrierSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp (((PacketReaderReturnCodedSyntax.existsRun w B z o n).iff (PacketReaderStateSyntax.carrier w n))))))).close

theorem source_packetReaderReturnRunDomainExactlyActualCarrier {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnRunDomainExactlyActualCarrierSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inl rfl)
  exact PacketReaderReturnRunExistence.exact_domain hZ w B z o n h0 h1 h2 h3

theorem packetReaderReturnRunDomainExactlyActualCarrier_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnRunDomainExactlyActualCarrierSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderReturnRunDomainExactlyActualCarrier w B z o n)

theorem native_packetReaderReturnRunDomainExactlyActualCarrier {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnRunDomainExactlyActualCarrierSentence w B z o n)) := ZFReplay.replay (packetReaderReturnRunDomainExactlyActualCarrier_kernel_certificate w B z o n)

def packetReaderReturnRealRunCandidateUniqueSentence {m} (w B z o n p q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderReturnCodedSyntax.run w B z o n p).imp ((PacketReaderReturnCodedSyntax.run w B z o n q).imp ((Formula.equal p q)))))).close

theorem source_packetReaderReturnRealRunCandidateUnique {m} (w B z o n p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnRealRunCandidateUniqueSentence w B z o n p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnCodedSyntax.run w B z o n q) (Context.add (PacketReaderReturnCodedSyntax.run w B z o n p) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderReturnCodedSyntax.run w B z o n p) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderReturnCodedSyntax.run w B z o n q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnRunUnique.unique hZ w B z o n p q h0 h1 h2 h3

theorem packetReaderReturnRealRunCandidateUnique_kernel_certificate {m} (w B z o n p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnRealRunCandidateUniqueSentence w B z o n p q)) := TheoryTransport.sentence (source_packetReaderReturnRealRunCandidateUnique w B z o n p q)

theorem native_packetReaderReturnRealRunCandidateUnique {m} (w B z o n p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnRealRunCandidateUniqueSentence w B z o n p q)) := ZFReplay.replay (packetReaderReturnRealRunCandidateUnique_kernel_certificate w B z o n p q)

def packetReaderReturnRealRunValueNaturalSentence {m} (w B z o n q : Fin m) : Source.Sentence := ((omega w).imp ((PacketReaderReturnCodedSyntax.run w B z o n q).imp ((Formula.mem q w)))).close

theorem source_packetReaderReturnRealRunValueNatural {m} (w B z o n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnRealRunValueNaturalSentence w B z o n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnCodedSyntax.run w B z o n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketReaderReturnCodedSyntax.run w B z o n q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnRunUnique.natural hZ w B z o n q h0 h1

theorem packetReaderReturnRealRunValueNatural_kernel_certificate {m} (w B z o n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnRealRunValueNaturalSentence w B z o n q)) := TheoryTransport.sentence (source_packetReaderReturnRealRunValueNatural w B z o n q)

theorem native_packetReaderReturnRealRunValueNatural {m} (w B z o n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnRealRunValueNaturalSentence w B z o n q)) := ZFReplay.replay (packetReaderReturnRealRunValueNatural_kernel_certificate w B z o n q)

def packetReaderReturnRealRunObjectExistsUniqueFiberSentence {m} (w B z o n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((empty z).imp ((Formula.mem o w).imp ((PacketReaderStateSyntax.carrier w n).imp ((PacketReaderReturnCodedSyntax.runFiber w B z o n))))))).close

theorem source_packetReaderReturnRealRunObjectExistsUniqueFiber {m} (w B z o n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnRealRunObjectExistsUniqueFiberSentence w B z o n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.carrier w n) (Context.add (Formula.mem o w) (Context.add (empty z) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem o w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderStateSyntax.carrier w n) := .hyp (Or.inl rfl)
  exact PacketReaderReturnRunUnique.exists_unique hZ w B z o n h0 h1 h2 h3 h4

theorem packetReaderReturnRealRunObjectExistsUniqueFiber_kernel_certificate {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnRealRunObjectExistsUniqueFiberSentence w B z o n)) := TheoryTransport.sentence (source_packetReaderReturnRealRunObjectExistsUniqueFiber w B z o n)

theorem native_packetReaderReturnRealRunObjectExistsUniqueFiber {m} (w B z o n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnRealRunObjectExistsUniqueFiberSentence w B z o n)) := ZFReplay.replay (packetReaderReturnRealRunObjectExistsUniqueFiber_kernel_certificate w B z o n)

def packetReaderReturnRealRunNormalizeAtStoppedHistorySentence {m} (w B z o n r l d f q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp (((PacketReaderReturnCodedSyntax.run w B z o n q).iff (PacketReaderReturnCodedSyntax.coded w B z o r q)))))).close

theorem source_packetReaderReturnRealRunNormalizeAtStoppedHistory {m} (w B z o n r l d f q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnRealRunNormalizeAtStoppedHistorySentence w B z o n r l d f q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inl rfl)
  exact PacketReaderReturnRunNormalize.at_history hZ w B z o n r l d f q h0 h1 h2

theorem packetReaderReturnRealRunNormalizeAtStoppedHistory_kernel_certificate {m} (w B z o n r l d f q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnRealRunNormalizeAtStoppedHistorySentence w B z o n r l d f q)) := TheoryTransport.sentence (source_packetReaderReturnRealRunNormalizeAtStoppedHistory w B z o n r l d f q)

theorem native_packetReaderReturnRealRunNormalizeAtStoppedHistory {m} (w B z o n r l d f q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnRealRunNormalizeAtStoppedHistorySentence w B z o n r l d f q)) := ZFReplay.replay (packetReaderReturnRealRunNormalizeAtStoppedHistory_kernel_certificate w B z o n r l d f q)

def packetReaderReturnRealRunNormalizeAtActualEndpointSentence {m} (w B z o n r l d f q L v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderStateSyntax.code w L v s a r).imp (((PacketReaderReturnCodedSyntax.run w B z o n q).iff (PacketReaderReturnSyntax.result w B z o L v s a q))))))).close

theorem source_packetReaderReturnRealRunNormalizeAtActualEndpoint {m} (w B z o n r l d f q L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnRealRunNormalizeAtActualEndpointSentence w B z o n r l d f q L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderStateSyntax.code w L v s a r) (Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketReaderStateSyntax.code w L v s a r) := .hyp (Or.inl rfl)
  exact PacketReaderReturnRunNormalize.at_endpoint hZ w B z o n r l d f q L v s a h0 h1 h2 h3

theorem packetReaderReturnRealRunNormalizeAtActualEndpoint_kernel_certificate {m} (w B z o n r l d f q L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnRealRunNormalizeAtActualEndpointSentence w B z o n r l d f q L v s a)) := TheoryTransport.sentence (source_packetReaderReturnRealRunNormalizeAtActualEndpoint w B z o n r l d f q L v s a)

theorem native_packetReaderReturnRealRunNormalizeAtActualEndpoint {m} (w B z o n r l d f q L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnRealRunNormalizeAtActualEndpointSentence w B z o n r l d f q L v s a)) := ZFReplay.replay (packetReaderReturnRealRunNormalizeAtActualEndpoint_kernel_certificate w B z o n r l d f q L v s a)

def packetReaderReturnRealRunExactSomeActualReverseSentence {m} (w B z o n r l d f q L v s a u : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderStateSyntax.code w L v s a r).imp ((PacketReaderReturnSyntax.some w u q).imp (((PacketReaderReturnCodedSyntax.run w B z o n q).iff ((PacketReaderInputSyntax.eofSuccess w z o L v s a).conj (StructuralListReverseSyntax.reverses w a u))))))))).close

theorem source_packetReaderReturnRealRunExactSomeActualReverse {m} (w B z o n r l d f q L v s a u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnRealRunExactSomeActualReverseSentence w B z o n r l d f q L v s a u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.some w u q) (Context.add (PacketReaderStateSyntax.code w L v s a r) (Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketReaderStateSyntax.code w L v s a r) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderReturnSyntax.some w u q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnRunNormalize.at_some hZ w B z o n r l d f q L v s a u h0 h1 h2 h3 h4

theorem packetReaderReturnRealRunExactSomeActualReverse_kernel_certificate {m} (w B z o n r l d f q L v s a u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnRealRunExactSomeActualReverseSentence w B z o n r l d f q L v s a u)) := TheoryTransport.sentence (source_packetReaderReturnRealRunExactSomeActualReverse w B z o n r l d f q L v s a u)

theorem native_packetReaderReturnRealRunExactSomeActualReverse {m} (w B z o n r l d f q L v s a u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnRealRunExactSomeActualReverseSentence w B z o n r l d f q L v s a u)) := ZFReplay.replay (packetReaderReturnRealRunExactSomeActualReverse_kernel_certificate w B z o n r l d f q L v s a u)

def packetReaderReturnRealRunExactNoneOriginalRejectionSentence {m} (w B z o n r l d f q L v s a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((PacketReaderStoppingSyntax.halted w B z o n r l d f).imp ((PacketReaderStateSyntax.code w L v s a r).imp ((PacketReaderReturnSyntax.none w q).imp (((PacketReaderReturnCodedSyntax.run w B z o n q).iff (PacketReaderReturnSyntax.rejection w B z o L v s a)))))))).close

theorem source_packetReaderReturnRealRunExactNoneOriginalRejection {m} (w B z o n r l d f q L v s a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetReaderReturnRealRunExactNoneOriginalRejectionSentence w B z o n r l d f q L v s a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketReaderReturnSyntax.none w q) (Context.add (PacketReaderStateSyntax.code w L v s a r) (Context.add (PacketReaderStoppingSyntax.halted w B z o n r l d f) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketReaderStoppingSyntax.halted w B z o n r l d f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketReaderStateSyntax.code w L v s a r) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketReaderReturnSyntax.none w q) := .hyp (Or.inl rfl)
  exact PacketReaderReturnRunNormalize.at_none hZ w B z o n r l d f q L v s a h0 h1 h2 h3 h4

theorem packetReaderReturnRealRunExactNoneOriginalRejection_kernel_certificate {m} (w B z o n r l d f q L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetReaderReturnRealRunExactNoneOriginalRejectionSentence w B z o n r l d f q L v s a)) := TheoryTransport.sentence (source_packetReaderReturnRealRunExactNoneOriginalRejection w B z o n r l d f q L v s a)

theorem native_packetReaderReturnRealRunExactNoneOriginalRejection {m} (w B z o n r l d f q L v s a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetReaderReturnRealRunExactNoneOriginalRejectionSentence w B z o n r l d f q L v s a)) := ZFReplay.replay (packetReaderReturnRealRunExactNoneOriginalRejection_kernel_certificate w B z o n r l d f q L v s a)

end PPAC.Migration.Internal.ObjectPacketReaderReturn
