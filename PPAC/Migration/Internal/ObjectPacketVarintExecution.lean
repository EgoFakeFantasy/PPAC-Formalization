import PPAC.Migration.Internal.PacketVarintExecution

/-! Independent canonical varint lists exist uniquely on all internal natural inputs and every actual candidate has the independent byte guard; all joint IH and literal witnesses are discharged. Actual Tok/prefix correspondence, original varint/readTokens bridge, Basic AST, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketVarintExecution
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetVarintExecutionStrictQuotientAuthorizesJointIHSentence {m} (w B n d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((PacketVarintExecutionSyntax.earlier w n).imp ((PacketAffineSyntax.affine w B d q n).imp (((empty q).neg).imp ((PacketVarintExecutionSyntax.property w q))))))).close

theorem source_packetVarintExecutionStrictQuotientAuthorizesJointIH {m} (w B n d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionStrictQuotientAuthorizesJointIHSentence w B n d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((empty q).neg) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (PacketVarintExecutionSyntax.earlier w n) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketVarintExecutionSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ ((empty q).neg) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionHelpers.below_property hZ w B n d q h0 h1 h2 h3 h4

theorem packetVarintExecutionStrictQuotientAuthorizesJointIH_kernel_certificate {m} (w B n d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionStrictQuotientAuthorizesJointIHSentence w B n d q)) := TheoryTransport.sentence (source_packetVarintExecutionStrictQuotientAuthorizesJointIH w B n d q)

theorem native_packetVarintExecutionStrictQuotientAuthorizesJointIH {m} (w B n d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionStrictQuotientAuthorizesJointIHSentence w B n d q)) := ZFReplay.replay (packetVarintExecutionStrictQuotientAuthorizesJointIH_kernel_certificate w B n d q)

def packetVarintExecutionActualSmallListConstructedSentence {m} (w B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((Formula.mem n B).imp ((PacketVarintExecutionSyntax.existsList w n))))).close

theorem source_packetVarintExecutionActualSmallListConstructed {m} (w B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionActualSmallListConstructedSentence w B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n B) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem n B) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionTotal.small_point hZ w B n h0 h1 h2

theorem packetVarintExecutionActualSmallListConstructed_kernel_certificate {m} (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionActualSmallListConstructedSentence w B n)) := TheoryTransport.sentence (source_packetVarintExecutionActualSmallListConstructed w B n)

theorem native_packetVarintExecutionActualSmallListConstructed {m} (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionActualSmallListConstructedSentence w B n)) := ZFReplay.replay (packetVarintExecutionActualSmallListConstructed_kernel_certificate w B n)

def packetVarintExecutionActualRecursiveListConstructedSentence {m} (w B n d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((PacketVarintExecutionSyntax.earlier w n).imp ((PacketAffineSyntax.affine w B d q n).imp (((Formula.mem n B).neg).imp ((PacketVarintExecutionSyntax.existsList w n))))))).close

theorem source_packetVarintExecutionActualRecursiveListConstructed {m} (w B n d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionActualRecursiveListConstructedSentence w B n d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n B).neg) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (PacketVarintExecutionSyntax.earlier w n) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketVarintExecutionSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ ((Formula.mem n B).neg) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionTotal.large_point hZ w B n d q h0 h1 h2 h3 h4

theorem packetVarintExecutionActualRecursiveListConstructed_kernel_certificate {m} (w B n d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionActualRecursiveListConstructedSentence w B n d q)) := TheoryTransport.sentence (source_packetVarintExecutionActualRecursiveListConstructed w B n d q)

theorem native_packetVarintExecutionActualRecursiveListConstructed {m} (w B n d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionActualRecursiveListConstructedSentence w B n d q)) := ZFReplay.replay (packetVarintExecutionActualRecursiveListConstructed_kernel_certificate w B n d q)

def packetVarintExecutionExistenceJointStepSentence {m} (w B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((Formula.mem n w).imp ((PacketVarintExecutionSyntax.earlier w n).imp ((PacketVarintExecutionSyntax.existsList w n)))))).close

theorem source_packetVarintExecutionExistenceJointStep {m} (w B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionExistenceJointStepSentence w B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintExecutionSyntax.earlier w n) (Context.add (Formula.mem n w) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketVarintExecutionSyntax.earlier w n) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionTotal.point hZ w B n h0 h1 h2 h3

theorem packetVarintExecutionExistenceJointStep_kernel_certificate {m} (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionExistenceJointStepSentence w B n)) := TheoryTransport.sentence (source_packetVarintExecutionExistenceJointStep w B n)

theorem native_packetVarintExecutionExistenceJointStep {m} (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionExistenceJointStepSentence w B n)) := ZFReplay.replay (packetVarintExecutionExistenceJointStep_kernel_certificate w B n)

def packetVarintExecutionAllActualCandidatesByteGuardJointStepSentence {m} (w B C n s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketVarintExecutionSyntax.earlier w n).imp ((PacketVarintSyntax.canonical w n s).imp ((PacketByteInputSyntax.byteList w s))))))).close

theorem source_packetVarintExecutionAllActualCandidatesByteGuardJointStep {m} (w B C n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionAllActualCandidatesByteGuardJointStepSentence w B C n s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintSyntax.canonical w n s) (Context.add (PacketVarintExecutionSyntax.earlier w n) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketVarintExecutionSyntax.earlier w n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketVarintSyntax.canonical w n s) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionDomain.point hZ w B C n s h0 h1 h2 h3 h4

theorem packetVarintExecutionAllActualCandidatesByteGuardJointStep_kernel_certificate {m} (w B C n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionAllActualCandidatesByteGuardJointStepSentence w B C n s)) := TheoryTransport.sentence (source_packetVarintExecutionAllActualCandidatesByteGuardJointStep w B C n s)

theorem native_packetVarintExecutionAllActualCandidatesByteGuardJointStep {m} (w B C n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionAllActualCandidatesByteGuardJointStepSentence w B C n s)) := ZFReplay.replay (packetVarintExecutionAllActualCandidatesByteGuardJointStep_kernel_certificate w B C n s)

def packetVarintExecutionAllActualCandidateListsUniqueJointStepSentence {m} (w B n s t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((PacketVarintExecutionSyntax.earlier w n).imp ((PacketVarintSyntax.canonical w n s).imp ((PacketVarintSyntax.canonical w n t).imp ((Formula.equal s t))))))).close

theorem source_packetVarintExecutionAllActualCandidateListsUniqueJointStep {m} (w B n s t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionAllActualCandidateListsUniqueJointStepSentence w B n s t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintSyntax.canonical w n t) (Context.add (PacketVarintSyntax.canonical w n s) (Context.add (PacketVarintExecutionSyntax.earlier w n) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketVarintExecutionSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketVarintSyntax.canonical w n s) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketVarintSyntax.canonical w n t) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionUnique.point hZ w B n s t h0 h1 h2 h3 h4

theorem packetVarintExecutionAllActualCandidateListsUniqueJointStep_kernel_certificate {m} (w B n s t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionAllActualCandidateListsUniqueJointStepSentence w B n s t)) := TheoryTransport.sentence (source_packetVarintExecutionAllActualCandidateListsUniqueJointStep w B n s t)

theorem native_packetVarintExecutionAllActualCandidateListsUniqueJointStep {m} (w B n s t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionAllActualCandidateListsUniqueJointStepSentence w B n s t)) := ZFReplay.replay (packetVarintExecutionAllActualCandidateListsUniqueJointStep_kernel_certificate w B n s t)

def packetVarintExecutionJointPropertyStepSentence {m} (w B C n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.mem n w).imp ((PacketVarintExecutionSyntax.earlier w n).imp ((PacketVarintExecutionSyntax.property w n))))))).close

theorem source_packetVarintExecutionJointPropertyStep {m} (w B C n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionJointPropertyStepSentence w B C n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintExecutionSyntax.earlier w n) (Context.add (Formula.mem n w) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketVarintExecutionSyntax.earlier w n) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionInduction.property_from_earlier hZ w B C n h0 h1 h2 h3 h4

theorem packetVarintExecutionJointPropertyStep_kernel_certificate {m} (w B C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionJointPropertyStepSentence w B C n)) := TheoryTransport.sentence (source_packetVarintExecutionJointPropertyStep w B C n)

theorem native_packetVarintExecutionJointPropertyStep {m} (w B C n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionJointPropertyStepSentence w B C n)) := ZFReplay.replay (packetVarintExecutionJointPropertyStep_kernel_certificate w B C n)

def packetVarintExecutionOriginalFoundationSeparationAllJointIHDischargedSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketVarintExecutionInduction.allProperties w))))).close

theorem source_packetVarintExecutionOriginalFoundationSeparationAllJointIHDischarged {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionOriginalFoundationSeparationAllJointIHDischargedSentence w B C) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionInduction.all_properties_at hZ w B C h0 h1 h2

theorem packetVarintExecutionOriginalFoundationSeparationAllJointIHDischarged_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionOriginalFoundationSeparationAllJointIHDischargedSentence w B C)) := TheoryTransport.sentence (source_packetVarintExecutionOriginalFoundationSeparationAllJointIHDischarged w B C)

theorem native_packetVarintExecutionOriginalFoundationSeparationAllJointIHDischarged {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionOriginalFoundationSeparationAllJointIHDischargedSentence w B C)) := ZFReplay.replay (packetVarintExecutionOriginalFoundationSeparationAllJointIHDischarged_kernel_certificate w B C)

def packetVarintExecutionAllJointPropertiesOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintExecutionInduction.allProperties w))).close

theorem source_packetVarintExecutionAllJointPropertiesOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionAllJointPropertiesOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionLiterals.all_properties hZ w h0

theorem packetVarintExecutionAllJointPropertiesOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionAllJointPropertiesOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetVarintExecutionAllJointPropertiesOnlyOmega w)

theorem native_packetVarintExecutionAllJointPropertiesOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionAllJointPropertiesOnlyOmegaSentence w)) := ZFReplay.replay (packetVarintExecutionAllJointPropertiesOnlyOmega_kernel_certificate w)

def packetVarintExecutionActualListExistsOnlyOmegaSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((PacketVarintExecutionSyntax.existsList w n)))).close

theorem source_packetVarintExecutionActualListExistsOnlyOmega {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionActualListExistsOnlyOmegaSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionLiterals.exists_list hZ w n h0 h1

theorem packetVarintExecutionActualListExistsOnlyOmega_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionActualListExistsOnlyOmegaSentence w n)) := TheoryTransport.sentence (source_packetVarintExecutionActualListExistsOnlyOmega w n)

theorem native_packetVarintExecutionActualListExistsOnlyOmega {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionActualListExistsOnlyOmegaSentence w n)) := ZFReplay.replay (packetVarintExecutionActualListExistsOnlyOmega_kernel_certificate w n)

def packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuardSentence {m} (w n s : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintSyntax.canonical w n s).imp ((PacketByteInputSyntax.byteList w s)))).close

theorem source_packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuard {m} (w n s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuardSentence w n s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintSyntax.canonical w n s) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketVarintSyntax.canonical w n s) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionLiterals.byte_input hZ w n s h0 h1

theorem packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuard_kernel_certificate {m} (w n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuardSentence w n s)) := TheoryTransport.sentence (source_packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuard w n s)

theorem native_packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuard {m} (w n s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuardSentence w n s)) := ZFReplay.replay (packetVarintExecutionEveryActualCanonicalCandidateHasIndependentByteGuard_kernel_certificate w n s)

def packetVarintExecutionEveryActualCanonicalCandidateListUniqueSentence {m} (w n s t : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintSyntax.canonical w n s).imp ((PacketVarintSyntax.canonical w n t).imp ((Formula.equal s t))))).close

theorem source_packetVarintExecutionEveryActualCanonicalCandidateListUnique {m} (w n s t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionEveryActualCanonicalCandidateListUniqueSentence w n s t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintSyntax.canonical w n t) (Context.add (PacketVarintSyntax.canonical w n s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketVarintSyntax.canonical w n s) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketVarintSyntax.canonical w n t) := .hyp (Or.inl rfl)
  exact PacketVarintExecutionLiterals.list_unique hZ w n s t h0 h1 h2

theorem packetVarintExecutionEveryActualCanonicalCandidateListUnique_kernel_certificate {m} (w n s t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionEveryActualCanonicalCandidateListUniqueSentence w n s t)) := TheoryTransport.sentence (source_packetVarintExecutionEveryActualCanonicalCandidateListUnique w n s t)

theorem native_packetVarintExecutionEveryActualCanonicalCandidateListUnique {m} (w n s t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionEveryActualCanonicalCandidateListUniqueSentence w n s t)) := ZFReplay.replay (packetVarintExecutionEveryActualCanonicalCandidateListUnique_kernel_certificate w n s t)

def packetVarintExecutionExistenceExactNaturalDomainSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp (((PacketVarintExecutionSyntax.existsList w n).iff (.mem n w)))).close

theorem source_packetVarintExecutionExistenceExactNaturalDomain {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionExistenceExactNaturalDomainSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketVarintExecution.exists_iff hZ w n h0

theorem packetVarintExecutionExistenceExactNaturalDomain_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionExistenceExactNaturalDomainSentence w n)) := TheoryTransport.sentence (source_packetVarintExecutionExistenceExactNaturalDomain w n)

theorem native_packetVarintExecutionExistenceExactNaturalDomain {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionExistenceExactNaturalDomainSentence w n)) := ZFReplay.replay (packetVarintExecutionExistenceExactNaturalDomain_kernel_certificate w n)

def packetVarintExecutionUniqueByteListFiberExactNaturalDomainSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp (((PacketVarintExecutionFiberSyntax.fiber w n).iff (.mem n w)))).close

theorem source_packetVarintExecutionUniqueByteListFiberExactNaturalDomain {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionUniqueByteListFiberExactNaturalDomainSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketVarintExecution.fiber_iff hZ w n h0

theorem packetVarintExecutionUniqueByteListFiberExactNaturalDomain_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionUniqueByteListFiberExactNaturalDomainSentence w n)) := TheoryTransport.sentence (source_packetVarintExecutionUniqueByteListFiberExactNaturalDomain w n)

theorem native_packetVarintExecutionUniqueByteListFiberExactNaturalDomain {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionUniqueByteListFiberExactNaturalDomainSentence w n)) := ZFReplay.replay (packetVarintExecutionUniqueByteListFiberExactNaturalDomain_kernel_certificate w n)

def packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintExecutionFiberSyntax.allLaw w))).close

theorem source_packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketVarintExecution.all_law hZ w h0

theorem packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmega w)

theorem native_packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmegaSentence w)) := ZFReplay.replay (packetVarintExecutionAllInternalUniqueByteListFibersOnlyOmega_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketVarintExecution
