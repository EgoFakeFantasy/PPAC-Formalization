import PPAC.Migration.Internal.PacketTokenPrefixLaws

/-! Actual token numeric prefix inversion and byte branch disjointness for all internal candidates; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketTokenPrefix
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetTokenPrefixShiftedByteNotSmallSentence {m} (w B d q n y : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((NaturalAdditionSyntax.sum w d B y).imp (((Formula.mem y B).neg))))).close

theorem source_packetTokenPrefixShiftedByteNotSmall {m} (w B d q n y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixShiftedByteNotSmallSentence w B d q n y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionSyntax.sum w d B y) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (NaturalAdditionSyntax.sum w d B y) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixValues.shifted_not_small hZ w B d q n y h0 h1 h2

theorem packetTokenPrefixShiftedByteNotSmall_kernel_certificate {m} (w B d q n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixShiftedByteNotSmallSentence w B d q n y)) := TheoryTransport.sentence (source_packetTokenPrefixShiftedByteNotSmall w B d q n y)

theorem native_packetTokenPrefixShiftedByteNotSmall {m} (w B d q n y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixShiftedByteNotSmallSentence w B d q n y)) := ZFReplay.replay (packetTokenPrefixShiftedByteNotSmall_kernel_certificate w B d q n y)

def packetTokenPrefixTerminalContinuationDisjointSentence {m} (w B C n t a k s : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n B).imp ((PacketAffineSyntax.affine w C n t a).imp ((PacketTokenArithmeticSyntax.largeCase w B C k s a).imp ((Formula.bot)))))).close

theorem source_packetTokenPrefixTerminalContinuationDisjoint {m} (w B C n t a k s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixTerminalContinuationDisjointSentence w B C n t a k s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenArithmeticSyntax.largeCase w B C k s a) (Context.add (PacketAffineSyntax.affine w C n t a) (Context.add (Formula.mem n B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketAffineSyntax.affine w C n t a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketTokenArithmeticSyntax.largeCase w B C k s a) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixValues.small_large_false hZ w B C n t a k s h0 h1 h2 h3

theorem packetTokenPrefixTerminalContinuationDisjoint_kernel_certificate {m} (w B C n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixTerminalContinuationDisjointSentence w B C n t a k s)) := TheoryTransport.sentence (source_packetTokenPrefixTerminalContinuationDisjoint w B C n t a k s)

theorem native_packetTokenPrefixTerminalContinuationDisjoint {m} (w B C n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixTerminalContinuationDisjointSentence w B C n t a k s)) := ZFReplay.replay (packetTokenPrefixTerminalContinuationDisjoint_kernel_certificate w B C n t a k s)

def packetTokenPrefixTerminalInverseSentence {m} (w B C n t a k s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.mem n B).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenAcceptedSyntax.accepted w k s a).imp (((Formula.equal n k).conj (.equal t s))))))))).close

theorem source_packetTokenPrefixTerminalInverse {m} (w B C n t a k s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixTerminalInverseSentence w B C n t a k s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w k s a) (Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (Formula.mem n B) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (Formula.mem n B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (PacketTokenAcceptedSyntax.accepted w k s a) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixPoint.small_point hZ w B C n t a k s h0 h1 h2 h3 h4 h5

theorem packetTokenPrefixTerminalInverse_kernel_certificate {m} (w B C n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixTerminalInverseSentence w B C n t a k s)) := TheoryTransport.sentence (source_packetTokenPrefixTerminalInverse w B C n t a k s)

theorem native_packetTokenPrefixTerminalInverse {m} (w B C n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixTerminalInverseSentence w B C n t a k s)) := ZFReplay.replay (packetTokenPrefixTerminalInverse_kernel_certificate w B C n t a k s)

def packetTokenPrefixLargeWitnessInverseSentence {m} (w B C n d q t a k s : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((PacketTokenPrefixSyntax.property w q).imp ((PacketTokenArithmeticSyntax.largeCase w B C n t a).imp ((PacketTokenArithmeticSyntax.largeCase w B C k s a).imp (((Formula.equal n k).conj (.equal t s)))))))).close

theorem source_packetTokenPrefixLargeWitnessInverse {m} (w B C n d q t a k s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixLargeWitnessInverseSentence w B C n d q t a k s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenArithmeticSyntax.largeCase w B C k s a) (Context.add (PacketTokenArithmeticSyntax.largeCase w B C n t a) (Context.add (PacketTokenPrefixSyntax.property w q) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketTokenPrefixSyntax.property w q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketTokenArithmeticSyntax.largeCase w B C n t a) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketTokenArithmeticSyntax.largeCase w B C k s a) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixPoint.large_cases_unique hZ w B C n d q t a k s h0 h1 h2 h3 h4

theorem packetTokenPrefixLargeWitnessInverse_kernel_certificate {m} (w B C n d q t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixLargeWitnessInverseSentence w B C n d q t a k s)) := TheoryTransport.sentence (source_packetTokenPrefixLargeWitnessInverse w B C n d q t a k s)

theorem native_packetTokenPrefixLargeWitnessInverse {m} (w B C n d q t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixLargeWitnessInverseSentence w B C n d q t a k s)) := ZFReplay.replay (packetTokenPrefixLargeWitnessInverse_kernel_certificate w B C n d q t a k s)

def packetTokenPrefixAllQuotientInductionSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (PacketTokenPrefixSyntax.property w.castSucc (Fin.last m)))))))).close

theorem source_packetTokenPrefixAllQuotientInduction {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixAllQuotientInductionSentence w B C) := by
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
  exact PacketTokenPrefixInduction.all_property hZ w B C h0 h1 h2

theorem packetTokenPrefixAllQuotientInduction_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixAllQuotientInductionSentence w B C)) := TheoryTransport.sentence (source_packetTokenPrefixAllQuotientInduction w B C)

theorem native_packetTokenPrefixAllQuotientInduction {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixAllQuotientInductionSentence w B C)) := ZFReplay.replay (packetTokenPrefixAllQuotientInduction_kernel_certificate w B C)

def packetTokenPrefixAllAtRadicesSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTokenPrefixLawSyntax.allLaw w))))).close

theorem source_packetTokenPrefixAllAtRadices {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixAllAtRadicesSentence w B C) := by
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
  exact PacketTokenPrefixLaws.all_law_at hZ w B C h0 h1 h2

theorem packetTokenPrefixAllAtRadices_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixAllAtRadicesSentence w B C)) := TheoryTransport.sentence (source_packetTokenPrefixAllAtRadices w B C)

theorem native_packetTokenPrefixAllAtRadices {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixAllAtRadicesSentence w B C)) := ZFReplay.replay (packetTokenPrefixAllAtRadices_kernel_certificate w B C)

def packetTokenPrefixAllInternalOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenPrefixLawSyntax.allLaw w))).close

theorem source_packetTokenPrefixAllInternalOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixAllInternalOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixLaws.all_law hZ w h0

theorem packetTokenPrefixAllInternalOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixAllInternalOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetTokenPrefixAllInternalOnlyOmega w)

theorem native_packetTokenPrefixAllInternalOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixAllInternalOnlyOmegaSentence w)) := ZFReplay.replay (packetTokenPrefixAllInternalOnlyOmega_kernel_certificate w)

def packetTokenPrefixJointInverseOnlyOmegaSentence {m} (w n t a k s : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenAcceptedSyntax.accepted w k s a).imp (((Formula.equal n k).conj (.equal t s)))))).close

theorem source_packetTokenPrefixJointInverseOnlyOmega {m} (w n t a k s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixJointInverseOnlyOmegaSentence w n t a k s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w k s a) (Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTokenAcceptedSyntax.accepted w k s a) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixLaws.unique hZ w n t a k s h0 h1 h2

theorem packetTokenPrefixJointInverseOnlyOmega_kernel_certificate {m} (w n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixJointInverseOnlyOmegaSentence w n t a k s)) := TheoryTransport.sentence (source_packetTokenPrefixJointInverseOnlyOmega w n t a k s)

theorem native_packetTokenPrefixJointInverseOnlyOmega {m} (w n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixJointInverseOnlyOmegaSentence w n t a k s)) := ZFReplay.replay (packetTokenPrefixJointInverseOnlyOmega_kernel_certificate w n t a k s)

def packetTokenPrefixInputOnlyOmegaSentence {m} (w n t a k s : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenAcceptedSyntax.accepted w k s a).imp ((Formula.equal n k))))).close

theorem source_packetTokenPrefixInputOnlyOmega {m} (w n t a k s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixInputOnlyOmegaSentence w n t a k s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w k s a) (Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTokenAcceptedSyntax.accepted w k s a) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixLaws.input_unique hZ w n t a k s h0 h1 h2

theorem packetTokenPrefixInputOnlyOmega_kernel_certificate {m} (w n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixInputOnlyOmegaSentence w n t a k s)) := TheoryTransport.sentence (source_packetTokenPrefixInputOnlyOmega w n t a k s)

theorem native_packetTokenPrefixInputOnlyOmega {m} (w n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixInputOnlyOmegaSentence w n t a k s)) := ZFReplay.replay (packetTokenPrefixInputOnlyOmega_kernel_certificate w n t a k s)

def packetTokenPrefixTailOnlyOmegaSentence {m} (w n t a k s : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenAcceptedSyntax.accepted w k s a).imp ((Formula.equal t s))))).close

theorem source_packetTokenPrefixTailOnlyOmega {m} (w n t a k s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixTailOnlyOmegaSentence w n t a k s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w k s a) (Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTokenAcceptedSyntax.accepted w k s a) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixLaws.tail_unique hZ w n t a k s h0 h1 h2

theorem packetTokenPrefixTailOnlyOmega_kernel_certificate {m} (w n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixTailOnlyOmegaSentence w n t a k s)) := TheoryTransport.sentence (source_packetTokenPrefixTailOnlyOmega w n t a k s)

theorem native_packetTokenPrefixTailOnlyOmega {m} (w n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixTailOnlyOmegaSentence w n t a k s)) := ZFReplay.replay (packetTokenPrefixTailOnlyOmega_kernel_certificate w n t a k s)

def packetTokenPrefixActualFiberIffOnlyOmegaSentence {m} (w n t a k s : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp (((PacketTokenAcceptedSyntax.accepted w k s a).iff ((Formula.equal n k).conj (.equal t s)))))).close

theorem source_packetTokenPrefixActualFiberIffOnlyOmega {m} (w n t a k s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixActualFiberIffOnlyOmegaSentence w n t a k s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixLaws.fiber_iff hZ w n t a k s h0 h1

theorem packetTokenPrefixActualFiberIffOnlyOmega_kernel_certificate {m} (w n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixActualFiberIffOnlyOmegaSentence w n t a k s)) := TheoryTransport.sentence (source_packetTokenPrefixActualFiberIffOnlyOmega w n t a k s)

theorem native_packetTokenPrefixActualFiberIffOnlyOmega {m} (w n t a k s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixActualFiberIffOnlyOmegaSentence w n t a k s)) := ZFReplay.replay (packetTokenPrefixActualFiberIffOnlyOmega_kernel_certificate w n t a k s)

def packetTokenPrefixOutputIffOnlyOmegaSentence {m} (w n t a k s b : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenAcceptedSyntax.accepted w k s b).imp (((Formula.equal a b).iff ((Formula.equal n k).conj (.equal t s))))))).close

theorem source_packetTokenPrefixOutputIffOnlyOmega {m} (w n t a k s b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenPrefixOutputIffOnlyOmegaSentence w n t a k s b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w k s b) (Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTokenAcceptedSyntax.accepted w k s b) := .hyp (Or.inl rfl)
  exact PacketTokenPrefixLaws.output_iff hZ w n t a k s b h0 h1 h2

theorem packetTokenPrefixOutputIffOnlyOmega_kernel_certificate {m} (w n t a k s b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenPrefixOutputIffOnlyOmegaSentence w n t a k s b)) := TheoryTransport.sentence (source_packetTokenPrefixOutputIffOnlyOmega w n t a k s b)

theorem native_packetTokenPrefixOutputIffOnlyOmega {m} (w n t a k s b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenPrefixOutputIffOnlyOmegaSentence w n t a k s b)) := ZFReplay.replay (packetTokenPrefixOutputIffOnlyOmega_kernel_certificate w n t a k s b)

end PPAC.Migration.Internal.ObjectPacketTokenPrefix
