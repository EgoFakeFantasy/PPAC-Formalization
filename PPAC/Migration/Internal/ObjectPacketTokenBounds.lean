import PPAC.Migration.Internal.PacketTokenBounds

/-! Actual token quantitative bounds for all internal input, tail and output candidates; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketTokenBounds
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetTokenTwoCoordinateSumComparisonSentence {m} (w d y p r n a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem d w).imp ((Formula.mem y w).imp ((Formula.mem p w).imp ((Formula.mem r w).imp ((NaturalAdditionSyntax.sum w d p n).imp ((NaturalAdditionSyntax.sum w y r a).imp ((NaturalAdditionBounds.below d y).imp ((NaturalAdditionBounds.below p r).imp ((NaturalAdditionBounds.below n a))))))))))).close

theorem source_packetTokenTwoCoordinateSumComparison {m} (w d y p r n a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenTwoCoordinateSumComparisonSentence w d y p r n a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionBounds.below p r) (Context.add (NaturalAdditionBounds.below d y) (Context.add (NaturalAdditionSyntax.sum w y r a) (Context.add (NaturalAdditionSyntax.sum w d p n) (Context.add (Formula.mem r w) (Context.add (Formula.mem p w) (Context.add (Formula.mem y w) (Context.add (Formula.mem d w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (Formula.mem d w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (Formula.mem y w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (NaturalAdditionSyntax.sum w d p n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (NaturalAdditionSyntax.sum w y r a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (NaturalAdditionBounds.below d y) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (NaturalAdditionBounds.below p r) := .hyp (Or.inl rfl)
  exact PacketTokenBoundComparison.sum_compare hZ w d y p r n a h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem packetTokenTwoCoordinateSumComparison_kernel_certificate {m} (w d y p r n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenTwoCoordinateSumComparisonSentence w d y p r n a)) := TheoryTransport.sentence (source_packetTokenTwoCoordinateSumComparison w d y p r n a)

theorem native_packetTokenTwoCoordinateSumComparison {m} (w d y p r n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenTwoCoordinateSumComparisonSentence w d y p r n a)) := ZFReplay.replay (packetTokenTwoCoordinateSumComparison_kernel_certificate w d y p r n a)

def packetTokenTwoCoordinateProductComparisonSentence {m} (w B C q u p r : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem B w).imp ((Formula.mem C w).imp ((Formula.mem q w).imp ((Formula.mem u w).imp ((NaturalMultiplicationSyntax.product w B q p).imp ((NaturalMultiplicationSyntax.product w C u r).imp ((NaturalAdditionBounds.below B C).imp ((NaturalAdditionBounds.below q u).imp ((NaturalAdditionBounds.below p r))))))))))).close

theorem source_packetTokenTwoCoordinateProductComparison {m} (w B C q u p r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenTwoCoordinateProductComparisonSentence w B C q u p r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionBounds.below q u) (Context.add (NaturalAdditionBounds.below B C) (Context.add (NaturalMultiplicationSyntax.product w C u r) (Context.add (NaturalMultiplicationSyntax.product w B q p) (Context.add (Formula.mem u w) (Context.add (Formula.mem q w) (Context.add (Formula.mem C w) (Context.add (Formula.mem B w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (Formula.mem B w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (Formula.mem C w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (Formula.mem q w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (Formula.mem u w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (NaturalMultiplicationSyntax.product w B q p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (NaturalMultiplicationSyntax.product w C u r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (NaturalAdditionBounds.below B C) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (NaturalAdditionBounds.below q u) := .hyp (Or.inl rfl)
  exact PacketTokenBoundComparison.product_compare hZ w B C q u p r h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem packetTokenTwoCoordinateProductComparison_kernel_certificate {m} (w B C q u p r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenTwoCoordinateProductComparisonSentence w B C q u p r)) := TheoryTransport.sentence (source_packetTokenTwoCoordinateProductComparison w B C q u p r)

theorem native_packetTokenTwoCoordinateProductComparison {m} (w B C q u p r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenTwoCoordinateProductComparisonSentence w B C q u p r)) := ZFReplay.replay (packetTokenTwoCoordinateProductComparison_kernel_certificate w B C q u p r)

def packetTokenActualAffineComparisonSentence {m} (w B C d q n y u a : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((PacketAffineSyntax.affine w C y u a).imp ((NaturalAdditionBounds.below B C).imp ((NaturalAdditionBounds.below d y).imp ((NaturalAdditionBounds.below q u).imp ((NaturalAdditionBounds.below n a)))))))).close

theorem source_packetTokenActualAffineComparison {m} (w B C d q n y u a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualAffineComparisonSentence w B C d q n y u a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionBounds.below q u) (Context.add (NaturalAdditionBounds.below d y) (Context.add (NaturalAdditionBounds.below B C) (Context.add (PacketAffineSyntax.affine w C y u a) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (PacketAffineSyntax.affine w C y u a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (NaturalAdditionBounds.below B C) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (NaturalAdditionBounds.below d y) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (NaturalAdditionBounds.below q u) := .hyp (Or.inl rfl)
  exact PacketTokenBoundComparison.affine_compare hZ w B C d q n y u a h0 h1 h2 h3 h4 h5

theorem packetTokenActualAffineComparison_kernel_certificate {m} (w B C d q n y u a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualAffineComparisonSentence w B C d q n y u a)) := TheoryTransport.sentence (source_packetTokenActualAffineComparison w B C d q n y u a)

theorem native_packetTokenActualAffineComparison {m} (w B C d q n y u a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualAffineComparisonSentence w B C d q n y u a)) := ZFReplay.replay (packetTokenActualAffineComparison_kernel_certificate w B C d q n y u a)

def packetTokenSmallInputTailBoundsSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.mem n B).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenBoundsSyntax.bounds n t a))))))).close

theorem source_packetTokenSmallInputTailBounds {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenSmallInputTailBoundsSentence w B C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (Formula.mem n B) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (Formula.mem n B) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inl rfl)
  exact PacketTokenBoundsPoint.small_point hZ w B C n t a h0 h1 h2 h3 h4

theorem packetTokenSmallInputTailBounds_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenSmallInputTailBoundsSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenSmallInputTailBounds w B C n t a)

theorem native_packetTokenSmallInputTailBounds {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenSmallInputTailBoundsSentence w B C n t a)) := ZFReplay.replay (packetTokenSmallInputTailBounds_kernel_certificate w B C n t a)

def packetTokenAllInternalBoundsIHDischargedSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (PacketTokenBoundsSyntax.property w.castSucc (Fin.last m)))))))).close

theorem source_packetTokenAllInternalBoundsIHDischarged {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllInternalBoundsIHDischargedSentence w B C) := by
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
  exact PacketTokenBoundsInduction.all_property hZ w B C h0 h1 h2

theorem packetTokenAllInternalBoundsIHDischarged_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllInternalBoundsIHDischargedSentence w B C)) := TheoryTransport.sentence (source_packetTokenAllInternalBoundsIHDischarged w B C)

theorem native_packetTokenAllInternalBoundsIHDischarged {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllInternalBoundsIHDischargedSentence w B C)) := ZFReplay.replay (packetTokenAllInternalBoundsIHDischarged_kernel_certificate w B C)

def packetTokenInputTailBoundsAtRadicesSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenBoundsSyntax.bounds n t a)))))).close

theorem source_packetTokenInputTailBoundsAtRadices {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenInputTailBoundsAtRadicesSentence w B C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inl rfl)
  exact PacketTokenBoundsInduction.bounds_at hZ w B C n t a h0 h1 h2 h3

theorem packetTokenInputTailBoundsAtRadices_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenInputTailBoundsAtRadicesSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenInputTailBoundsAtRadices w B C n t a)

theorem native_packetTokenInputTailBoundsAtRadices {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenInputTailBoundsAtRadicesSentence w B C n t a)) := ZFReplay.replay (packetTokenInputTailBoundsAtRadices_kernel_certificate w B C n t a)

def packetTokenAllNumericBoundsAtRadicesSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTokenBoundsSystemSyntax.allLaw w))))).close

theorem source_packetTokenAllNumericBoundsAtRadices {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllNumericBoundsAtRadicesSentence w B C) := by
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
  exact PacketTokenBounds.all_law_at hZ w B C h0 h1 h2

theorem packetTokenAllNumericBoundsAtRadices_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllNumericBoundsAtRadicesSentence w B C)) := TheoryTransport.sentence (source_packetTokenAllNumericBoundsAtRadices w B C)

theorem native_packetTokenAllNumericBoundsAtRadices {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllNumericBoundsAtRadicesSentence w B C)) := ZFReplay.replay (packetTokenAllNumericBoundsAtRadices_kernel_certificate w B C)

def packetTokenAllInternalNumericBoundsOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenBoundsSystemSyntax.allLaw w))).close

theorem source_packetTokenAllInternalNumericBoundsOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllInternalNumericBoundsOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokenBounds.all_law hZ w h0

theorem packetTokenAllInternalNumericBoundsOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllInternalNumericBoundsOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetTokenAllInternalNumericBoundsOnlyOmega w)

theorem native_packetTokenAllInternalNumericBoundsOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllInternalNumericBoundsOnlyOmegaSentence w)) := ZFReplay.replay (packetTokenAllInternalNumericBoundsOnlyOmega_kernel_certificate w)

def packetTokenActualInputTailBoundsOnlyOmegaSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenBoundsSyntax.bounds n t a)))).close

theorem source_packetTokenActualInputTailBoundsOnlyOmega {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualInputTailBoundsOnlyOmegaSentence w n t a) := by
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
  exact PacketTokenBounds.bounds hZ w n t a h0 h1

theorem packetTokenActualInputTailBoundsOnlyOmega_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualInputTailBoundsOnlyOmegaSentence w n t a)) := TheoryTransport.sentence (source_packetTokenActualInputTailBoundsOnlyOmega w n t a)

theorem native_packetTokenActualInputTailBoundsOnlyOmega {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualInputTailBoundsOnlyOmegaSentence w n t a)) := ZFReplay.replay (packetTokenActualInputTailBoundsOnlyOmega_kernel_certificate w n t a)

def packetTokenActualInputBelowOutputSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((NaturalAdditionBounds.below n a)))).close

theorem source_packetTokenActualInputBelowOutput {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualInputBelowOutputSentence w n t a) := by
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
  exact PacketTokenBounds.input_below hZ w n t a h0 h1

theorem packetTokenActualInputBelowOutput_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualInputBelowOutputSentence w n t a)) := TheoryTransport.sentence (source_packetTokenActualInputBelowOutput w n t a)

theorem native_packetTokenActualInputBelowOutput {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualInputBelowOutputSentence w n t a)) := ZFReplay.replay (packetTokenActualInputBelowOutput_kernel_certificate w n t a)

def packetTokenActualTailBelowOutputSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((NaturalAdditionBounds.below t a)))).close

theorem source_packetTokenActualTailBelowOutput {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualTailBelowOutputSentence w n t a) := by
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
  exact PacketTokenBounds.tail_below hZ w n t a h0 h1

theorem packetTokenActualTailBelowOutput_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualTailBelowOutputSentence w n t a)) := TheoryTransport.sentence (source_packetTokenActualTailBelowOutput w n t a)

theorem native_packetTokenActualTailBelowOutput {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualTailBelowOutputSentence w n t a)) := ZFReplay.replay (packetTokenActualTailBelowOutput_kernel_certificate w n t a)

def packetTokenActualContainedInputTailBoundsSentence {m} (w n t a r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((Formula.mem r w).imp ((NaturalAdditionBounds.below a r).imp ((PacketTokenBoundsSyntax.bounds n t r)))))).close

theorem source_packetTokenActualContainedInputTailBounds {m} (w n t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualContainedInputTailBoundsSentence w n t a r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionBounds.below a r) (Context.add (Formula.mem r w) (Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem r w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (NaturalAdditionBounds.below a r) := .hyp (Or.inl rfl)
  exact PacketTokenBounds.contained_bounds hZ w n t a r h0 h1 h2 h3

theorem packetTokenActualContainedInputTailBounds_kernel_certificate {m} (w n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualContainedInputTailBoundsSentence w n t a r)) := TheoryTransport.sentence (source_packetTokenActualContainedInputTailBounds w n t a r)

theorem native_packetTokenActualContainedInputTailBounds {m} (w n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualContainedInputTailBoundsSentence w n t a r)) := ZFReplay.replay (packetTokenActualContainedInputTailBounds_kernel_certificate w n t a r)

end PPAC.Migration.Internal.ObjectPacketTokenBounds
