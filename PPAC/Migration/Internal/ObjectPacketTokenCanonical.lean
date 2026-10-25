import PPAC.Migration.Internal.PacketTokenCanonicalLaws

/-! Original object Tok agrees with independent canonical Prefix on all internal candidates, and with Bytes at every actual canonical list; all quotient IH and numeral witnesses are discharged. Original reader/accumulator program bridge, Basic AST, complete packet, Proof and Con remain unproved -/
namespace PPAC.Migration.Internal.ObjectPacketTokenCanonical
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetTokenCanonicalGivenConsExactByteTailIffSentence {m} (w h x s t a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((Formula.mem x w).imp ((StructuralListSyntax.consCode w h x s).imp (((PacketBytesTraceSyntax.bytes w s t a).iff (PacketBytesConsSyntax.remaining w h x t a))))))).close

theorem source_packetTokenCanonicalGivenConsExactByteTailIff {m} (w h x s t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalGivenConsExactByteTailIffSentence w h x s t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralListSyntax.consCode w h x s) (Context.add (Formula.mem x w) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h x s) := .hyp (Or.inl rfl)
  exact PacketBytesCons.cons_iff hZ w h x s t a h0 h1 h2 h3

theorem packetTokenCanonicalGivenConsExactByteTailIff_kernel_certificate {m} (w h x s t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalGivenConsExactByteTailIffSentence w h x s t a)) := TheoryTransport.sentence (source_packetTokenCanonicalGivenConsExactByteTailIff w h x s t a)

theorem native_packetTokenCanonicalGivenConsExactByteTailIff {m} (w h x s t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalGivenConsExactByteTailIffSentence w h x s t a)) := ZFReplay.replay (packetTokenCanonicalGivenConsExactByteTailIff_kernel_certificate w h x s t a)

def packetTokenCanonicalActualSingletonLastCellNormalizedSentence {m} (w h e s t a : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem h w).imp ((StructuralListSyntax.nilCode w e).imp ((StructuralListSyntax.consCode w h e s).imp ((PacketBytesTraceSyntax.bytes w s t a).imp ((PacketAffineAcceptedSyntax.accepted true w h t a))))))).close

theorem source_packetTokenCanonicalActualSingletonLastCellNormalized {m} (w h e s t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalActualSingletonLastCellNormalizedSentence w h e s t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketBytesTraceSyntax.bytes w s t a) (Context.add (StructuralListSyntax.consCode w h e s) (Context.add (StructuralListSyntax.nilCode w e) (Context.add (Formula.mem h w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem h w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (StructuralListSyntax.nilCode w e) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralListSyntax.consCode w h e s) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketBytesTraceSyntax.bytes w s t a) := .hyp (Or.inl rfl)
  exact PacketBytesCons.singleton hZ w h e s t a h0 h1 h2 h3 h4

theorem packetTokenCanonicalActualSingletonLastCellNormalized_kernel_certificate {m} (w h e s t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalActualSingletonLastCellNormalizedSentence w h e s t a)) := TheoryTransport.sentence (source_packetTokenCanonicalActualSingletonLastCellNormalized w h e s t a)

theorem native_packetTokenCanonicalActualSingletonLastCellNormalized {m} (w h e s t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalActualSingletonLastCellNormalizedSentence w h e s t a)) := ZFReplay.replay (packetTokenCanonicalActualSingletonLastCellNormalized_kernel_certificate w h e s t a)

def packetTokenCanonicalIndependentPrefixExactArithmeticRecursionSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp (((PacketVarintPrefixSyntax.prefixCode w n t a).iff (PacketVarintPrefixRecursionSyntax.criterion w B C n t a)))))).close

theorem source_packetTokenCanonicalIndependentPrefixExactArithmeticRecursion {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalIndependentPrefixExactArithmeticRecursionSentence w B C n t a) := by
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
  exact PacketVarintPrefixEquation.prefix_iff hZ w B C n t a h0 h1 h2

theorem packetTokenCanonicalIndependentPrefixExactArithmeticRecursion_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalIndependentPrefixExactArithmeticRecursionSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenCanonicalIndependentPrefixExactArithmeticRecursion w B C n t a)

theorem native_packetTokenCanonicalIndependentPrefixExactArithmeticRecursion {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalIndependentPrefixExactArithmeticRecursionSentence w B C n t a)) := ZFReplay.replay (packetTokenCanonicalIndependentPrefixExactArithmeticRecursion_kernel_certificate w B C n t a)

def packetTokenCanonicalAllInternalIndependentPrefixRecursionSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketVarintPrefixRecursionSyntax.allLaw w B C))))).close

theorem source_packetTokenCanonicalAllInternalIndependentPrefixRecursion {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalAllInternalIndependentPrefixRecursionSentence w B C) := by
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
  exact PacketVarintPrefixEquation.all_law hZ w B C h0 h1 h2

theorem packetTokenCanonicalAllInternalIndependentPrefixRecursion_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalAllInternalIndependentPrefixRecursionSentence w B C)) := TheoryTransport.sentence (source_packetTokenCanonicalAllInternalIndependentPrefixRecursion w B C)

theorem native_packetTokenCanonicalAllInternalIndependentPrefixRecursion {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalAllInternalIndependentPrefixRecursionSentence w B C)) := ZFReplay.replay (packetTokenCanonicalAllInternalIndependentPrefixRecursion_kernel_certificate w B C)

def packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIHSentence {m} (w B n d q t u : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((PacketTokenCanonicalSyntax.earlier w n).imp ((PacketAffineSyntax.affine w B d q n).imp (((empty q).neg).imp ((PacketTokenCanonicalSyntax.agreement w q t u))))))).close

theorem source_packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIH {m} (w B n d q t u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIHSentence w B n d q t u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((empty q).neg) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (PacketTokenCanonicalSyntax.earlier w n) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketTokenCanonicalSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ ((empty q).neg) := .hyp (Or.inl rfl)
  exact PacketTokenCanonicalStep.below_agreement hZ w B n d q t u h0 h1 h2 h3 h4

theorem packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIH_kernel_certificate {m} (w B n d q t u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIHSentence w B n d q t u)) := TheoryTransport.sentence (source_packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIH w B n d q t u)

theorem native_packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIH {m} (w B n d q t u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIHSentence w B n d q t u)) := ZFReplay.replay (packetTokenCanonicalStrictActualQuotientAuthorizesAgreementIH_kernel_certificate w B n d q t u)

def packetTokenCanonicalFullOriginalAndIndependentCriteriaAgreeSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((PacketTokenCanonicalSyntax.earlier w n).imp (((PacketTokenArithmeticSyntax.criterion w B C n t a).iff (PacketVarintPrefixRecursionSyntax.criterion w B C n t a)))))).close

theorem source_packetTokenCanonicalFullOriginalAndIndependentCriteriaAgree {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalFullOriginalAndIndependentCriteriaAgreeSentence w B C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenCanonicalSyntax.earlier w n) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTokenCanonicalSyntax.earlier w n) := .hyp (Or.inl rfl)
  exact PacketTokenCanonicalStep.criterion_iff hZ w B C n t a h0 h1 h2

theorem packetTokenCanonicalFullOriginalAndIndependentCriteriaAgree_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalFullOriginalAndIndependentCriteriaAgreeSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenCanonicalFullOriginalAndIndependentCriteriaAgree w B C n t a)

theorem native_packetTokenCanonicalFullOriginalAndIndependentCriteriaAgree {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalFullOriginalAndIndependentCriteriaAgreeSentence w B C n t a)) := ZFReplay.replay (packetTokenCanonicalFullOriginalAndIndependentCriteriaAgree_kernel_certificate w B C n t a)

def packetTokenCanonicalWholeActualTokenPrefixAgreementStepSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTokenCanonicalSyntax.earlier w n).imp ((PacketTokenCanonicalSyntax.agreement w n t a)))))).close

theorem source_packetTokenCanonicalWholeActualTokenPrefixAgreementStep {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalWholeActualTokenPrefixAgreementStepSentence w B C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenCanonicalSyntax.earlier w n) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketTokenCanonicalSyntax.earlier w n) := .hyp (Or.inl rfl)
  exact PacketTokenCanonicalStep.point hZ w B C n t a h0 h1 h2 h3

theorem packetTokenCanonicalWholeActualTokenPrefixAgreementStep_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalWholeActualTokenPrefixAgreementStepSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenCanonicalWholeActualTokenPrefixAgreementStep w B C n t a)

theorem native_packetTokenCanonicalWholeActualTokenPrefixAgreementStep {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalWholeActualTokenPrefixAgreementStepSentence w B C n t a)) := ZFReplay.replay (packetTokenCanonicalWholeActualTokenPrefixAgreementStep_kernel_certificate w B C n t a)

def packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischargedSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTokenCanonicalSyntax.allProperties w))))).close

theorem source_packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischarged {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischargedSentence w B C) := by
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
  exact PacketTokenCanonicalInduction.all_properties_at hZ w B C h0 h1 h2

theorem packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischarged_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischargedSentence w B C)) := TheoryTransport.sentence (source_packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischarged w B C)

theorem native_packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischarged {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischargedSentence w B C)) := ZFReplay.replay (packetTokenCanonicalOriginalFoundationSeparationAgreementIHDischarged_kernel_certificate w B C)

def packetTokenCanonicalAllAgreementPropertiesOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenCanonicalSyntax.allProperties w))).close

theorem source_packetTokenCanonicalAllAgreementPropertiesOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalAllAgreementPropertiesOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokenCanonicalLiterals.all_properties hZ w h0

theorem packetTokenCanonicalAllAgreementPropertiesOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalAllAgreementPropertiesOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetTokenCanonicalAllAgreementPropertiesOnlyOmega w)

theorem native_packetTokenCanonicalAllAgreementPropertiesOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalAllAgreementPropertiesOnlyOmegaSentence w)) := ZFReplay.replay (packetTokenCanonicalAllAgreementPropertiesOnlyOmega_kernel_certificate w)

def packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmegaSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenCanonicalSyntax.agreement w n t a))).close

theorem source_packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmega {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmegaSentence w n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokenCanonicalLaws.actual_iff hZ w n t a h0

theorem packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmega_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmegaSentence w n t a)) := TheoryTransport.sentence (source_packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmega w n t a)

theorem native_packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmega {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmegaSentence w n t a)) := ZFReplay.replay (packetTokenCanonicalActualTokIffIndependentPrefixOnlyOmega_kernel_certificate w n t a)

def packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmegaSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenCanonicalSyntax.allLaw w))).close

theorem source_packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmega {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmegaSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokenCanonicalLaws.all_law hZ w h0

theorem packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmega_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmegaSentence w)) := TheoryTransport.sentence (source_packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmega w)

theorem native_packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmega {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmegaSentence w)) := ZFReplay.replay (packetTokenCanonicalAllInternalActualTokPrefixAgreementOnlyOmega_kernel_certificate w)

def packetTokenCanonicalPrefixAtAnyActualCanonicalListSentence {m} (w n s t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintSyntax.canonical w n s).imp ((PacketVarintPrefixSyntax.prefixCode w n t a).imp ((PacketBytesTraceSyntax.bytes w s t a))))).close

theorem source_packetTokenCanonicalPrefixAtAnyActualCanonicalList {m} (w n s t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalPrefixAtAnyActualCanonicalListSentence w n s t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketVarintPrefixSyntax.prefixCode w n t a) (Context.add (PacketVarintSyntax.canonical w n s) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketVarintSyntax.canonical w n s) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketVarintPrefixSyntax.prefixCode w n t a) := .hyp (Or.inl rfl)
  exact PacketTokenCanonicalLaws.prefix_at_given_list hZ w n s t a h0 h1 h2

theorem packetTokenCanonicalPrefixAtAnyActualCanonicalList_kernel_certificate {m} (w n s t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalPrefixAtAnyActualCanonicalListSentence w n s t a)) := TheoryTransport.sentence (source_packetTokenCanonicalPrefixAtAnyActualCanonicalList w n s t a)

theorem native_packetTokenCanonicalPrefixAtAnyActualCanonicalList {m} (w n s t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalPrefixAtAnyActualCanonicalListSentence w n s t a)) := ZFReplay.replay (packetTokenCanonicalPrefixAtAnyActualCanonicalList_kernel_certificate w n s t a)

def packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalListSentence {m} (w n s t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketVarintSyntax.canonical w n s).imp (((PacketTokenAcceptedSyntax.accepted w n t a).iff (PacketBytesTraceSyntax.bytes w s t a))))).close

theorem source_packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalList {m} (w n s t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalListSentence w n s t a) := by
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
  exact PacketTokenCanonicalLaws.at_canonical_list hZ w n s t a h0 h1

theorem packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalList_kernel_certificate {m} (w n s t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalListSentence w n s t a)) := TheoryTransport.sentence (source_packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalList w n s t a)

theorem native_packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalList {m} (w n s t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalListSentence w n s t a)) := ZFReplay.replay (packetTokenCanonicalActualTokIffBytesAtAnyActualCanonicalList_kernel_certificate w n s t a)

end PPAC.Migration.Internal.ObjectPacketTokenCanonical
