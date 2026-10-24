import PPAC.Migration.Internal.PacketDivisionDescentAccepted

/-! All internal quotient descent, exact stopping thresholds and object quotient induction schemas; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketDescent
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetDescentOneProductSentence {m} (w a e : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem a w).imp ((SyntaxNumeralSyntax.numeral 1 e).imp ((NaturalMultiplicationSyntax.product w e a a))))).close

theorem source_packetDescentOneProduct {m} (w a e : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentOneProductSentence w a e) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 1 e) (Context.add (Formula.mem a w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem a w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 1 e) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentOrder.one_product hZ w a e h0 h1 h2

theorem packetDescentOneProduct_kernel_certificate {m} (w a e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentOneProductSentence w a e)) := TheoryTransport.sentence (source_packetDescentOneProduct w a e)

theorem native_packetDescentOneProduct {m} (w a e : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentOneProductSentence w a e)) := ZFReplay.replay (packetDescentOneProduct_kernel_certificate w a e)

def packetDescentProductBoundsSentence {m} (wide : Bool) (w B q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((Formula.mem q w).imp ((NaturalMultiplicationSyntax.product w B q v).imp (((NaturalAdditionBounds.below q v).conj ((empty q).neg.imp (.mem q v)))))))).close

theorem source_packetDescentProductBounds {m} (wide : Bool) (w B q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentProductBoundsSentence wide w B q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalMultiplicationSyntax.product w B q v) (Context.add (Formula.mem q w) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem q w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (NaturalMultiplicationSyntax.product w B q v) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentOrder.product_bounds hZ wide w B q v h0 h1 h2 h3

theorem packetDescentProductBounds_kernel_certificate {m} (wide : Bool) (w B q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentProductBoundsSentence wide w B q v)) := TheoryTransport.sentence (source_packetDescentProductBounds wide w B q v)

theorem native_packetDescentProductBounds {m} (wide : Bool) (w B q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentProductBoundsSentence wide w B q v)) := ZFReplay.replay (packetDescentProductBounds_kernel_certificate wide w B q v)

def packetDescentQuotientBoundsSentence {m} (wide : Bool) (w B d q n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineSyntax.affine w B d q n).imp (((NaturalAdditionBounds.below q n).conj ((empty q).neg.imp (.mem q n))))))).close

theorem source_packetDescentQuotientBounds {m} (wide : Bool) (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentQuotientBoundsSentence wide w B d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentCore.quotient_bounds hZ wide w B d q n h0 h1 h2

theorem packetDescentQuotientBounds_kernel_certificate {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentQuotientBoundsSentence wide w B d q n)) := TheoryTransport.sentence (source_packetDescentQuotientBounds wide w B d q n)

theorem native_packetDescentQuotientBounds {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentQuotientBoundsSentence wide w B d q n)) := ZFReplay.replay (packetDescentQuotientBounds_kernel_certificate wide w B d q n)

def packetDescentQuotientBelowSentence {m} (wide : Bool) (w B d q n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineSyntax.affine w B d q n).imp ((NaturalAdditionBounds.below q n))))).close

theorem source_packetDescentQuotientBelow {m} (wide : Bool) (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentQuotientBelowSentence wide w B d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentCore.quotient_below hZ wide w B d q n h0 h1 h2

theorem packetDescentQuotientBelow_kernel_certificate {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentQuotientBelowSentence wide w B d q n)) := TheoryTransport.sentence (source_packetDescentQuotientBelow wide w B d q n)

theorem native_packetDescentQuotientBelow {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentQuotientBelowSentence wide w B d q n)) := ZFReplay.replay (packetDescentQuotientBelow_kernel_certificate wide w B d q n)

def packetDescentNonzeroOutputStrictSentence {m} (wide : Bool) (w B d q n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineSyntax.affine w B d q n).imp (((empty n).neg).imp ((Formula.mem q n)))))).close

theorem source_packetDescentNonzeroOutputStrict {m} (wide : Bool) (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentNonzeroOutputStrictSentence wide w B d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((empty n).neg) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ ((empty n).neg) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentCore.quotient_strict hZ wide w B d q n h0 h1 h2 h3

theorem packetDescentNonzeroOutputStrict_kernel_certificate {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentNonzeroOutputStrictSentence wide w B d q n)) := TheoryTransport.sentence (source_packetDescentNonzeroOutputStrict wide w B d q n)

theorem native_packetDescentNonzeroOutputStrict {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentNonzeroOutputStrictSentence wide w B d q n)) := ZFReplay.replay (packetDescentNonzeroOutputStrict_kernel_certificate wide w B d q n)

def packetDescentTerminalDigitSentence {m} (w B d q n : Fin m) : Source.Sentence := ((PacketAffineSyntax.affine w B d q n).imp ((empty q).imp ((Formula.equal n d)))).close

theorem source_packetDescentTerminalDigit {m} (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentTerminalDigitSentence w B d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty q) (Context.add (PacketAffineSyntax.affine w B d q n) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty q) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentCore.terminal_digit w B d q n h0 h1

theorem packetDescentTerminalDigit_kernel_certificate {m} (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentTerminalDigitSentence w B d q n)) := TheoryTransport.sentence (source_packetDescentTerminalDigit w B d q n)

theorem native_packetDescentTerminalDigit {m} (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentTerminalDigitSentence w B d q n)) := ZFReplay.replay (packetDescentTerminalDigit_kernel_certificate w B d q n)

def packetDescentExactStoppingThresholdSentence {m} (w B d q n : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp (((empty q).iff (.mem n B))))).close

theorem source_packetDescentExactStoppingThreshold {m} (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentExactStoppingThresholdSentence w B d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentCore.terminal_iff hZ w B d q n h0 h1

theorem packetDescentExactStoppingThreshold_kernel_certificate {m} (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentExactStoppingThresholdSentence w B d q n)) := TheoryTransport.sentence (source_packetDescentExactStoppingThreshold w B d q n)

theorem native_packetDescentExactStoppingThreshold {m} (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentExactStoppingThresholdSentence w B d q n)) := ZFReplay.replay (packetDescentExactStoppingThreshold_kernel_certificate w B d q n)

def packetDescentZeroOutputExactFieldsSentence {m} (wide : Bool) (w B d q n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineSyntax.affine w B d q n).imp (((empty n).iff ((empty d).conj (empty q))))))).close

theorem source_packetDescentZeroOutputExactFields {m} (wide : Bool) (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentZeroOutputExactFieldsSentence wide w B d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentCore.zero_output hZ wide w B d q n h0 h1 h2

theorem packetDescentZeroOutputExactFields_kernel_certificate {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentZeroOutputExactFieldsSentence wide w B d q n)) := TheoryTransport.sentence (source_packetDescentZeroOutputExactFields wide w B d q n)

theorem native_packetDescentZeroOutputExactFields {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentZeroOutputExactFieldsSentence wide w B d q n)) := ZFReplay.replay (packetDescentZeroOutputExactFields_kernel_certificate wide w B d q n)

def packetDescentLargeOutputNonzeroSentence {m} (wide : Bool) (B n : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((Formula.mem n B).neg).imp (((empty n).neg)))).close

theorem source_packetDescentLargeOutputNonzero {m} (wide : Bool) (B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentLargeOutputNonzeroSentence wide B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n B).neg) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem n B).neg) := .hyp (Or.inl rfl)
  exact PacketQuotientInduction.large_nonempty hZ wide B n h0 h1

theorem packetDescentLargeOutputNonzero_kernel_certificate {m} (wide : Bool) (B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentLargeOutputNonzeroSentence wide B n)) := TheoryTransport.sentence (source_packetDescentLargeOutputNonzero wide B n)

theorem native_packetDescentLargeOutputNonzero {m} (wide : Bool) (B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentLargeOutputNonzeroSentence wide B n)) := ZFReplay.replay (packetDescentLargeOutputNonzero_kernel_certificate wide B n)

def packetDescentQuotientInductionPointSentence {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketQuotientInductionSyntax.base p ρ w B).imp ((PacketQuotientInductionSyntax.step p ρ w B).imp ((Formula.mem n w).imp ((BoundedInduction.below p ρ w n).imp ((MinimalPredicates.pred p ρ n)))))))).close

theorem source_packetDescentQuotientInductionPoint {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentQuotientInductionPointSentence wide p ρ w B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (BoundedInduction.below p ρ w n) (Context.add (Formula.mem n w) (Context.add (PacketQuotientInductionSyntax.step p ρ w B) (Context.add (PacketQuotientInductionSyntax.base p ρ w B) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (PacketQuotientInductionSyntax.base p ρ w B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PacketQuotientInductionSyntax.step p ρ w B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (BoundedInduction.below p ρ w n) := .hyp (Or.inl rfl)
  exact PacketQuotientInduction.point hZ wide p ρ w B n h0 h1 h2 h3 h4 h5

theorem packetDescentQuotientInductionPoint_kernel_certificate {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentQuotientInductionPointSentence wide p ρ w B n)) := TheoryTransport.sentence (source_packetDescentQuotientInductionPoint wide p ρ w B n)

theorem native_packetDescentQuotientInductionPoint {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentQuotientInductionPointSentence wide p ρ w B n)) := ZFReplay.replay (packetDescentQuotientInductionPoint_kernel_certificate wide p ρ w B n)

def packetDescentQuotientInductionProgressiveSentence {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketQuotientInductionSyntax.base p ρ w B).imp ((PacketQuotientInductionSyntax.step p ρ w B).imp ((BoundedInduction.progressive p ρ w)))))).close

theorem source_packetDescentQuotientInductionProgressive {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentQuotientInductionProgressiveSentence wide p ρ w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketQuotientInductionSyntax.step p ρ w B) (Context.add (PacketQuotientInductionSyntax.base p ρ w B) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketQuotientInductionSyntax.base p ρ w B) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketQuotientInductionSyntax.step p ρ w B) := .hyp (Or.inl rfl)
  exact PacketQuotientInduction.progressive hZ wide p ρ w B h0 h1 h2 h3

theorem packetDescentQuotientInductionProgressive_kernel_certificate {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentQuotientInductionProgressiveSentence wide p ρ w B)) := TheoryTransport.sentence (source_packetDescentQuotientInductionProgressive wide p ρ w B)

theorem native_packetDescentQuotientInductionProgressive {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentQuotientInductionProgressiveSentence wide p ρ w B)) := ZFReplay.replay (packetDescentQuotientInductionProgressive_kernel_certificate wide p ρ w B)

def packetDescentAllInternalQuotientInductionSentence {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketQuotientInductionSyntax.base p ρ w B).imp ((PacketQuotientInductionSyntax.step p ρ w B).imp ((BoundedInduction.holds p ρ w)))))).close

theorem source_packetDescentAllInternalQuotientInduction {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentAllInternalQuotientInductionSentence wide p ρ w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketQuotientInductionSyntax.step p ρ w B) (Context.add (PacketQuotientInductionSyntax.base p ρ w B) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketQuotientInductionSyntax.base p ρ w B) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketQuotientInductionSyntax.step p ρ w B) := .hyp (Or.inl rfl)
  exact PacketQuotientInduction.all_holds hZ wide p ρ w B h0 h1 h2 h3

theorem packetDescentAllInternalQuotientInduction_kernel_certificate {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentAllInternalQuotientInductionSentence wide p ρ w B)) := TheoryTransport.sentence (source_packetDescentAllInternalQuotientInduction wide p ρ w B)

theorem native_packetDescentAllInternalQuotientInduction {m} {k} (wide : Bool) (p : Formula (k+1)) (ρ : Fin k → Fin m) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentAllInternalQuotientInductionSentence wide p ρ w B)) := ZFReplay.replay (packetDescentAllInternalQuotientInduction_kernel_certificate wide p ρ w B)

def packetDescentAffinePropertiesSentence {m} (wide : Bool) (w B d q n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineSyntax.affine w B d q n).imp ((PacketDivisionDescentSyntax.properties w B d q n))))).close

theorem source_packetDescentAffineProperties {m} (wide : Bool) (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentAffinePropertiesSentence wide w B d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentAccepted.affine_properties hZ wide w B d q n h0 h1 h2

theorem packetDescentAffineProperties_kernel_certificate {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentAffinePropertiesSentence wide w B d q n)) := TheoryTransport.sentence (source_packetDescentAffineProperties wide w B d q n)

theorem native_packetDescentAffineProperties {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentAffinePropertiesSentence wide w B d q n)) := ZFReplay.replay (packetDescentAffineProperties_kernel_certificate wide w B d q n)

def packetDescentAffineTerminalRecursiveBranchesSentence {m} (wide : Bool) (w B d q n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineSyntax.affine w B d q n).imp ((PacketDivisionDescentSyntax.branch B d q n))))).close

theorem source_packetDescentAffineTerminalRecursiveBranches {m} (wide : Bool) (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentAffineTerminalRecursiveBranchesSentence wide w B d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentAccepted.affine_branch hZ wide w B d q n h0 h1 h2

theorem packetDescentAffineTerminalRecursiveBranches_kernel_certificate {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentAffineTerminalRecursiveBranchesSentence wide w B d q n)) := TheoryTransport.sentence (source_packetDescentAffineTerminalRecursiveBranches wide w B d q n)

theorem native_packetDescentAffineTerminalRecursiveBranches {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentAffineTerminalRecursiveBranchesSentence wide w B d q n)) := ZFReplay.replay (packetDescentAffineTerminalRecursiveBranches_kernel_certificate wide w B d q n)

def packetDescentAcceptedPropertiesSentence {m} (wide : Bool) (w B d q n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineAcceptedSyntax.accepted wide w d q n).imp (((PacketDivisionDescentSyntax.properties w B d q n).conj (PacketDivisionDescentSyntax.branch B d q n)))))).close

theorem source_packetDescentAcceptedProperties {m} (wide : Bool) (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentAcceptedPropertiesSentence wide w B d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted wide w d q n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineAcceptedSyntax.accepted wide w d q n) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentAccepted.accepted_properties hZ wide w B d q n h0 h1 h2

theorem packetDescentAcceptedProperties_kernel_certificate {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentAcceptedPropertiesSentence wide w B d q n)) := TheoryTransport.sentence (source_packetDescentAcceptedProperties wide w B d q n)

theorem native_packetDescentAcceptedProperties {m} (wide : Bool) (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentAcceptedPropertiesSentence wide w B d q n)) := ZFReplay.replay (packetDescentAcceptedProperties_kernel_certificate wide w B d q n)

def packetDescentAllInternalAcceptedLawSentence {m} (wide : Bool) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketDivisionDescentSyntax.allLaw wide w B)))).close

theorem source_packetDescentAllInternalAcceptedLaw {m} (wide : Bool) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentAllInternalAcceptedLawSentence wide w B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentAccepted.all_law hZ wide w B h0 h1

theorem packetDescentAllInternalAcceptedLaw_kernel_certificate {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentAllInternalAcceptedLawSentence wide w B)) := TheoryTransport.sentence (source_packetDescentAllInternalAcceptedLaw wide w B)

theorem native_packetDescentAllInternalAcceptedLaw {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentAllInternalAcceptedLawSentence wide w B)) := ZFReplay.replay (packetDescentAllInternalAcceptedLaw_kernel_certificate wide w B)

def packetDescentActualLiteralSystemExistsSentence {m} (wide : Bool) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketDivisionDescentSyntax.existsSystem wide w))).close

theorem source_packetDescentActualLiteralSystemExists {m} (wide : Bool) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetDescentActualLiteralSystemExistsSentence wide w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketDivisionDescentAccepted.exists_system hZ wide w h0

theorem packetDescentActualLiteralSystemExists_kernel_certificate {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetDescentActualLiteralSystemExistsSentence wide w)) := TheoryTransport.sentence (source_packetDescentActualLiteralSystemExists wide w)

theorem native_packetDescentActualLiteralSystemExists {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetDescentActualLiteralSystemExistsSentence wide w)) := ZFReplay.replay (packetDescentActualLiteralSystemExists_kernel_certificate wide w)

end PPAC.Migration.Internal.ObjectPacketDescent
