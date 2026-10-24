import PPAC.Migration.Internal.PacketTokenSystem

/-! Actual token matrices, complete bounded applications and all-root relational equations; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketToken
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetTokenSmallExactMatrixSentence {m} (env : Fin 3 → Fin m) (w B r V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((SyntaxNumeralSyntax.numeral 128 B).imp (((HornRuleSyntax.matrix PacketTokenRuleData.smallRule w r V env).iff (PacketTokenSyntax.small w B V (env 0) (env 1) (env 2) r)))))).close

theorem source_packetTokenSmallExactMatrix {m} (env : Fin 3 → Fin m) (w B r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenSmallExactMatrixSentence env w B r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inl rfl)
  exact PacketTokenMatrix.small_at hZ w B r V env h0 h1 h2

theorem packetTokenSmallExactMatrix_kernel_certificate {m} (env : Fin 3 → Fin m) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenSmallExactMatrixSentence env w B r V)) := TheoryTransport.sentence (source_packetTokenSmallExactMatrix env w B r V)

theorem native_packetTokenSmallExactMatrix {m} (env : Fin 3 → Fin m) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenSmallExactMatrixSentence env w B r V)) := ZFReplay.replay (packetTokenSmallExactMatrix_kernel_certificate env w B r V)

def packetTokenLargeExactMatrixAtSentence {m} (env : Fin 6 → Fin m) (w B z y r V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((empty z).imp ((NaturalAdditionSyntax.sum w (env 3) B y).imp (((HornRuleSyntax.matrix PacketTokenRuleData.largeRule w r V env).iff (PacketTokenSyntax.largeAt w B V z y r env)))))))).close

theorem source_packetTokenLargeExactMatrixAt {m} (env : Fin 6 → Fin m) (w B z y r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenLargeExactMatrixAtSentence env w B z y r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionSyntax.sum w (env 3) B y) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (NaturalAdditionSyntax.sum w (env 3) B y) := .hyp (Or.inl rfl)
  exact PacketTokenMatrix.large_at hZ w B z y r V env h0 h1 h2 h3 h4

theorem packetTokenLargeExactMatrixAt_kernel_certificate {m} (env : Fin 6 → Fin m) (w B z y r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenLargeExactMatrixAtSentence env w B z y r V)) := TheoryTransport.sentence (source_packetTokenLargeExactMatrixAt env w B z y r V)

theorem native_packetTokenLargeExactMatrixAt {m} (env : Fin 6 → Fin m) (w B z y r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenLargeExactMatrixAtSentence env w B z y r V)) := ZFReplay.replay (packetTokenLargeExactMatrixAt_kernel_certificate env w B z y r V)

def packetTokenLargeExactMatrixWitnessesDischargedSentence {m} (env : Fin 6 → Fin m) (w B r V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((SyntaxNumeralSyntax.numeral 128 B).imp (((HornRuleSyntax.matrix PacketTokenRuleData.largeRule w r V env).iff (PacketTokenSyntax.large w B V r env)))))).close

theorem source_packetTokenLargeExactMatrixWitnessesDischarged {m} (env : Fin 6 → Fin m) (w B r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenLargeExactMatrixWitnessesDischargedSentence env w B r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inl rfl)
  exact PacketTokenLocal.large_iff hZ w B r V env h0 h1 h2

theorem packetTokenLargeExactMatrixWitnessesDischarged_kernel_certificate {m} (env : Fin 6 → Fin m) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenLargeExactMatrixWitnessesDischargedSentence env w B r V)) := TheoryTransport.sentence (source_packetTokenLargeExactMatrixWitnessesDischarged env w B r V)

theorem native_packetTokenLargeExactMatrixWitnessesDischarged {m} (env : Fin 6 → Fin m) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenLargeExactMatrixWitnessesDischargedSentence env w B r V)) := ZFReplay.replay (packetTokenLargeExactMatrixWitnessesDischarged_kernel_certificate env w B r V)

def packetTokenLargeAssignmentNaturalSentence {m} (env : Fin 6 → Fin m) (w B V r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenSyntax.large w B V r env).imp ((HornExprSyntax.environmentNat 6 w env)))).close

theorem source_packetTokenLargeAssignmentNatural {m} (env : Fin 6 → Fin m) (w B V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenLargeAssignmentNaturalSentence env w B V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenSyntax.large w B V r env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTokenSyntax.large w B V r env) := .hyp (Or.inl rfl)
  exact PacketTokenNatural.large_environment hZ w B V r env h0 h1

theorem packetTokenLargeAssignmentNatural_kernel_certificate {m} (env : Fin 6 → Fin m) (w B V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenLargeAssignmentNaturalSentence env w B V r)) := TheoryTransport.sentence (source_packetTokenLargeAssignmentNatural env w B V r)

theorem native_packetTokenLargeAssignmentNatural {m} (env : Fin 6 → Fin m) (w B V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenLargeAssignmentNaturalSentence env w B V r)) := ZFReplay.replay (packetTokenLargeAssignmentNatural_kernel_certificate env w B V r)

def packetTokenCanonicalAffineEntryArithmeticSentence {m} (wide : Bool) (w B V d q n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketTraceCore.value w V).imp ((PacketTokenSyntax.tagEntry (PacketAffineRuleData.relation wide) w V d q n).imp ((PacketAffineSyntax.affine w B d q n)))))).close

theorem source_packetTokenCanonicalAffineEntryArithmetic {m} (wide : Bool) (w B V d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalAffineEntryArithmeticSentence wide w B V d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenSyntax.tagEntry (PacketAffineRuleData.relation wide) w V d q n) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketTokenSyntax.tagEntry (PacketAffineRuleData.relation wide) w V d q n) := .hyp (Or.inl rfl)
  exact PacketTokenEntryArithmetic.affine_of_entry hZ wide w B V d q n h0 h1 h2 h3

theorem packetTokenCanonicalAffineEntryArithmetic_kernel_certificate {m} (wide : Bool) (w B V d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalAffineEntryArithmeticSentence wide w B V d q n)) := TheoryTransport.sentence (source_packetTokenCanonicalAffineEntryArithmetic wide w B V d q n)

theorem native_packetTokenCanonicalAffineEntryArithmetic {m} (wide : Bool) (w B V d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalAffineEntryArithmeticSentence wide w B V d q n)) := ZFReplay.replay (packetTokenCanonicalAffineEntryArithmetic_kernel_certificate wide w B V d q n)

def packetTokenDigitBelowAffineOutputSentence {m} (w B d q n : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineSyntax.affine w B d q n).imp ((NaturalAdditionBounds.below d n)))).close

theorem source_packetTokenDigitBelowAffineOutput {m} (w B d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenDigitBelowAffineOutputSentence w B d q n) := by
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
  exact PacketTokenEntryArithmetic.digit_below_output hZ w B d q n h0 h1

theorem packetTokenDigitBelowAffineOutput_kernel_certificate {m} (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenDigitBelowAffineOutputSentence w B d q n)) := TheoryTransport.sentence (source_packetTokenDigitBelowAffineOutput w B d q n)

theorem native_packetTokenDigitBelowAffineOutput {m} (w B d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenDigitBelowAffineOutputSentence w B d q n)) := ZFReplay.replay (packetTokenDigitBelowAffineOutput_kernel_certificate w B d q n)

def packetTokenAllSixActualAssignmentBoundsAtSentence {m} (env : Fin 6 → Fin m) (w B C V z y r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp ((PacketTokenSyntax.largeAt w B V z y r env).imp ((HornExprBounds.environmentBound 6 r env))))))).close

theorem source_packetTokenAllSixActualAssignmentBoundsAt {m} (env : Fin 6 → Fin m) (w B C V z y r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllSixActualAssignmentBoundsAtSentence env w B C V z y r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenSyntax.largeAt w B V z y r env) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketTokenSyntax.largeAt w B V z y r env) := .hyp (Or.inl rfl)
  exact PacketTokenApplicationBounds.largeAt_bounds hZ w B C V z y r env h0 h1 h2 h3 h4

theorem packetTokenAllSixActualAssignmentBoundsAt_kernel_certificate {m} (env : Fin 6 → Fin m) (w B C V z y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllSixActualAssignmentBoundsAtSentence env w B C V z y r)) := TheoryTransport.sentence (source_packetTokenAllSixActualAssignmentBoundsAt env w B C V z y r)

theorem native_packetTokenAllSixActualAssignmentBoundsAt {m} (env : Fin 6 → Fin m) (w B C V z y r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllSixActualAssignmentBoundsAtSentence env w B C V z y r)) := ZFReplay.replay (packetTokenAllSixActualAssignmentBoundsAt_kernel_certificate env w B C V z y r)

def packetTokenAllSixActualAssignmentBoundsSentence {m} (env : Fin 6 → Fin m) (w B C V r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp ((PacketTokenSyntax.large w B V r env).imp ((HornExprBounds.environmentBound 6 r env))))))).close

theorem source_packetTokenAllSixActualAssignmentBounds {m} (env : Fin 6 → Fin m) (w B C V r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllSixActualAssignmentBoundsSentence env w B C V r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenSyntax.large w B V r env) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketTokenSyntax.large w B V r env) := .hyp (Or.inl rfl)
  exact PacketTokenApplicationBounds.large_bounds hZ w B C V r env h0 h1 h2 h3 h4

theorem packetTokenAllSixActualAssignmentBounds_kernel_certificate {m} (env : Fin 6 → Fin m) (w B C V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllSixActualAssignmentBoundsSentence env w B C V r)) := TheoryTransport.sentence (source_packetTokenAllSixActualAssignmentBounds env w B C V r)

theorem native_packetTokenAllSixActualAssignmentBounds {m} (env : Fin 6 → Fin m) (w B C V r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllSixActualAssignmentBoundsSentence env w B C V r)) := ZFReplay.replay (packetTokenAllSixActualAssignmentBounds_kernel_certificate env w B C V r)

def packetTokenSmallApplicationIffSentence {m} (w B r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp (((HornApplicationSyntax.application PacketTokenRuleData.smallRule w r V).iff (PacketTokenApplicationSyntax.smallOutcome w B V r))))).close

theorem source_packetTokenSmallApplicationIff {m} (w B r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenSmallApplicationIffSentence w B r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inl rfl)
  exact PacketTokenApplication.small_iff hZ w B r V h0 h1

theorem packetTokenSmallApplicationIff_kernel_certificate {m} (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenSmallApplicationIffSentence w B r V)) := TheoryTransport.sentence (source_packetTokenSmallApplicationIff w B r V)

theorem native_packetTokenSmallApplicationIff {m} (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenSmallApplicationIffSentence w B r V)) := ZFReplay.replay (packetTokenSmallApplicationIff_kernel_certificate w B r V)

def packetTokenLargeApplicationIffSentence {m} (w B C r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp (((HornApplicationSyntax.application PacketTokenRuleData.largeRule w r V).iff (PacketTokenApplicationSyntax.largeOutcome w B V r))))))).close

theorem source_packetTokenLargeApplicationIff {m} (w B C r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenLargeApplicationIffSentence w B C r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketTokenApplication.large_iff hZ w B C r V h0 h1 h2 h3

theorem packetTokenLargeApplicationIff_kernel_certificate {m} (w B C r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenLargeApplicationIffSentence w B C r V)) := TheoryTransport.sentence (source_packetTokenLargeApplicationIff w B C r V)

theorem native_packetTokenLargeApplicationIff {m} (w B C r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenLargeApplicationIffSentence w B C r V)) := ZFReplay.replay (packetTokenLargeApplicationIff_kernel_certificate w B C r V)

def packetTokenOriginalTwoRuleDispatchSentence {m} (w n t a r V : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenSyntax.row w n t a r).imp (((PacketTraceSyntax.step w r V).iff ((HornApplicationSyntax.application PacketTokenRuleData.smallRule w r V).disj (HornApplicationSyntax.application PacketTokenRuleData.largeRule w r V)))))).close

theorem source_packetTokenOriginalTwoRuleDispatch {m} (w n t a r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenOriginalTwoRuleDispatchSentence w n t a r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenSyntax.row w n t a r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTokenSyntax.row w n t a r) := .hyp (Or.inl rfl)
  exact PacketTokenDispatch.step_iff_applications hZ w n t a r V h0 h1

theorem packetTokenOriginalTwoRuleDispatch_kernel_certificate {m} (w n t a r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenOriginalTwoRuleDispatchSentence w n t a r V)) := TheoryTransport.sentence (source_packetTokenOriginalTwoRuleDispatch w n t a r V)

theorem native_packetTokenOriginalTwoRuleDispatch {m} (w n t a r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenOriginalTwoRuleDispatchSentence w n t a r V)) := ZFReplay.replay (packetTokenOriginalTwoRuleDispatch_kernel_certificate w n t a r V)

def packetTokenCompleteStepEquationSentence {m} (w B C n t a r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp ((PacketTokenSyntax.row w n t a r).imp (((PacketTraceSyntax.step w r V).iff ((PacketTokenApplicationSyntax.smallOutcome w B V r).disj (PacketTokenApplicationSyntax.largeOutcome w B V r))))))))).close

theorem source_packetTokenCompleteStepEquation {m} (w B C n t a r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCompleteStepEquationSentence w B C n t a r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenSyntax.row w n t a r) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketTokenSyntax.row w n t a r) := .hyp (Or.inl rfl)
  exact PacketTokenDispatch.step_iff_outcomes hZ w B C n t a r V h0 h1 h2 h3 h4

theorem packetTokenCompleteStepEquation_kernel_certificate {m} (w B C n t a r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCompleteStepEquationSentence w B C n t a r V)) := TheoryTransport.sentence (source_packetTokenCompleteStepEquation w B C n t a r V)

theorem native_packetTokenCompleteStepEquation {m} (w B C n t a r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCompleteStepEquationSentence w B C n t a r V)) := ZFReplay.replay (packetTokenCompleteStepEquation_kernel_certificate w B C n t a r V)

def packetTokenActualConditionEquationSentence {m} (w B C n t a r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp ((PacketTokenSyntax.row w n t a r).imp (((PacketTraceSyntax.condition w r).iff ((PacketTokenApplicationSyntax.smallOutcome w B V r).disj (PacketTokenApplicationSyntax.largeOutcome w B V r))))))))).close

theorem source_packetTokenActualConditionEquation {m} (w B C n t a r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualConditionEquationSentence w B C n t a r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenSyntax.row w n t a r) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketTokenSyntax.row w n t a r) := .hyp (Or.inl rfl)
  exact PacketTokenDispatch.condition_iff_outcomes hZ w B C n t a r V h0 h1 h2 h3 h4

theorem packetTokenActualConditionEquation_kernel_certificate {m} (w B C n t a r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualConditionEquationSentence w B C n t a r V)) := TheoryTransport.sentence (source_packetTokenActualConditionEquation w B C n t a r V)

theorem native_packetTokenActualConditionEquation {m} (w B C n t a r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualConditionEquationSentence w B C n t a r V)) := ZFReplay.replay (packetTokenActualConditionEquation_kernel_certificate w B C n t a r V)

def packetTokenAllInternalRootEquationSentence {m} (w B C V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp ((PacketTokenSystemSyntax.allLaw w B C V)))))).close

theorem source_packetTokenAllInternalRootEquation {m} (w B C V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllInternalRootEquationSentence w B C V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketTokenSystem.all_law hZ w B C V h0 h1 h2 h3

theorem packetTokenAllInternalRootEquation_kernel_certificate {m} (w B C V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllInternalRootEquationSentence w B C V)) := TheoryTransport.sentence (source_packetTokenAllInternalRootEquation w B C V)

theorem native_packetTokenAllInternalRootEquation {m} (w B C V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllInternalRootEquationSentence w B C V)) := ZFReplay.replay (packetTokenAllInternalRootEquation_kernel_certificate w B C V)

def packetTokenActualTwoRadixSystemExistsSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenSystemSyntax.existsSystem w))).close

theorem source_packetTokenActualTwoRadixSystemExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualTwoRadixSystemExistsSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokenSystem.exists_system hZ w h0

theorem packetTokenActualTwoRadixSystemExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualTwoRadixSystemExistsSentence w)) := TheoryTransport.sentence (source_packetTokenActualTwoRadixSystemExists w)

theorem native_packetTokenActualTwoRadixSystemExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualTwoRadixSystemExistsSentence w)) := ZFReplay.replay (packetTokenActualTwoRadixSystemExists_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketToken
