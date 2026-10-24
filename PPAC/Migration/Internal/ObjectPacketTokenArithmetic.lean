import PPAC.Migration.Internal.PacketTokenArithmeticSystem

/-! Actual token root fields and all-internal exact arithmetic recursion with canonical and root witnesses discharged; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketTokenArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetTokenRootSmallFieldsIffSentence {m} (w B V n t a r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenSyntax.row w n t a r).imp (((PacketTokenApplicationSyntax.smallOutcome w B V r).iff (PacketTokenRootSyntax.smallCase w B V n t a))))).close

theorem source_packetTokenRootSmallFieldsIff {m} (w B V n t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenRootSmallFieldsIffSentence w B V n t a r) := by
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
  exact PacketTokenRootSmall.small_iff hZ w B V n t a r h0 h1

theorem packetTokenRootSmallFieldsIff_kernel_certificate {m} (w B V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenRootSmallFieldsIffSentence w B V n t a r)) := TheoryTransport.sentence (source_packetTokenRootSmallFieldsIff w B V n t a r)

theorem native_packetTokenRootSmallFieldsIff {m} (w B V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenRootSmallFieldsIffSentence w B V n t a r)) := ZFReplay.replay (packetTokenRootSmallFieldsIff_kernel_certificate w B V n t a r)

def packetTokenRootLargeFieldsIffSentence {m} (w B V n t a r : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenSyntax.row w n t a r).imp (((PacketTokenApplicationSyntax.largeOutcome w B V r).iff (PacketTokenRootSyntax.largeCase w B V n t a))))).close

theorem source_packetTokenRootLargeFieldsIff {m} (w B V n t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenRootLargeFieldsIffSentence w B V n t a r) := by
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
  exact PacketTokenRootLarge.large_iff hZ w B V n t a r h0 h1

theorem packetTokenRootLargeFieldsIff_kernel_certificate {m} (w B V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenRootLargeFieldsIffSentence w B V n t a r)) := TheoryTransport.sentence (source_packetTokenRootLargeFieldsIff w B V n t a r)

theorem native_packetTokenRootLargeFieldsIff {m} (w B V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenRootLargeFieldsIffSentence w B V n t a r)) := ZFReplay.replay (packetTokenRootLargeFieldsIff_kernel_certificate w B V n t a r)

def packetTokenSpecifiedRootConditionEquationSentence {m} (w B C V n t a r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp ((PacketTokenSyntax.row w n t a r).imp (((PacketTraceSyntax.condition w r).iff (PacketTokenRootSyntax.criterion w B V n t a)))))))).close

theorem source_packetTokenSpecifiedRootConditionEquation {m} (w B C V n t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenSpecifiedRootConditionEquationSentence w B C V n t a r) := by
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
  exact PacketTokenRootEquation.condition_iff hZ w B C V n t a r h0 h1 h2 h3 h4

theorem packetTokenSpecifiedRootConditionEquation_kernel_certificate {m} (w B C V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenSpecifiedRootConditionEquationSentence w B C V n t a r)) := TheoryTransport.sentence (source_packetTokenSpecifiedRootConditionEquation w B C V n t a r)

theorem native_packetTokenSpecifiedRootConditionEquation {m} (w B C V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenSpecifiedRootConditionEquationSentence w B C V n t a r)) := ZFReplay.replay (packetTokenSpecifiedRootConditionEquation_kernel_certificate w B C V n t a r)

def packetTokenSpecifiedRootMemberEquationSentence {m} (w B C V n t a r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp ((PacketTokenSyntax.row w n t a r).imp (((Formula.mem r V).iff (PacketTokenRootSyntax.criterion w B V n t a)))))))).close

theorem source_packetTokenSpecifiedRootMemberEquation {m} (w B C V n t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenSpecifiedRootMemberEquationSentence w B C V n t a r) := by
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
  exact PacketTokenRootEquation.member_iff hZ w B C V n t a r h0 h1 h2 h3 h4

theorem packetTokenSpecifiedRootMemberEquation_kernel_certificate {m} (w B C V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenSpecifiedRootMemberEquationSentence w B C V n t a r)) := TheoryTransport.sentence (source_packetTokenSpecifiedRootMemberEquation w B C V n t a r)

theorem native_packetTokenSpecifiedRootMemberEquation {m} (w B C V n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenSpecifiedRootMemberEquationSentence w B C V n t a r)) := ZFReplay.replay (packetTokenSpecifiedRootMemberEquation_kernel_certificate w B C V n t a r)

def packetTokenCanonicalEntryActualAcceptanceIffSentence {m} (tag : Nat) (w V n t a : Fin m) : Source.Sentence := ((PacketTraceCore.value w V).imp (((PacketTokenSyntax.tagEntry tag w V n t a).iff (PacketTokenAcceptedSyntax.tagAccepted tag w n t a)))).close

theorem source_packetTokenCanonicalEntryActualAcceptanceIff {m} (tag : Nat) (w V n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalEntryActualAcceptanceIffSentence tag w V n t a) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketTokenCanonicalEntry.entry_iff tag w V n t a h0

theorem packetTokenCanonicalEntryActualAcceptanceIff_kernel_certificate {m} (tag : Nat) (w V n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalEntryActualAcceptanceIffSentence tag w V n t a)) := TheoryTransport.sentence (source_packetTokenCanonicalEntryActualAcceptanceIff tag w V n t a)

theorem native_packetTokenCanonicalEntryActualAcceptanceIff {m} (tag : Nat) (w V n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalEntryActualAcceptanceIffSentence tag w V n t a)) := ZFReplay.replay (packetTokenCanonicalEntryActualAcceptanceIff_kernel_certificate tag w V n t a)

def packetTokenCanonicalEntryAffineIffSentence {m} (wide : Bool) (w B V d q n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketTraceCore.value w V).imp (((PacketTokenSyntax.tagEntry (PacketAffineRuleData.relation wide) w V d q n).iff (PacketAffineSyntax.affine w B d q n)))))).close

theorem source_packetTokenCanonicalEntryAffineIff {m} (wide : Bool) (w B V d q n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenCanonicalEntryAffineIffSentence wide w B V d q n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketTokenCanonicalEntry.affine_entry_iff hZ wide w B V d q n h0 h1 h2

theorem packetTokenCanonicalEntryAffineIff_kernel_certificate {m} (wide : Bool) (w B V d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenCanonicalEntryAffineIffSentence wide w B V d q n)) := TheoryTransport.sentence (source_packetTokenCanonicalEntryAffineIff wide w B V d q n)

theorem native_packetTokenCanonicalEntryAffineIff {m} (wide : Bool) (w B V d q n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenCanonicalEntryAffineIffSentence wide w B V d q n)) := ZFReplay.replay (packetTokenCanonicalEntryAffineIff_kernel_certificate wide w B V d q n)

def packetTokenZeroGuardFromNonzeroQuotientSentence {m} (w z q : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((Formula.mem q w).imp (((empty q).neg).imp ((Formula.mem z q)))))).close

theorem source_packetTokenZeroGuardFromNonzeroQuotient {m} (w z q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenZeroGuardFromNonzeroQuotientSentence w z q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((empty q).neg) (Context.add (Formula.mem q w) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem q w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ ((empty q).neg) := .hyp (Or.inl rfl)
  exact PacketTokenArithmeticBridge.zero_member hZ w z q h0 h1 h2 h3

theorem packetTokenZeroGuardFromNonzeroQuotient_kernel_certificate {m} (w z q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenZeroGuardFromNonzeroQuotientSentence w z q)) := TheoryTransport.sentence (source_packetTokenZeroGuardFromNonzeroQuotient w z q)

theorem native_packetTokenZeroGuardFromNonzeroQuotient {m} (w z q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenZeroGuardFromNonzeroQuotientSentence w z q)) := ZFReplay.replay (packetTokenZeroGuardFromNonzeroQuotient_kernel_certificate w z q)

def packetTokenSmallExactArithmeticBridgeSentence {m} (w B C V n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp (((PacketTokenRootSyntax.smallCase w B V n t a).iff (PacketTokenArithmeticSyntax.smallCase w B C n t a)))))).close

theorem source_packetTokenSmallExactArithmeticBridge {m} (w B C V n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenSmallExactArithmeticBridgeSentence w B C V n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inl rfl)
  exact PacketTokenArithmeticBridge.small_iff hZ w B C V n t a h0 h1 h2

theorem packetTokenSmallExactArithmeticBridge_kernel_certificate {m} (w B C V n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenSmallExactArithmeticBridgeSentence w B C V n t a)) := TheoryTransport.sentence (source_packetTokenSmallExactArithmeticBridge w B C V n t a)

theorem native_packetTokenSmallExactArithmeticBridge {m} (w B C V n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenSmallExactArithmeticBridgeSentence w B C V n t a)) := ZFReplay.replay (packetTokenSmallExactArithmeticBridge_kernel_certificate w B C V n t a)

def packetTokenLargeExactArithmeticBridgeSentence {m} (w B C V n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp (((PacketTokenRootSyntax.largeCase w B V n t a).iff (PacketTokenArithmeticSyntax.largeCase w B C n t a))))))).close

theorem source_packetTokenLargeExactArithmeticBridge {m} (w B C V n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenLargeExactArithmeticBridgeSentence w B C V n t a) := by
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
  exact PacketTokenArithmeticBridge.large_iff hZ w B C V n t a h0 h1 h2 h3

theorem packetTokenLargeExactArithmeticBridge_kernel_certificate {m} (w B C V n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenLargeExactArithmeticBridgeSentence w B C V n t a)) := TheoryTransport.sentence (source_packetTokenLargeExactArithmeticBridge w B C V n t a)

theorem native_packetTokenLargeExactArithmeticBridge {m} (w B C V n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenLargeExactArithmeticBridgeSentence w B C V n t a)) := ZFReplay.replay (packetTokenLargeExactArithmeticBridge_kernel_certificate w B C V n t a)

def packetTokenFullExactArithmeticBridgeSentence {m} (w B C V n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTraceCore.value w V).imp (((PacketTokenRootSyntax.criterion w B V n t a).iff (PacketTokenArithmeticSyntax.criterion w B C n t a))))))).close

theorem source_packetTokenFullExactArithmeticBridge {m} (w B C V n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenFullExactArithmeticBridgeSentence w B C V n t a) := by
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
  exact PacketTokenArithmeticBridge.criterion_iff hZ w B C V n t a h0 h1 h2 h3

theorem packetTokenFullExactArithmeticBridge_kernel_certificate {m} (w B C V n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenFullExactArithmeticBridgeSentence w B C V n t a)) := TheoryTransport.sentence (source_packetTokenFullExactArithmeticBridge w B C V n t a)

theorem native_packetTokenFullExactArithmeticBridge {m} (w B C V n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenFullExactArithmeticBridgeSentence w B C V n t a)) := ZFReplay.replay (packetTokenFullExactArithmeticBridge_kernel_certificate w B C V n t a)

def packetTokenActualAcceptanceNaturalFieldsSentence {m} (w n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three n t a))))).close

theorem source_packetTokenActualAcceptanceNaturalFields {m} (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualAcceptanceNaturalFieldsSentence w n t a) := by
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
  exact PacketTokenAcceptedNatural.accepted_environment hZ w n t a h0 h1

theorem packetTokenActualAcceptanceNaturalFields_kernel_certificate {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualAcceptanceNaturalFieldsSentence w n t a)) := TheoryTransport.sentence (source_packetTokenActualAcceptanceNaturalFields w n t a)

theorem native_packetTokenActualAcceptanceNaturalFields {m} (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualAcceptanceNaturalFieldsSentence w n t a)) := ZFReplay.replay (packetTokenActualAcceptanceNaturalFields_kernel_certificate w n t a)

def packetTokenArithmeticCriterionNaturalFieldsSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenArithmeticSyntax.criterion w B C n t a).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three n t a))))).close

theorem source_packetTokenArithmeticCriterionNaturalFields {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenArithmeticCriterionNaturalFieldsSentence w B C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenArithmeticSyntax.criterion w B C n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTokenArithmeticSyntax.criterion w B C n t a) := .hyp (Or.inl rfl)
  exact PacketTokenAcceptedNatural.criterion_environment hZ w B C n t a h0 h1

theorem packetTokenArithmeticCriterionNaturalFields_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenArithmeticCriterionNaturalFieldsSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenArithmeticCriterionNaturalFields w B C n t a)

theorem native_packetTokenArithmeticCriterionNaturalFields {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenArithmeticCriterionNaturalFieldsSentence w B C n t a)) := ZFReplay.replay (packetTokenArithmeticCriterionNaturalFields_kernel_certificate w B C n t a)

def packetTokenConditionExactArithmeticWithoutCanonicalWitnessSentence {m} (w B C n t a r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTokenSyntax.row w n t a r).imp (((PacketTraceSyntax.condition w r).iff (PacketTokenArithmeticSyntax.criterion w B C n t a))))))).close

theorem source_packetTokenConditionExactArithmeticWithoutCanonicalWitness {m} (w B C n t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenConditionExactArithmeticWithoutCanonicalWitnessSentence w B C n t a r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenSyntax.row w n t a r) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketTokenSyntax.row w n t a r) := .hyp (Or.inl rfl)
  exact PacketTokenArithmeticEquation.condition_iff hZ w B C n t a r h0 h1 h2 h3

theorem packetTokenConditionExactArithmeticWithoutCanonicalWitness_kernel_certificate {m} (w B C n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenConditionExactArithmeticWithoutCanonicalWitnessSentence w B C n t a r)) := TheoryTransport.sentence (source_packetTokenConditionExactArithmeticWithoutCanonicalWitness w B C n t a r)

theorem native_packetTokenConditionExactArithmeticWithoutCanonicalWitness {m} (w B C n t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenConditionExactArithmeticWithoutCanonicalWitnessSentence w B C n t a r)) := ZFReplay.replay (packetTokenConditionExactArithmeticWithoutCanonicalWitness_kernel_certificate w B C n t a r)

def packetTokenActualAcceptedExactArithmeticRecursionSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp (((PacketTokenAcceptedSyntax.accepted w n t a).iff (PacketTokenArithmeticSyntax.criterion w B C n t a)))))).close

theorem source_packetTokenActualAcceptedExactArithmeticRecursion {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualAcceptedExactArithmeticRecursionSentence w B C n t a) := by
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
  exact PacketTokenArithmeticEquation.accepted_iff hZ w B C n t a h0 h1 h2

theorem packetTokenActualAcceptedExactArithmeticRecursion_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualAcceptedExactArithmeticRecursionSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenActualAcceptedExactArithmeticRecursion w B C n t a)

theorem native_packetTokenActualAcceptedExactArithmeticRecursion {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualAcceptedExactArithmeticRecursionSentence w B C n t a)) := ZFReplay.replay (packetTokenActualAcceptedExactArithmeticRecursion_kernel_certificate w B C n t a)

def packetTokenLargeBranchExcludesSmallInputSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenArithmeticSyntax.largeCase w B C n t a).imp (((Formula.mem n B).neg)))).close

theorem source_packetTokenLargeBranchExcludesSmallInput {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenLargeBranchExcludesSmallInputSentence w B C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenArithmeticSyntax.largeCase w B C n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketTokenArithmeticSyntax.largeCase w B C n t a) := .hyp (Or.inl rfl)
  exact PacketTokenArithmeticProperties.large_not_small hZ w B C n t a h0 h1

theorem packetTokenLargeBranchExcludesSmallInput_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenLargeBranchExcludesSmallInputSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenLargeBranchExcludesSmallInput w B C n t a)

theorem native_packetTokenLargeBranchExcludesSmallInput {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenLargeBranchExcludesSmallInputSentence w B C n t a)) := ZFReplay.replay (packetTokenLargeBranchExcludesSmallInput_kernel_certificate w B C n t a)

def packetTokenActualSmallBranchIffSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.mem n B).imp (((PacketTokenAcceptedSyntax.accepted w n t a).iff (PacketAffineSyntax.affine w C n t a))))))).close

theorem source_packetTokenActualSmallBranchIff {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualSmallBranchIffSentence w B C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n B) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem n B) := .hyp (Or.inl rfl)
  exact PacketTokenArithmeticProperties.accepted_small_iff hZ w B C n t a h0 h1 h2 h3

theorem packetTokenActualSmallBranchIff_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualSmallBranchIffSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenActualSmallBranchIff w B C n t a)

theorem native_packetTokenActualSmallBranchIff {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualSmallBranchIffSentence w B C n t a)) := ZFReplay.replay (packetTokenActualSmallBranchIff_kernel_certificate w B C n t a)

def packetTokenActualLargeBranchIffSentence {m} (w B C n t a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp (((Formula.mem n B).neg).imp (((PacketTokenAcceptedSyntax.accepted w n t a).iff (PacketTokenArithmeticSyntax.largeCase w B C n t a))))))).close

theorem source_packetTokenActualLargeBranchIff {m} (w B C n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualLargeBranchIffSentence w B C n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n B).neg) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ ((Formula.mem n B).neg) := .hyp (Or.inl rfl)
  exact PacketTokenArithmeticProperties.accepted_large_iff hZ w B C n t a h0 h1 h2 h3

theorem packetTokenActualLargeBranchIff_kernel_certificate {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualLargeBranchIffSentence w B C n t a)) := TheoryTransport.sentence (source_packetTokenActualLargeBranchIff w B C n t a)

theorem native_packetTokenActualLargeBranchIff {m} (w B C n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualLargeBranchIffSentence w B C n t a)) := ZFReplay.replay (packetTokenActualLargeBranchIff_kernel_certificate w B C n t a)

def packetTokenActualRejectInvalidFieldSentence {m} (i : Fin 3) (w n t a : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem (SyntaxAtomSyntax.three n t a i) w).neg).imp (((PacketTokenAcceptedSyntax.accepted w n t a).neg)))).close

theorem source_packetTokenActualRejectInvalidField {m} (i : Fin 3) (w n t a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualRejectInvalidFieldSentence i w n t a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem (SyntaxAtomSyntax.three n t a i) w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem (SyntaxAtomSyntax.three n t a i) w).neg) := .hyp (Or.inl rfl)
  exact PacketTokenArithmeticProperties.reject_field hZ w n t a i h0 h1

theorem packetTokenActualRejectInvalidField_kernel_certificate {m} (i : Fin 3) (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualRejectInvalidFieldSentence i w n t a)) := TheoryTransport.sentence (source_packetTokenActualRejectInvalidField i w n t a)

theorem native_packetTokenActualRejectInvalidField {m} (i : Fin 3) (w n t a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualRejectInvalidFieldSentence i w n t a)) := ZFReplay.replay (packetTokenActualRejectInvalidField_kernel_certificate i w n t a)

def packetTokenAllInternalAcceptedArithmeticRecursionSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTokenArithmeticSystemSyntax.allLaw w B C))))).close

theorem source_packetTokenAllInternalAcceptedArithmeticRecursion {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllInternalAcceptedArithmeticRecursionSentence w B C) := by
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
  exact PacketTokenArithmeticSystem.all_law hZ w B C h0 h1 h2

theorem packetTokenAllInternalAcceptedArithmeticRecursion_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllInternalAcceptedArithmeticRecursionSentence w B C)) := TheoryTransport.sentence (source_packetTokenAllInternalAcceptedArithmeticRecursion w B C)

theorem native_packetTokenAllInternalAcceptedArithmeticRecursion {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllInternalAcceptedArithmeticRecursionSentence w B C)) := ZFReplay.replay (packetTokenAllInternalAcceptedArithmeticRecursion_kernel_certificate w B C)

def packetTokenAllInternalRootArithmeticRecursionSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTokenArithmeticSystemSyntax.allRootLaw w B C))))).close

theorem source_packetTokenAllInternalRootArithmeticRecursion {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllInternalRootArithmeticRecursionSentence w B C) := by
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
  exact PacketTokenArithmeticSystem.all_root_law hZ w B C h0 h1 h2

theorem packetTokenAllInternalRootArithmeticRecursion_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllInternalRootArithmeticRecursionSentence w B C)) := TheoryTransport.sentence (source_packetTokenAllInternalRootArithmeticRecursion w B C)

theorem native_packetTokenAllInternalRootArithmeticRecursion {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllInternalRootArithmeticRecursionSentence w B C)) := ZFReplay.replay (packetTokenAllInternalRootArithmeticRecursion_kernel_certificate w B C)

def packetTokenActualArithmeticRecursionSystemExistsSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenArithmeticSystemSyntax.existsSystem w))).close

theorem source_packetTokenActualArithmeticRecursionSystemExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualArithmeticRecursionSystemExistsSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokenArithmeticSystem.exists_system hZ w h0

theorem packetTokenActualArithmeticRecursionSystemExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualArithmeticRecursionSystemExistsSentence w)) := TheoryTransport.sentence (source_packetTokenActualArithmeticRecursionSystemExists w)

theorem native_packetTokenActualArithmeticRecursionSystemExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualArithmeticRecursionSystemExistsSentence w)) := ZFReplay.replay (packetTokenActualArithmeticRecursionSystemExists_kernel_certificate w)

end PPAC.Migration.Internal.ObjectPacketTokenArithmetic
