import PPAC.Migration.Internal.PacketTokenExecution

/-! Actual token output existence, uniqueness and exact typed fibers for all internal natural input and tail pairs; full Basic AST and varint bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketTokenExecution
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetTokenFiniteNumeralSumSentence {m} (i j : Nat) (w a b c : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral i a).imp ((SyntaxNumeralSyntax.numeral j b).imp ((SyntaxNumeralSyntax.numeral (i+j) c).imp ((NaturalAdditionSyntax.sum w a b c)))))).close

theorem source_packetTokenFiniteNumeralSum {m} (i j : Nat) (w a b c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenFiniteNumeralSumSentence i j w a b c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (i+j) c) (Context.add (SyntaxNumeralSyntax.numeral j b) (Context.add (SyntaxNumeralSyntax.numeral i a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral i a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral j b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral (i+j) c) := .hyp (Or.inl rfl)
  exact SyntaxNumeralAddition.sum_at hZ i j w a b c h0 h1 h2 h3

theorem packetTokenFiniteNumeralSum_kernel_certificate {m} (i j : Nat) (w a b c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenFiniteNumeralSumSentence i j w a b c)) := TheoryTransport.sentence (source_packetTokenFiniteNumeralSum i j w a b c)

theorem native_packetTokenFiniteNumeralSum {m} (i j : Nat) (w a b c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenFiniteNumeralSumSentence i j w a b c)) := ZFReplay.replay (packetTokenFiniteNumeralSum_kernel_certificate i j w a b c)

def packetTokenActualDouble128Sentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((NaturalAdditionSyntax.sum w B B C))))).close

theorem source_packetTokenActualDouble128 {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualDouble128Sentence w B C) := by
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
  exact PacketTokenByteBounds.radix_sum hZ w B C h0 h1 h2

theorem packetTokenActualDouble128_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualDouble128Sentence w B C)) := TheoryTransport.sentence (source_packetTokenActualDouble128 w B C)

theorem native_packetTokenActualDouble128 {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualDouble128Sentence w B C)) := ZFReplay.replay (packetTokenActualDouble128_kernel_certificate w B C)

def packetTokenSmallDigitByteBoundSentence {m} (w B C d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.mem d B).imp ((Formula.mem d C)))))).close

theorem source_packetTokenSmallDigitByteBound {m} (w B C d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenSmallDigitByteBoundSentence w B C d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem d B) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem d B) := .hyp (Or.inl rfl)
  exact PacketTokenByteBounds.small_digit_byte hZ w B C d h0 h1 h2 h3

theorem packetTokenSmallDigitByteBound_kernel_certificate {m} (w B C d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenSmallDigitByteBoundSentence w B C d)) := TheoryTransport.sentence (source_packetTokenSmallDigitByteBound w B C d)

theorem native_packetTokenSmallDigitByteBound {m} (w B C d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenSmallDigitByteBoundSentence w B C d)) := ZFReplay.replay (packetTokenSmallDigitByteBound_kernel_certificate w B C d)

def packetTokenShiftedDigitByteBoundSentence {m} (w B C d y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.mem d B).imp ((NaturalAdditionSyntax.sum w d B y).imp ((Formula.mem y C))))))).close

theorem source_packetTokenShiftedDigitByteBound {m} (w B C d y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenShiftedDigitByteBoundSentence w B C d y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NaturalAdditionSyntax.sum w d B y) (Context.add (Formula.mem d B) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (Formula.mem d B) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (NaturalAdditionSyntax.sum w d B y) := .hyp (Or.inl rfl)
  exact PacketTokenByteBounds.shifted_digit_byte hZ w B C d y h0 h1 h2 h3 h4

theorem packetTokenShiftedDigitByteBound_kernel_certificate {m} (w B C d y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenShiftedDigitByteBoundSentence w B C d y)) := TheoryTransport.sentence (source_packetTokenShiftedDigitByteBound w B C d y)

theorem native_packetTokenShiftedDigitByteBound {m} (w B C d y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenShiftedDigitByteBoundSentence w B C d y)) := ZFReplay.replay (packetTokenShiftedDigitByteBound_kernel_certificate w B C d y)

def packetTokenActualSmallOutputConstructedSentence {m} (w B C n t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.mem n B).imp ((Formula.mem t w).imp ((PacketTokenExistenceSyntax.existsOutput w n t))))))).close

theorem source_packetTokenActualSmallOutputConstructed {m} (w B C n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualSmallOutputConstructedSentence w B C n t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem t w) (Context.add (Formula.mem n B) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (Formula.mem t w) := .hyp (Or.inl rfl)
  exact PacketTokenExistencePoint.small_point hZ w B C n t h0 h1 h2 h3 h4

theorem packetTokenActualSmallOutputConstructed_kernel_certificate {m} (w B C n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualSmallOutputConstructedSentence w B C n t)) := TheoryTransport.sentence (source_packetTokenActualSmallOutputConstructed w B C n t)

theorem native_packetTokenActualSmallOutputConstructed {m} (w B C n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualSmallOutputConstructedSentence w B C n t)) := ZFReplay.replay (packetTokenActualSmallOutputConstructed_kernel_certificate w B C n t)

def packetTokenActualRecursiveOutputConstructedSentence {m} (w B C n d q t u y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketAffineSyntax.affine w B d q n).imp (((empty q).neg).imp ((NaturalAdditionSyntax.sum w d B y).imp ((PacketTokenAcceptedSyntax.accepted w q t u).imp ((PacketTokenExistenceSyntax.existsOutput w n t))))))))).close

theorem source_packetTokenActualRecursiveOutputConstructed {m} (w B C n d q t u y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualRecursiveOutputConstructedSentence w B C n d q t u y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w q t u) (Context.add (NaturalAdditionSyntax.sum w d B y) (Context.add ((empty q).neg) (Context.add (PacketAffineSyntax.affine w B d q n) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 128 B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral 256 C) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (PacketAffineSyntax.affine w B d q n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ ((empty q).neg) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (NaturalAdditionSyntax.sum w d B y) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketTokenAcceptedSyntax.accepted w q t u) := .hyp (Or.inl rfl)
  exact PacketTokenExistencePoint.step_values hZ w B C n d q t u y h0 h1 h2 h3 h4 h5 h6

theorem packetTokenActualRecursiveOutputConstructed_kernel_certificate {m} (w B C n d q t u y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualRecursiveOutputConstructedSentence w B C n d q t u y)) := TheoryTransport.sentence (source_packetTokenActualRecursiveOutputConstructed w B C n d q t u y)

theorem native_packetTokenActualRecursiveOutputConstructed {m} (w B C n d q t u y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualRecursiveOutputConstructedSentence w B C n d q t u y)) := ZFReplay.replay (packetTokenActualRecursiveOutputConstructed_kernel_certificate w B C n d q t u y)

def packetTokenAllInternalOutputExistenceIHDischargedSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (PacketTokenExistenceSyntax.property w.castSucc (Fin.last m)))))))).close

theorem source_packetTokenAllInternalOutputExistenceIHDischarged {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllInternalOutputExistenceIHDischargedSentence w B C) := by
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
  exact PacketTokenExistenceInduction.all_property hZ w B C h0 h1 h2

theorem packetTokenAllInternalOutputExistenceIHDischarged_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllInternalOutputExistenceIHDischargedSentence w B C)) := TheoryTransport.sentence (source_packetTokenAllInternalOutputExistenceIHDischarged w B C)

theorem native_packetTokenAllInternalOutputExistenceIHDischarged {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllInternalOutputExistenceIHDischargedSentence w B C)) := ZFReplay.replay (packetTokenAllInternalOutputExistenceIHDischarged_kernel_certificate w B C)

def packetTokenActualOutputExistsAtRadicesSentence {m} (w B C n t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.mem n w).imp ((Formula.mem t w).imp ((PacketTokenExistenceSyntax.existsOutput w n t))))))).close

theorem source_packetTokenActualOutputExistsAtRadices {m} (w B C n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualOutputExistsAtRadicesSentence w B C n t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem t w) (Context.add (Formula.mem n w) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (Formula.mem t w) := .hyp (Or.inl rfl)
  exact PacketTokenExistenceInduction.exists_output hZ w B C n t h0 h1 h2 h3 h4

theorem packetTokenActualOutputExistsAtRadices_kernel_certificate {m} (w B C n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualOutputExistsAtRadicesSentence w B C n t)) := TheoryTransport.sentence (source_packetTokenActualOutputExistsAtRadices w B C n t)

theorem native_packetTokenActualOutputExistsAtRadices {m} (w B C n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualOutputExistsAtRadicesSentence w B C n t)) := ZFReplay.replay (packetTokenActualOutputExistsAtRadices_kernel_certificate w B C n t)

def packetTokenAllInternalOutputUniquenessIHDischargedSentence {m} (w B C : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (PacketTokenUniqueSyntax.property w.castSucc (Fin.last m)))))))).close

theorem source_packetTokenAllInternalOutputUniquenessIHDischarged {m} (w B C : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllInternalOutputUniquenessIHDischargedSentence w B C) := by
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
  exact PacketTokenUniqueInduction.all_property hZ w B C h0 h1 h2

theorem packetTokenAllInternalOutputUniquenessIHDischarged_kernel_certificate {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllInternalOutputUniquenessIHDischargedSentence w B C)) := TheoryTransport.sentence (source_packetTokenAllInternalOutputUniquenessIHDischarged w B C)

theorem native_packetTokenAllInternalOutputUniquenessIHDischarged {m} (w B C : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllInternalOutputUniquenessIHDischargedSentence w B C)) := ZFReplay.replay (packetTokenAllInternalOutputUniquenessIHDischarged_kernel_certificate w B C)

def packetTokenActualOutputUniqueAtRadicesSentence {m} (w B C n t a b : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenAcceptedSyntax.accepted w n t b).imp ((Formula.equal a b))))))).close

theorem source_packetTokenActualOutputUniqueAtRadices {m} (w B C n t a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualOutputUniqueAtRadicesSentence w B C n t a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w n t b) (Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t b) := .hyp (Or.inl rfl)
  exact PacketTokenUniqueInduction.unique hZ w B C n t a b h0 h1 h2 h3 h4

theorem packetTokenActualOutputUniqueAtRadices_kernel_certificate {m} (w B C n t a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualOutputUniqueAtRadicesSentence w B C n t a b)) := TheoryTransport.sentence (source_packetTokenActualOutputUniqueAtRadices w B C n t a b)

theorem native_packetTokenActualOutputUniqueAtRadices {m} (w B C n t a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualOutputUniqueAtRadicesSentence w B C n t a b)) := ZFReplay.replay (packetTokenActualOutputUniqueAtRadices_kernel_certificate w B C n t a b)

def packetTokenActualUniqueOutputFiberAtRadicesSentence {m} (w B C n t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp ((Formula.mem n w).imp ((Formula.mem t w).imp ((PacketTokenExecutionSyntax.fiber w n t))))))).close

theorem source_packetTokenActualUniqueOutputFiberAtRadices {m} (w B C n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualUniqueOutputFiberAtRadicesSentence w B C n t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem t w) (Context.add (Formula.mem n w) (Context.add (SyntaxNumeralSyntax.numeral 256 C) (Context.add (SyntaxNumeralSyntax.numeral 128 B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (Formula.mem t w) := .hyp (Or.inl rfl)
  exact PacketTokenExecutionFiber.exists_fiber hZ w B C n t h0 h1 h2 h3 h4

theorem packetTokenActualUniqueOutputFiberAtRadices_kernel_certificate {m} (w B C n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualUniqueOutputFiberAtRadicesSentence w B C n t)) := TheoryTransport.sentence (source_packetTokenActualUniqueOutputFiberAtRadices w B C n t)

theorem native_packetTokenActualUniqueOutputFiberAtRadices {m} (w B C n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualUniqueOutputFiberAtRadicesSentence w B C n t)) := ZFReplay.replay (packetTokenActualUniqueOutputFiberAtRadices_kernel_certificate w B C n t)

def packetTokenUniqueOutputFiberDomainAtRadicesSentence {m} (w B C n t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 128 B).imp ((SyntaxNumeralSyntax.numeral 256 C).imp (((PacketTokenExecutionSyntax.fiber w n t).iff ((Formula.mem n w).conj (.mem t w))))))).close

theorem source_packetTokenUniqueOutputFiberDomainAtRadices {m} (w B C n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenUniqueOutputFiberDomainAtRadicesSentence w B C n t) := by
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
  exact PacketTokenExecutionFiber.fiber_iff hZ w B C n t h0 h1 h2

theorem packetTokenUniqueOutputFiberDomainAtRadices_kernel_certificate {m} (w B C n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenUniqueOutputFiberDomainAtRadicesSentence w B C n t)) := TheoryTransport.sentence (source_packetTokenUniqueOutputFiberDomainAtRadices w B C n t)

theorem native_packetTokenUniqueOutputFiberDomainAtRadices {m} (w B C n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenUniqueOutputFiberDomainAtRadicesSentence w B C n t)) := ZFReplay.replay (packetTokenUniqueOutputFiberDomainAtRadices_kernel_certificate w B C n t)

def packetTokenAllInternalExactUniqueOutputFibersSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenExecutionSyntax.allLaw w))).close

theorem source_packetTokenAllInternalExactUniqueOutputFibers {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenAllInternalExactUniqueOutputFibersSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokenExecution.all_law hZ w h0

theorem packetTokenAllInternalExactUniqueOutputFibers_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenAllInternalExactUniqueOutputFibersSentence w)) := TheoryTransport.sentence (source_packetTokenAllInternalExactUniqueOutputFibers w)

theorem native_packetTokenAllInternalExactUniqueOutputFibers {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenAllInternalExactUniqueOutputFibersSentence w)) := ZFReplay.replay (packetTokenAllInternalExactUniqueOutputFibers_kernel_certificate w)

def packetTokenActualUniqueOutputFiberExactDomainSentence {m} (w n t : Fin m) : Source.Sentence := ((omega w).imp (((PacketTokenExecutionSyntax.fiber w n t).iff ((Formula.mem n w).conj (.mem t w))))).close

theorem source_packetTokenActualUniqueOutputFiberExactDomain {m} (w n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualUniqueOutputFiberExactDomainSentence w n t) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketTokenExecution.fiber_iff hZ w n t h0

theorem packetTokenActualUniqueOutputFiberExactDomain_kernel_certificate {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualUniqueOutputFiberExactDomainSentence w n t)) := TheoryTransport.sentence (source_packetTokenActualUniqueOutputFiberExactDomain w n t)

theorem native_packetTokenActualUniqueOutputFiberExactDomain {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualUniqueOutputFiberExactDomainSentence w n t)) := ZFReplay.replay (packetTokenActualUniqueOutputFiberExactDomain_kernel_certificate w n t)

def packetTokenActualOutputExistsOnlyOmegaSentence {m} (w n t : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((Formula.mem t w).imp ((PacketTokenExistenceSyntax.existsOutput w n t))))).close

theorem source_packetTokenActualOutputExistsOnlyOmega {m} (w n t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualOutputExistsOnlyOmegaSentence w n t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem t w) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (Formula.mem t w) := .hyp (Or.inl rfl)
  exact PacketTokenExecution.exists_output hZ w n t h0 h1 h2

theorem packetTokenActualOutputExistsOnlyOmega_kernel_certificate {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualOutputExistsOnlyOmegaSentence w n t)) := TheoryTransport.sentence (source_packetTokenActualOutputExistsOnlyOmega w n t)

theorem native_packetTokenActualOutputExistsOnlyOmega {m} (w n t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualOutputExistsOnlyOmegaSentence w n t)) := ZFReplay.replay (packetTokenActualOutputExistsOnlyOmega_kernel_certificate w n t)

def packetTokenActualOutputUniqueOnlyOmegaSentence {m} (w n t a b : Fin m) : Source.Sentence := ((omega w).imp ((PacketTokenAcceptedSyntax.accepted w n t a).imp ((PacketTokenAcceptedSyntax.accepted w n t b).imp ((Formula.equal a b))))).close

theorem source_packetTokenActualOutputUniqueOnlyOmega {m} (w n t a b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetTokenActualOutputUniqueOnlyOmegaSentence w n t a b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketTokenAcceptedSyntax.accepted w n t b) (Context.add (PacketTokenAcceptedSyntax.accepted w n t a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t a) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketTokenAcceptedSyntax.accepted w n t b) := .hyp (Or.inl rfl)
  exact PacketTokenExecution.unique hZ w n t a b h0 h1 h2

theorem packetTokenActualOutputUniqueOnlyOmega_kernel_certificate {m} (w n t a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetTokenActualOutputUniqueOnlyOmegaSentence w n t a b)) := TheoryTransport.sentence (source_packetTokenActualOutputUniqueOnlyOmega w n t a b)

theorem native_packetTokenActualOutputUniqueOnlyOmega {m} (w n t a b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetTokenActualOutputUniqueOnlyOmegaSentence w n t a b)) := ZFReplay.replay (packetTokenActualOutputUniqueOnlyOmega_kernel_certificate w n t a b)

end PPAC.Migration.Internal.ObjectPacketTokenExecution
