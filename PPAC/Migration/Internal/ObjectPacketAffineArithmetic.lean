import PPAC.Migration.Internal.PacketAffineAcceptedProperties

/-! Exact all-internal relational Packet affine arithmetic by object omega induction; original Basic AST translation and full byte bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketAffineArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetAffineRootBaseFieldsIffSentence {m} (wide : Bool) (w B d t n r : Fin m) : Source.Sentence := ((omega w).imp ((PacketHornAffineSyntax.row wide w d t n r).imp (((PacketAffineApplicationSyntax.baseOutcome wide w B r).iff (PacketAffineRootSyntax.zeroCase B d t n))))).close

theorem source_packetAffineRootBaseFieldsIff {m} (wide : Bool) (w B d t n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineRootBaseFieldsIffSentence wide w B d t n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inl rfl)
  exact PacketAffineRootBase.base_iff hZ wide w B d t n r h0 h1

theorem packetAffineRootBaseFieldsIff_kernel_certificate {m} (wide : Bool) (w B d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineRootBaseFieldsIffSentence wide w B d t n r)) := TheoryTransport.sentence (source_packetAffineRootBaseFieldsIff wide w B d t n r)

theorem native_packetAffineRootBaseFieldsIff {m} (wide : Bool) (w B d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineRootBaseFieldsIffSentence wide w B d t n r)) := ZFReplay.replay (packetAffineRootBaseFieldsIff_kernel_certificate wide w B d t n r)

def packetAffineRootStepFieldsIffSentence {m} (wide : Bool) (w B V d t n r : Fin m) : Source.Sentence := ((omega w).imp ((PacketHornAffineSyntax.row wide w d t n r).imp (((PacketAffineApplicationSyntax.stepOutcome wide w B V r).iff (PacketAffineRootSyntax.predecessor wide w B V d t n))))).close

theorem source_packetAffineRootStepFieldsIff {m} (wide : Bool) (w B V d t n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineRootStepFieldsIffSentence wide w B V d t n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inl rfl)
  exact PacketAffineRootStep.step_iff hZ wide w B V d t n r h0 h1

theorem packetAffineRootStepFieldsIff_kernel_certificate {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineRootStepFieldsIffSentence wide w B V d t n r)) := TheoryTransport.sentence (source_packetAffineRootStepFieldsIff wide w B V d t n r)

theorem native_packetAffineRootStepFieldsIff {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineRootStepFieldsIffSentence wide w B V d t n r)) := ZFReplay.replay (packetAffineRootStepFieldsIff_kernel_certificate wide w B V d t n r)

def packetAffineExactRootStepEquationSentence {m} (wide : Bool) (w B V d t n r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketHornAffineSyntax.row wide w d t n r).imp (((PacketTraceSyntax.step w r V).iff (PacketAffineRootSyntax.criterion wide w B V d t n)))))).close

theorem source_packetAffineExactRootStepEquation {m} (wide : Bool) (w B V d t n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineExactRootStepEquationSentence wide w B V d t n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inl rfl)
  exact PacketAffineRootEquation.step_iff hZ wide w B V d t n r h0 h1 h2

theorem packetAffineExactRootStepEquation_kernel_certificate {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineExactRootStepEquationSentence wide w B V d t n r)) := TheoryTransport.sentence (source_packetAffineExactRootStepEquation wide w B V d t n r)

theorem native_packetAffineExactRootStepEquation {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineExactRootStepEquationSentence wide w B V d t n r)) := ZFReplay.replay (packetAffineExactRootStepEquation_kernel_certificate wide w B V d t n r)

def packetAffineExactRootMemberEquationSentence {m} (wide : Bool) (w B V d t n r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketTraceCore.value w V).imp ((PacketHornAffineSyntax.row wide w d t n r).imp (((Formula.mem r V).iff (PacketAffineRootSyntax.criterion wide w B V d t n))))))).close

theorem source_packetAffineExactRootMemberEquation {m} (wide : Bool) (w B V d t n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineExactRootMemberEquationSentence wide w B V d t n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inl rfl)
  exact PacketAffineRootEquation.member_iff hZ wide w B V d t n r h0 h1 h2 h3

theorem packetAffineExactRootMemberEquation_kernel_certificate {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineExactRootMemberEquationSentence wide w B V d t n r)) := TheoryTransport.sentence (source_packetAffineExactRootMemberEquation wide w B V d t n r)

theorem native_packetAffineExactRootMemberEquation {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineExactRootMemberEquationSentence wide w B V d t n r)) := ZFReplay.replay (packetAffineExactRootMemberEquation_kernel_certificate wide w B V d t n r)

def packetAffineInternalEntryFromIHSentence {m} (wide : Bool) (w B V t d a : Fin m) : Source.Sentence := ((PacketAffineInductionSyntax.correct wide w B V t).imp ((PacketHornAffineSyntax.entry wide w V d t a).imp ((PacketAffineSyntax.affine w B d t a)))).close

theorem source_packetAffineInternalEntryFromIH {m} (wide : Bool) (w B V t d a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineInternalEntryFromIHSentence wide w B V t d a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.entry wide w V d t a) (Context.add (PacketAffineInductionSyntax.correct wide w B V t) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (PacketAffineInductionSyntax.correct wide w B V t) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketHornAffineSyntax.entry wide w V d t a) := .hyp (Or.inl rfl)
  exact PacketAffineInductionEntry.entry_to_affine wide w B V t d a h0 h1

theorem packetAffineInternalEntryFromIH_kernel_certificate {m} (wide : Bool) (w B V t d a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineInternalEntryFromIHSentence wide w B V t d a)) := TheoryTransport.sentence (source_packetAffineInternalEntryFromIH wide w B V t d a)

theorem native_packetAffineInternalEntryFromIH {m} (wide : Bool) (w B V t d a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineInternalEntryFromIHSentence wide w B V t d a)) := ZFReplay.replay (packetAffineInternalEntryFromIH_kernel_certificate wide w B V t d a)

def packetAffineInternalEntryConstructedFromIHSentence {m} (wide : Bool) (w B V t d a : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineInductionSyntax.correct wide w B V t).imp ((PacketAffineSyntax.affine w B d t a).imp ((PacketHornAffineSyntax.entry wide w V d t a))))).close

theorem source_packetAffineInternalEntryConstructedFromIH {m} (wide : Bool) (w B V t d a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineInternalEntryConstructedFromIHSentence wide w B V t d a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineSyntax.affine w B d t a) (Context.add (PacketAffineInductionSyntax.correct wide w B V t) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PacketAffineInductionSyntax.correct wide w B V t) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketAffineSyntax.affine w B d t a) := .hyp (Or.inl rfl)
  exact PacketAffineInductionEntry.affine_to_entry hZ wide w B V t d a h0 h1 h2

theorem packetAffineInternalEntryConstructedFromIH_kernel_certificate {m} (wide : Bool) (w B V t d a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineInternalEntryConstructedFromIHSentence wide w B V t d a)) := TheoryTransport.sentence (source_packetAffineInternalEntryConstructedFromIH wide w B V t d a)

theorem native_packetAffineInternalEntryConstructedFromIH {m} (wide : Bool) (w B V t d a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineInternalEntryConstructedFromIHSentence wide w B V t d a)) := ZFReplay.replay (packetAffineInternalEntryConstructedFromIH_kernel_certificate wide w B V t d a)

def packetAffineZeroPointMembershipIffSentence {m} (wide : Bool) (w B V d z n r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketTraceCore.value w V).imp ((empty z).imp ((PacketHornAffineSyntax.row wide w d z n r).imp (((Formula.mem r V).iff (PacketAffineSyntax.affine w B d z n)))))))).close

theorem source_packetAffineZeroPointMembershipIff {m} (wide : Bool) (w B V d z n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineZeroPointMembershipIffSentence wide w B V d z n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d z n r) (Context.add (empty z) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PacketHornAffineSyntax.row wide w d z n r) := .hyp (Or.inl rfl)
  exact PacketAffineInductionPoint.zero hZ wide w B V d z n r h0 h1 h2 h3 h4

theorem packetAffineZeroPointMembershipIff_kernel_certificate {m} (wide : Bool) (w B V d z n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineZeroPointMembershipIffSentence wide w B V d z n r)) := TheoryTransport.sentence (source_packetAffineZeroPointMembershipIff wide w B V d z n r)

theorem native_packetAffineZeroPointMembershipIff {m} (wide : Bool) (w B V d z n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineZeroPointMembershipIffSentence wide w B V d z n r)) := ZFReplay.replay (packetAffineZeroPointMembershipIff_kernel_certificate wide w B V d z n r)

def packetAffineSuccessorPointMembershipIffSentence {m} (wide : Bool) (w B V d t s n r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketTraceCore.value w V).imp ((Formula.mem t w).imp ((PacketAffineInductionSyntax.correct wide w B V t).imp ((successor s t).imp ((PacketHornAffineSyntax.row wide w d s n r).imp (((Formula.mem r V).iff (PacketAffineSyntax.affine w B d s n)))))))))).close

theorem source_packetAffineSuccessorPointMembershipIff {m} (wide : Bool) (w B V d t s n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineSuccessorPointMembershipIffSentence wide w B V d t s n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d s n r) (Context.add (successor s t) (Context.add (PacketAffineInductionSyntax.correct wide w B V t) (Context.add (Formula.mem t w) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (PacketAffineInductionSyntax.correct wide w B V t) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (successor s t) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PacketHornAffineSyntax.row wide w d s n r) := .hyp (Or.inl rfl)
  exact PacketAffineInductionPoint.successor hZ wide w B V d t s n r h0 h1 h2 h3 h4 h5 h6

theorem packetAffineSuccessorPointMembershipIff_kernel_certificate {m} (wide : Bool) (w B V d t s n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineSuccessorPointMembershipIffSentence wide w B V d t s n r)) := TheoryTransport.sentence (source_packetAffineSuccessorPointMembershipIff wide w B V d t s n r)

theorem native_packetAffineSuccessorPointMembershipIff {m} (wide : Bool) (w B V d t s n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineSuccessorPointMembershipIffSentence wide w B V d t s n r)) := ZFReplay.replay (packetAffineSuccessorPointMembershipIff_kernel_certificate wide w B V d t s n r)

def packetAffineAllInternalTailIHDischargedSentence {m} (wide : Bool) (w B V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketTraceCore.value w V).imp ((Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (PacketAffineInductionSyntax.correct wide w.castSucc B.castSucc V.castSucc (Fin.last m)))))))).close

theorem source_packetAffineAllInternalTailIHDischarged {m} (wide : Bool) (w B V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAllInternalTailIHDischargedSentence wide w B V) := by
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
  exact PacketAffineInduction.all_correct hZ wide w B V h0 h1 h2

theorem packetAffineAllInternalTailIHDischarged_kernel_certificate {m} (wide : Bool) (w B V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAllInternalTailIHDischargedSentence wide w B V)) := TheoryTransport.sentence (source_packetAffineAllInternalTailIHDischarged wide w B V)

theorem native_packetAffineAllInternalTailIHDischarged {m} (wide : Bool) (w B V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAllInternalTailIHDischargedSentence wide w B V)) := ZFReplay.replay (packetAffineAllInternalTailIHDischarged_kernel_certificate wide w B V)

def packetAffineAllInternalRootMembershipIffSentence {m} (wide : Bool) (w B V d t n r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketTraceCore.value w V).imp ((PacketHornAffineSyntax.row wide w d t n r).imp (((Formula.mem r V).iff (PacketAffineSyntax.affine w B d t n))))))).close

theorem source_packetAffineAllInternalRootMembershipIff {m} (wide : Bool) (w B V d t n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAllInternalRootMembershipIffSentence wide w B V d t n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (PacketTraceCore.value w V) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketTraceCore.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inl rfl)
  exact PacketAffineInduction.membership_iff hZ wide w B V d t n r h0 h1 h2 h3

theorem packetAffineAllInternalRootMembershipIff_kernel_certificate {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAllInternalRootMembershipIffSentence wide w B V d t n r)) := TheoryTransport.sentence (source_packetAffineAllInternalRootMembershipIff wide w B V d t n r)

theorem native_packetAffineAllInternalRootMembershipIff {m} (wide : Bool) (w B V d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAllInternalRootMembershipIffSentence wide w B V d t n r)) := ZFReplay.replay (packetAffineAllInternalRootMembershipIff_kernel_certificate wide w B V d t n r)

def packetAffineConditionExactArithmeticIffSentence {m} (wide : Bool) (w B d t n r : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketHornAffineSyntax.row wide w d t n r).imp (((PacketTraceSyntax.condition w r).iff (PacketAffineSyntax.affine w B d t n)))))).close

theorem source_packetAffineConditionExactArithmeticIff {m} (wide : Bool) (w B d t n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineConditionExactArithmeticIffSentence wide w B d t n r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.row wide w d t n r) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PacketHornAffineSyntax.row wide w d t n r) := .hyp (Or.inl rfl)
  exact PacketAffineAccepted.condition_iff hZ wide w B d t n r h0 h1 h2

theorem packetAffineConditionExactArithmeticIff_kernel_certificate {m} (wide : Bool) (w B d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineConditionExactArithmeticIffSentence wide w B d t n r)) := TheoryTransport.sentence (source_packetAffineConditionExactArithmeticIff wide w B d t n r)

theorem native_packetAffineConditionExactArithmeticIff {m} (wide : Bool) (w B d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineConditionExactArithmeticIffSentence wide w B d t n r)) := ZFReplay.replay (packetAffineConditionExactArithmeticIff_kernel_certificate wide w B d t n r)

def packetAffineAcceptedExactArithmeticIffSentence {m} (wide : Bool) (w B d t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((PacketAffineAcceptedSyntax.accepted wide w d t n).iff (PacketAffineSyntax.affine w B d t n))))).close

theorem source_packetAffineAcceptedExactArithmeticIff {m} (wide : Bool) (w B d t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAcceptedExactArithmeticIffSentence wide w B d t n) := by
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
  exact PacketAffineAccepted.accepted_iff hZ wide w B d t n h0 h1

theorem packetAffineAcceptedExactArithmeticIff_kernel_certificate {m} (wide : Bool) (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAcceptedExactArithmeticIffSentence wide w B d t n)) := TheoryTransport.sentence (source_packetAffineAcceptedExactArithmeticIff wide w B d t n)

theorem native_packetAffineAcceptedExactArithmeticIff {m} (wide : Bool) (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAcceptedExactArithmeticIffSentence wide w B d t n)) := ZFReplay.replay (packetAffineAcceptedExactArithmeticIff_kernel_certificate wide w B d t n)

def packetAffineAllInternalAcceptedExactArithmeticSentence {m} (wide : Bool) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineAcceptedSyntax.allLaw wide w B)))).close

theorem source_packetAffineAllInternalAcceptedExactArithmetic {m} (wide : Bool) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAllInternalAcceptedExactArithmeticSentence wide w B) := by
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
  exact PacketAffineAccepted.all_law hZ wide w B h0 h1

theorem packetAffineAllInternalAcceptedExactArithmetic_kernel_certificate {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAllInternalAcceptedExactArithmeticSentence wide w B)) := TheoryTransport.sentence (source_packetAffineAllInternalAcceptedExactArithmetic wide w B)

theorem native_packetAffineAllInternalAcceptedExactArithmetic {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAllInternalAcceptedExactArithmeticSentence wide w B)) := ZFReplay.replay (packetAffineAllInternalAcceptedExactArithmetic_kernel_certificate wide w B)

def packetAffineAllInternalRootExactArithmeticSentence {m} (wide : Bool) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineAcceptedSyntax.allRootLaw wide w B)))).close

theorem source_packetAffineAllInternalRootExactArithmetic {m} (wide : Bool) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAllInternalRootExactArithmeticSentence wide w B) := by
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
  exact PacketAffineAccepted.all_root_law hZ wide w B h0 h1

theorem packetAffineAllInternalRootExactArithmetic_kernel_certificate {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAllInternalRootExactArithmeticSentence wide w B)) := TheoryTransport.sentence (source_packetAffineAllInternalRootExactArithmetic wide w B)

theorem native_packetAffineAllInternalRootExactArithmetic {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAllInternalRootExactArithmeticSentence wide w B)) := ZFReplay.replay (packetAffineAllInternalRootExactArithmetic_kernel_certificate wide w B)

def packetAffineActualLiteralExactArithmeticSystemExistsSentence {m} (wide : Bool) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineAcceptedSyntax.existsSystem wide w))).close

theorem source_packetAffineActualLiteralExactArithmeticSystemExists {m} (wide : Bool) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineActualLiteralExactArithmeticSystemExistsSentence wide w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketAffineAccepted.exists_system hZ wide w h0

theorem packetAffineActualLiteralExactArithmeticSystemExists_kernel_certificate {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineActualLiteralExactArithmeticSystemExistsSentence wide w)) := TheoryTransport.sentence (source_packetAffineActualLiteralExactArithmeticSystemExists wide w)

theorem native_packetAffineActualLiteralExactArithmeticSystemExists {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineActualLiteralExactArithmeticSystemExistsSentence wide w)) := ZFReplay.replay (packetAffineActualLiteralExactArithmeticSystemExists_kernel_certificate wide w)

def packetAffineAcceptedOutputExistsSentence {m} (wide : Bool) (w B d t : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((Formula.mem d B).imp ((Formula.mem t w).imp ((PacketAffineAcceptedProperties.existsValue wide w d t)))))).close

theorem source_packetAffineAcceptedOutputExists {m} (wide : Bool) (w B d t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAcceptedOutputExistsSentence wide w B d t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem t w) (Context.add (Formula.mem d B) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem d B) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (Formula.mem t w) := .hyp (Or.inl rfl)
  exact PacketAffineAcceptedProperties.exists_value hZ wide w B d t h0 h1 h2 h3

theorem packetAffineAcceptedOutputExists_kernel_certificate {m} (wide : Bool) (w B d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAcceptedOutputExistsSentence wide w B d t)) := TheoryTransport.sentence (source_packetAffineAcceptedOutputExists wide w B d t)

theorem native_packetAffineAcceptedOutputExists {m} (wide : Bool) (w B d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAcceptedOutputExistsSentence wide w B d t)) := ZFReplay.replay (packetAffineAcceptedOutputExists_kernel_certificate wide w B d t)

def packetAffineAcceptedOutputsUniqueSentence {m} (wide : Bool) (w B d t n a : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineAcceptedSyntax.accepted wide w d t n).imp ((PacketAffineAcceptedSyntax.accepted wide w d t a).imp ((Formula.equal n a)))))).close

theorem source_packetAffineAcceptedOutputsUnique {m} (wide : Bool) (w B d t n a : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAcceptedOutputsUniqueSentence wide w B d t n a) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketAffineAcceptedSyntax.accepted wide w d t a) (Context.add (PacketAffineAcceptedSyntax.accepted wide w d t n) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PacketAffineAcceptedSyntax.accepted wide w d t n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (PacketAffineAcceptedSyntax.accepted wide w d t a) := .hyp (Or.inl rfl)
  exact PacketAffineAcceptedProperties.unique hZ wide w B d t n a h0 h1 h2 h3

theorem packetAffineAcceptedOutputsUnique_kernel_certificate {m} (wide : Bool) (w B d t n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAcceptedOutputsUniqueSentence wide w B d t n a)) := TheoryTransport.sentence (source_packetAffineAcceptedOutputsUnique wide w B d t n a)

theorem native_packetAffineAcceptedOutputsUnique {m} (wide : Bool) (w B d t n a : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAcceptedOutputsUniqueSentence wide w B d t n a)) := ZFReplay.replay (packetAffineAcceptedOutputsUnique_kernel_certificate wide w B d t n a)

def packetAffineAcceptedRejectDigitSentence {m} (wide : Bool) (w B d t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((Formula.mem d B).neg).imp (((PacketAffineAcceptedSyntax.accepted wide w d t n).neg))))).close

theorem source_packetAffineAcceptedRejectDigit {m} (wide : Bool) (w B d t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAcceptedRejectDigitSentence wide w B d t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem d B).neg) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((Formula.mem d B).neg) := .hyp (Or.inl rfl)
  exact PacketAffineAcceptedProperties.reject_digit hZ wide w B d t n h0 h1 h2

theorem packetAffineAcceptedRejectDigit_kernel_certificate {m} (wide : Bool) (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAcceptedRejectDigitSentence wide w B d t n)) := TheoryTransport.sentence (source_packetAffineAcceptedRejectDigit wide w B d t n)

theorem native_packetAffineAcceptedRejectDigit {m} (wide : Bool) (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAcceptedRejectDigitSentence wide w B d t n)) := ZFReplay.replay (packetAffineAcceptedRejectDigit_kernel_certificate wide w B d t n)

def packetAffineAcceptedRejectTailSentence {m} (wide : Bool) (w B d t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((Formula.mem t w).neg).imp (((PacketAffineAcceptedSyntax.accepted wide w d t n).neg))))).close

theorem source_packetAffineAcceptedRejectTail {m} (wide : Bool) (w B d t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAcceptedRejectTailSentence wide w B d t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem t w).neg) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((Formula.mem t w).neg) := .hyp (Or.inl rfl)
  exact PacketAffineAcceptedProperties.reject_tail hZ wide w B d t n h0 h1 h2

theorem packetAffineAcceptedRejectTail_kernel_certificate {m} (wide : Bool) (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAcceptedRejectTailSentence wide w B d t n)) := TheoryTransport.sentence (source_packetAffineAcceptedRejectTail wide w B d t n)

theorem native_packetAffineAcceptedRejectTail {m} (wide : Bool) (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAcceptedRejectTailSentence wide w B d t n)) := ZFReplay.replay (packetAffineAcceptedRejectTail_kernel_certificate wide w B d t n)

def packetAffineAcceptedRejectOutputSentence {m} (wide : Bool) (w B d t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((Formula.mem n w).neg).imp (((PacketAffineAcceptedSyntax.accepted wide w d t n).neg))))).close

theorem source_packetAffineAcceptedRejectOutput {m} (wide : Bool) (w B d t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineAcceptedRejectOutputSentence wide w B d t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n w).neg) (Context.add (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inl rfl)
  exact PacketAffineAcceptedProperties.reject_output hZ wide w B d t n h0 h1 h2

theorem packetAffineAcceptedRejectOutput_kernel_certificate {m} (wide : Bool) (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineAcceptedRejectOutputSentence wide w B d t n)) := TheoryTransport.sentence (source_packetAffineAcceptedRejectOutput wide w B d t n)

theorem native_packetAffineAcceptedRejectOutput {m} (wide : Bool) (w B d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineAcceptedRejectOutputSentence wide w B d t n)) := ZFReplay.replay (packetAffineAcceptedRejectOutput_kernel_certificate wide w B d t n)

end PPAC.Migration.Internal.ObjectPacketAffineArithmetic
