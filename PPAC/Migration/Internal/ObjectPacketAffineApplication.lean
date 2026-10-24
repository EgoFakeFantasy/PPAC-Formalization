import PPAC.Migration.Internal.PacketAffineApplicationLaws

/-! Original Packet affine bounded applications and all-internal exact outcomes; global Horn condition and byte bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectPacketAffineApplication
open Source SourceAlgebra SourceLogic OmegaSyntax

def packetAffineBaseHeadSearchBoundSentence {m} (wide : Bool) (env : Fin 1 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((HornExprSyntax.graph (PacketAffineRuleData.baseRule wide).head w env r).imp ((HornExprBounds.environmentBound 1 r env))))).close

theorem source_packetAffineBaseHeadSearchBound {m} (wide : Bool) (env : Fin 1 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineBaseHeadSearchBoundSentence wide env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (PacketAffineRuleData.baseRule wide).head w env r) (Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (PacketAffineRuleData.baseRule wide).head w env r) := .hyp (Or.inl rfl)
  exact PacketAffineApplicationBounds.base_bound hZ wide w r env h0 h1 h2

theorem packetAffineBaseHeadSearchBound_kernel_certificate {m} (wide : Bool) (env : Fin 1 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineBaseHeadSearchBoundSentence wide env w r)) := TheoryTransport.sentence (source_packetAffineBaseHeadSearchBound wide env w r)

theorem native_packetAffineBaseHeadSearchBound {m} (wide : Bool) (env : Fin 1 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineBaseHeadSearchBoundSentence wide env w r)) := ZFReplay.replay (packetAffineBaseHeadSearchBound_kernel_certificate wide env w r)

def packetAffineBaseMatrixSuppliesBoundedApplicationSentence {m} (wide : Bool) (env : Fin 1 → Fin m) (w r V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((HornRuleSyntax.matrix (PacketAffineRuleData.baseRule wide) w r V env).imp ((HornApplicationSyntax.application (PacketAffineRuleData.baseRule wide) w r V))))).close

theorem source_packetAffineBaseMatrixSuppliesBoundedApplication {m} (wide : Bool) (env : Fin 1 → Fin m) (w r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineBaseMatrixSuppliesBoundedApplicationSentence wide env w r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.matrix (PacketAffineRuleData.baseRule wide) w r V env) (Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornRuleSyntax.matrix (PacketAffineRuleData.baseRule wide) w r V env) := .hyp (Or.inl rfl)
  exact PacketAffineApplicationBounds.base_intro hZ wide w r V env h0 h1 h2

theorem packetAffineBaseMatrixSuppliesBoundedApplication_kernel_certificate {m} (wide : Bool) (env : Fin 1 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineBaseMatrixSuppliesBoundedApplicationSentence wide env w r V)) := TheoryTransport.sentence (source_packetAffineBaseMatrixSuppliesBoundedApplication wide env w r V)

theorem native_packetAffineBaseMatrixSuppliesBoundedApplication {m} (wide : Bool) (env : Fin 1 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineBaseMatrixSuppliesBoundedApplicationSentence wide env w r V)) := ZFReplay.replay (packetAffineBaseMatrixSuppliesBoundedApplication_kernel_certificate wide env w r V)

def packetAffineStepHeadSearchBoundSentence {m} (wide : Bool) (env : Fin 3 → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (PacketAffineRuleData.stepRule wide).head w env r).imp ((HornExprBounds.environmentBound 3 r env))))).close

theorem source_packetAffineStepHeadSearchBound {m} (wide : Bool) (env : Fin 3 → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineStepHeadSearchBoundSentence wide env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (PacketAffineRuleData.stepRule wide).head w env r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (PacketAffineRuleData.stepRule wide).head w env r) := .hyp (Or.inl rfl)
  exact PacketAffineApplicationBounds.step_bound hZ wide w r env h0 h1 h2

theorem packetAffineStepHeadSearchBound_kernel_certificate {m} (wide : Bool) (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineStepHeadSearchBoundSentence wide env w r)) := TheoryTransport.sentence (source_packetAffineStepHeadSearchBound wide env w r)

theorem native_packetAffineStepHeadSearchBound {m} (wide : Bool) (env : Fin 3 → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineStepHeadSearchBoundSentence wide env w r)) := ZFReplay.replay (packetAffineStepHeadSearchBound_kernel_certificate wide env w r)

def packetAffineStepMatrixSuppliesBoundedApplicationSentence {m} (wide : Bool) (env : Fin 3 → Fin m) (w r V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornRuleSyntax.matrix (PacketAffineRuleData.stepRule wide) w r V env).imp ((HornApplicationSyntax.application (PacketAffineRuleData.stepRule wide) w r V))))).close

theorem source_packetAffineStepMatrixSuppliesBoundedApplication {m} (wide : Bool) (env : Fin 3 → Fin m) (w r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineStepMatrixSuppliesBoundedApplicationSentence wide env w r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.matrix (PacketAffineRuleData.stepRule wide) w r V env) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornRuleSyntax.matrix (PacketAffineRuleData.stepRule wide) w r V env) := .hyp (Or.inl rfl)
  exact PacketAffineApplicationBounds.step_intro hZ wide w r V env h0 h1 h2

theorem packetAffineStepMatrixSuppliesBoundedApplication_kernel_certificate {m} (wide : Bool) (env : Fin 3 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineStepMatrixSuppliesBoundedApplicationSentence wide env w r V)) := TheoryTransport.sentence (source_packetAffineStepMatrixSuppliesBoundedApplication wide env w r V)

theorem native_packetAffineStepMatrixSuppliesBoundedApplication {m} (wide : Bool) (env : Fin 3 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineStepMatrixSuppliesBoundedApplicationSentence wide env w r V)) := ZFReplay.replay (packetAffineStepMatrixSuppliesBoundedApplication_kernel_certificate wide env w r V)

def packetAffineRowAssignmentsNaturalSentence {m} (wide : Bool) (w d t n r : Fin m) : Source.Sentence := ((omega w).imp ((PacketHornAffineSyntax.row wide w d t n r).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three d t n))))).close

theorem source_packetAffineRowAssignmentsNatural {m} (wide : Bool) (w d t n r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineRowAssignmentsNaturalSentence wide w d t n r) := by
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
  exact PacketAffineApplicationNatural.row_environment hZ wide w d t n r h0 h1

theorem packetAffineRowAssignmentsNatural_kernel_certificate {m} (wide : Bool) (w d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineRowAssignmentsNaturalSentence wide w d t n r)) := TheoryTransport.sentence (source_packetAffineRowAssignmentsNatural wide w d t n r)

theorem native_packetAffineRowAssignmentsNatural {m} (wide : Bool) (w d t n r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineRowAssignmentsNaturalSentence wide w d t n r)) := ZFReplay.replay (packetAffineRowAssignmentsNatural_kernel_certificate wide w d t n r)

def packetAffineEntryAssignmentsNaturalSentence {m} (wide : Bool) (w V d t n : Fin m) : Source.Sentence := ((omega w).imp ((PacketHornAffineSyntax.entry wide w V d t n).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three d t n))))).close

theorem source_packetAffineEntryAssignmentsNatural {m} (wide : Bool) (w V d t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineEntryAssignmentsNaturalSentence wide w V d t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.entry wide w V d t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketHornAffineSyntax.entry wide w V d t n) := .hyp (Or.inl rfl)
  exact PacketAffineApplicationNatural.entry_environment hZ wide w V d t n h0 h1

theorem packetAffineEntryAssignmentsNatural_kernel_certificate {m} (wide : Bool) (w V d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineEntryAssignmentsNaturalSentence wide w V d t n)) := TheoryTransport.sentence (source_packetAffineEntryAssignmentsNatural wide w V d t n)

theorem native_packetAffineEntryAssignmentsNatural {m} (wide : Bool) (w V d t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineEntryAssignmentsNaturalSentence wide w V d t n)) := ZFReplay.replay (packetAffineEntryAssignmentsNatural_kernel_certificate wide w V d t n)

def packetAffineBaseDigitNaturalSentence {m} (wide : Bool) (w B d r : Fin m) : Source.Sentence := ((omega w).imp ((PacketHornAffineSyntax.base wide w B d r).imp ((Formula.mem d w)))).close

theorem source_packetAffineBaseDigitNatural {m} (wide : Bool) (w B d r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineBaseDigitNaturalSentence wide w B d r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.base wide w B d r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketHornAffineSyntax.base wide w B d r) := .hyp (Or.inl rfl)
  exact PacketAffineApplicationNatural.base_digit hZ wide w B d r h0 h1

theorem packetAffineBaseDigitNatural_kernel_certificate {m} (wide : Bool) (w B d r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineBaseDigitNaturalSentence wide w B d r)) := TheoryTransport.sentence (source_packetAffineBaseDigitNatural wide w B d r)

theorem native_packetAffineBaseDigitNatural {m} (wide : Bool) (w B d r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineBaseDigitNaturalSentence wide w B d r)) := ZFReplay.replay (packetAffineBaseDigitNatural_kernel_certificate wide w B d r)

def packetAffineStepAssignmentsNaturalSentence {m} (wide : Bool) (w B V d t a r : Fin m) : Source.Sentence := ((omega w).imp ((PacketHornAffineSyntax.step wide w B V d t a r).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three d t a))))).close

theorem source_packetAffineStepAssignmentsNatural {m} (wide : Bool) (w B V d t a r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineStepAssignmentsNaturalSentence wide w B V d t a r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PacketHornAffineSyntax.step wide w B V d t a r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PacketHornAffineSyntax.step wide w B V d t a r) := .hyp (Or.inl rfl)
  exact PacketAffineApplicationNatural.step_environment hZ wide w B V d t a r h0 h1

theorem packetAffineStepAssignmentsNatural_kernel_certificate {m} (wide : Bool) (w B V d t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineStepAssignmentsNaturalSentence wide w B V d t a r)) := TheoryTransport.sentence (source_packetAffineStepAssignmentsNatural wide w B V d t a r)

theorem native_packetAffineStepAssignmentsNatural {m} (wide : Bool) (w B V d t a r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineStepAssignmentsNaturalSentence wide w B V d t a r)) := ZFReplay.replay (packetAffineStepAssignmentsNatural_kernel_certificate wide w B V d t a r)

def packetAffineWholeBaseApplicationIffSentence {m} (wide : Bool) (w B r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((HornApplicationSyntax.application (PacketAffineRuleData.baseRule wide) w r V).iff (PacketAffineApplicationSyntax.baseOutcome wide w B r))))).close

theorem source_packetAffineWholeBaseApplicationIff {m} (wide : Bool) (w B r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineWholeBaseApplicationIffSentence wide w B r V) := by
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
  exact PacketAffineApplication.base_iff hZ wide w B r V h0 h1

theorem packetAffineWholeBaseApplicationIff_kernel_certificate {m} (wide : Bool) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineWholeBaseApplicationIffSentence wide w B r V)) := TheoryTransport.sentence (source_packetAffineWholeBaseApplicationIff wide w B r V)

theorem native_packetAffineWholeBaseApplicationIff {m} (wide : Bool) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineWholeBaseApplicationIffSentence wide w B r V)) := ZFReplay.replay (packetAffineWholeBaseApplicationIff_kernel_certificate wide w B r V)

def packetAffineWholeStepApplicationIffSentence {m} (wide : Bool) (w B r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp (((HornApplicationSyntax.application (PacketAffineRuleData.stepRule wide) w r V).iff (PacketAffineApplicationSyntax.stepOutcome wide w B V r))))).close

theorem source_packetAffineWholeStepApplicationIff {m} (wide : Bool) (w B r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineWholeStepApplicationIffSentence wide w B r V) := by
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
  exact PacketAffineApplication.step_iff hZ wide w B r V h0 h1

theorem packetAffineWholeStepApplicationIff_kernel_certificate {m} (wide : Bool) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineWholeStepApplicationIffSentence wide w B r V)) := TheoryTransport.sentence (source_packetAffineWholeStepApplicationIff wide w B r V)

theorem native_packetAffineWholeStepApplicationIff {m} (wide : Bool) (w B r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineWholeStepApplicationIffSentence wide w B r V)) := ZFReplay.replay (packetAffineWholeStepApplicationIff_kernel_certificate wide w B r V)

def packetAllInternalAffineApplicationsLawSentence {m} (wide : Bool) (w B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B).imp ((PacketAffineApplicationLawSyntax.allLaw wide w B)))).close

theorem source_packetAllInternalAffineApplicationsLaw {m} (wide : Bool) (w B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAllInternalAffineApplicationsLawSentence wide w B) := by
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
  exact PacketAffineApplicationLaws.all_law hZ wide w B h0 h1

theorem packetAllInternalAffineApplicationsLaw_kernel_certificate {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAllInternalAffineApplicationsLawSentence wide w B)) := TheoryTransport.sentence (source_packetAllInternalAffineApplicationsLaw wide w B)

theorem native_packetAllInternalAffineApplicationsLaw {m} (wide : Bool) (w B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAllInternalAffineApplicationsLawSentence wide w B)) := ZFReplay.replay (packetAllInternalAffineApplicationsLaw_kernel_certificate wide w B)

def packetAffineLiteralApplicationSystemExistsSentence {m} (wide : Bool) (w : Fin m) : Source.Sentence := ((omega w).imp ((PacketAffineApplicationLawSyntax.existsSystem wide w))).close

theorem source_packetAffineLiteralApplicationSystemExists {m} (wide : Bool) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (packetAffineLiteralApplicationSystemExistsSentence wide w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact PacketAffineApplicationLaws.exists_system hZ wide w h0

theorem packetAffineLiteralApplicationSystemExists_kernel_certificate {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (packetAffineLiteralApplicationSystemExistsSentence wide w)) := TheoryTransport.sentence (source_packetAffineLiteralApplicationSystemExists wide w)

theorem native_packetAffineLiteralApplicationSystemExists {m} (wide : Bool) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (packetAffineLiteralApplicationSystemExistsSentence wide w)) := ZFReplay.replay (packetAffineLiteralApplicationSystemExists_kernel_certificate wide w)

def originalRuleApplicationRowNaturalSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r V : Fin m) : Source.Sentence := ((omega w).imp ((HornApplicationSyntax.application rule w r V).imp ((Formula.mem r w)))).close

theorem source_originalRuleApplicationRowNatural {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalRuleApplicationRowNaturalSentence rule w r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application rule w r V) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornApplicationSyntax.application rule w r V) := .hyp (Or.inl rfl)
  exact HornApplicationRange.range hZ rule w r V h0 h1

theorem originalRuleApplicationRowNatural_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalRuleApplicationRowNaturalSentence rule w r V)) := TheoryTransport.sentence (source_originalRuleApplicationRowNatural rule w r V)

theorem native_originalRuleApplicationRowNatural {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalRuleApplicationRowNaturalSentence rule w r V)) := ZFReplay.replay (originalRuleApplicationRowNatural_kernel_certificate rule w r V)

def originalRuleRejectNonNaturalRowSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r V : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem r w).neg).imp (((HornApplicationSyntax.application rule w r V).neg)))).close

theorem source_originalRuleRejectNonNaturalRow {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalRuleRejectNonNaturalRowSentence rule w r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem r w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem r w).neg) := .hyp (Or.inl rfl)
  exact HornApplicationRange.reject hZ rule w r V h0 h1

theorem originalRuleRejectNonNaturalRow_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalRuleRejectNonNaturalRowSentence rule w r V)) := TheoryTransport.sentence (source_originalRuleRejectNonNaturalRow rule w r V)

theorem native_originalRuleRejectNonNaturalRow {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalRuleRejectNonNaturalRowSentence rule w r V)) := ZFReplay.replay (originalRuleRejectNonNaturalRow_kernel_certificate rule w r V)

end PPAC.Migration.Internal.ObjectPacketAffineApplication
