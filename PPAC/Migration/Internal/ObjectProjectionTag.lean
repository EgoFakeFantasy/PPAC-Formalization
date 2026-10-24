import PPAC.Migration.Internal.ProjectionTag

/-! 原三类投影规则分派、查询自然域与tag全内部候选双条件的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectProjectionTag
open Source SourceAlgebra SourceLogic OmegaSyntax

def projectionConstructorFieldNaturalSentence {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w row : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k tag w xs row).imp ((Formula.mem (xs j) w)))).close

theorem source_projectionConstructorFieldNatural {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionConstructorFieldNaturalSentence k tag xs j w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor k tag w xs row) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k tag w xs row) := .hyp (Or.inl rfl)
  exact ProjectionNodeFields.constructor_field_natural hZ k tag w row xs j h0 h1

theorem projectionConstructorFieldNatural_kernel_certificate {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionConstructorFieldNaturalSentence k tag xs j w row)) := TheoryTransport.sentence (source_projectionConstructorFieldNatural k tag xs j w row)

theorem native_projectionConstructorFieldNatural {m} (k tag : Nat) (xs : Fin k → Fin m) (j : Fin k) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionConstructorFieldNaturalSentence k tag xs j w row)) := ZFReplay.replay (projectionConstructorFieldNatural_kernel_certificate k tag xs j w row)

def projectionTagQueryNaturalSentence {m} (j : Fin 2) (w x y : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.tag w x y).imp ((Formula.mem ((SetLanguage.args2 x y) j) w)))).close

theorem source_projectionTagQueryNatural {m} (j : Fin 2) (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagQueryNaturalSentence j w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.tag w x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectionTraceSyntax.tag w x y) := .hyp (Or.inl rfl)
  exact ProjectionNodeFields.tag_natural_at hZ w x y j h0 h1

theorem projectionTagQueryNatural_kernel_certificate {m} (j : Fin 2) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagQueryNaturalSentence j w x y)) := TheoryTransport.sentence (source_projectionTagQueryNatural j w x y)

theorem native_projectionTagQueryNatural {m} (j : Fin 2) (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagQueryNaturalSentence j w x y)) := ZFReplay.replay (projectionTagQueryNatural_kernel_certificate j w x y)

def projectionGetQueryNaturalSentence {m} (j : Fin 3) (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.get w x i y).imp ((Formula.mem ((SyntaxAtomSyntax.three x i y) j) w)))).close

theorem source_projectionGetQueryNatural {m} (j : Fin 3) (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetQueryNaturalSentence j w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.get w x i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectionTraceSyntax.get w x i y) := .hyp (Or.inl rfl)
  exact ProjectionNodeFields.get_natural_at hZ w x i y j h0 h1

theorem projectionGetQueryNatural_kernel_certificate {m} (j : Fin 3) (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetQueryNaturalSentence j w x i y)) := TheoryTransport.sentence (source_projectionGetQueryNatural j w x i y)

theorem native_projectionGetQueryNatural {m} (j : Fin 3) (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetQueryNaturalSentence j w x i y)) := ZFReplay.replay (projectionGetQueryNatural_kernel_certificate j w x i y)

def projectionFieldQueryNaturalSentence {m} (j : Fin 3) (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.field w x i y).imp ((Formula.mem ((SyntaxAtomSyntax.three x i y) j) w)))).close

theorem source_projectionFieldQueryNatural {m} (j : Fin 3) (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldQueryNaturalSentence j w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.field w x i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectionTraceSyntax.field w x i y) := .hyp (Or.inl rfl)
  exact ProjectionNodeFields.field_natural_at hZ w x i y j h0 h1

theorem projectionFieldQueryNatural_kernel_certificate {m} (j : Fin 3) (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldQueryNaturalSentence j w x i y)) := TheoryTransport.sentence (source_projectionFieldQueryNatural j w x i y)

theorem native_projectionFieldQueryNatural {m} (j : Fin 3) (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldQueryNaturalSentence j w x i y)) := ZFReplay.replay (projectionFieldQueryNatural_kernel_certificate j w x i y)

def projectionTagRuleDispatchSentence {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k 0 w xs row).imp ((HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w row R).imp ((HornStepSyntax.step ProjectionRuleDispatch.tagRules w row R))))).close

theorem source_projectionTagRuleDispatch {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagRuleDispatchSentence k xs w row R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w row R) (Context.add (SyntaxNodeSyntax.constructor k 0 w xs row) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k 0 w xs row) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w row R) := .hyp (Or.inl rfl)
  exact ProjectionRuleDispatch.tag_step hZ k w row R xs h0 h1 h2

theorem projectionTagRuleDispatch_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagRuleDispatchSentence k xs w row R)) := TheoryTransport.sentence (source_projectionTagRuleDispatch k xs w row R)

theorem native_projectionTagRuleDispatch {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagRuleDispatchSentence k xs w row R)) := ZFReplay.replay (projectionTagRuleDispatch_kernel_certificate k xs w row R)

def projectionGetRuleDispatchSentence {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k 1 w xs row).imp ((HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w row R).imp ((HornStepSyntax.step ProjectionRuleDispatch.getRules w row R))))).close

theorem source_projectionGetRuleDispatch {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetRuleDispatchSentence k xs w row R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w row R) (Context.add (SyntaxNodeSyntax.constructor k 1 w xs row) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k 1 w xs row) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w row R) := .hyp (Or.inl rfl)
  exact ProjectionRuleDispatch.get_step hZ k w row R xs h0 h1 h2

theorem projectionGetRuleDispatch_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetRuleDispatchSentence k xs w row R)) := TheoryTransport.sentence (source_projectionGetRuleDispatch k xs w row R)

theorem native_projectionGetRuleDispatch {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetRuleDispatchSentence k xs w row R)) := ZFReplay.replay (projectionGetRuleDispatch_kernel_certificate k xs w row R)

def projectionFieldRuleDispatchSentence {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor k 2 w xs row).imp ((HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w row R).imp ((HornStepSyntax.step ProjectionRuleDispatch.fieldRules w row R))))).close

theorem source_projectionFieldRuleDispatch {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldRuleDispatchSentence k xs w row R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w row R) (Context.add (SyntaxNodeSyntax.constructor k 2 w xs row) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor k 2 w xs row) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornStepSyntax.step YesMetaZFC.Automation.ObjectProjection.rules w row R) := .hyp (Or.inl rfl)
  exact ProjectionRuleDispatch.field_step hZ k w row R xs h0 h1 h2

theorem projectionFieldRuleDispatch_kernel_certificate {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldRuleDispatchSentence k xs w row R)) := TheoryTransport.sentence (source_projectionFieldRuleDispatch k xs w row R)

theorem native_projectionFieldRuleDispatch {m} (k : Nat) (xs : Fin k → Fin m) (w row R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldRuleDispatchSentence k xs w row R)) := ZFReplay.replay (projectionFieldRuleDispatch_kernel_certificate k xs w row R)

def projectionTagZeroConstructedSentence {m} (w x y : Fin m) : Source.Sentence := ((omega w).imp ((empty x).imp ((empty y).imp ((ProjectionTraceSyntax.tag w x y))))).close

theorem source_projectionTagZeroConstructed {m} (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagZeroConstructedSentence w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty y) (Context.add (empty x) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty x) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty y) := .hyp (Or.inl rfl)
  exact ProjectionTag.zero_checked hZ w x y h0 h1 h2

theorem projectionTagZeroConstructed_kernel_certificate {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagZeroConstructedSentence w x y)) := TheoryTransport.sentence (source_projectionTagZeroConstructed w x y)

theorem native_projectionTagZeroConstructed {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagZeroConstructedSentence w x y)) := ZFReplay.replay (projectionTagZeroConstructed_kernel_certificate w x y)

def projectionTagRawConstructedSentence {m} (w x y b : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem y w).imp ((Formula.mem b w).imp ((StructuralNodeSyntax.raw w y b x).imp ((ProjectionTraceSyntax.tag w x y)))))).close

theorem source_projectionTagRawConstructed {m} (w x y b : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagRawConstructedSentence w x y b) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w y b x) (Context.add (Formula.mem b w) (Context.add (Formula.mem y w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem y w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (StructuralNodeSyntax.raw w y b x) := .hyp (Or.inl rfl)
  exact ProjectionTag.positive_checked hZ w x y b h0 h1 h2 h3

theorem projectionTagRawConstructed_kernel_certificate {m} (w x y b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagRawConstructedSentence w x y b)) := TheoryTransport.sentence (source_projectionTagRawConstructed w x y b)

theorem native_projectionTagRawConstructed {m} (w x y b : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagRawConstructedSentence w x y b)) := ZFReplay.replay (projectionTagRawConstructed_kernel_certificate w x y b)

def projectionTagSoundSentence {m} (w x y : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.tag w x y).imp ((PairingProjectionSyntax.step true true w x y)))).close

theorem source_projectionTagSound {m} (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagSoundSentence w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.tag w x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectionTraceSyntax.tag w x y) := .hyp (Or.inl rfl)
  exact ProjectionTag.checked_sound hZ w x y h0 h1

theorem projectionTagSound_kernel_certificate {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagSoundSentence w x y)) := TheoryTransport.sentence (source_projectionTagSound w x y)

theorem native_projectionTagSound {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagSoundSentence w x y)) := ZFReplay.replay (projectionTagSound_kernel_certificate w x y)

def projectionTagCompleteSentence {m} (w x y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((PairingProjectionSyntax.step true true w x y).imp ((ProjectionTraceSyntax.tag w x y))))).close

theorem source_projectionTagComplete {m} (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagCompleteSentence w x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PairingProjectionSyntax.step true true w x y) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (PairingProjectionSyntax.step true true w x y) := .hyp (Or.inl rfl)
  exact ProjectionTag.checked_complete hZ w x y h0 h1 h2

theorem projectionTagComplete_kernel_certificate {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagCompleteSentence w x y)) := TheoryTransport.sentence (source_projectionTagComplete w x y)

theorem native_projectionTagComplete {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagCompleteSentence w x y)) := ZFReplay.replay (projectionTagComplete_kernel_certificate w x y)

def projectionTagQueryIffSentence {m} (w x y : Fin m) : Source.Sentence := ((omega w).imp (((ProjectionTraceSyntax.tag w x y).iff ((Formula.mem x w).conj (PairingProjectionSyntax.step true true w x y))))).close

theorem source_projectionTagQueryIff {m} (w x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagQueryIffSentence w x y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectionTag.checked_iff hZ w x y h0

theorem projectionTagQueryIff_kernel_certificate {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagQueryIffSentence w x y)) := TheoryTransport.sentence (source_projectionTagQueryIff w x y)

theorem native_projectionTagQueryIff {m} (w x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagQueryIffSentence w x y)) := ZFReplay.replay (projectionTagQueryIff_kernel_certificate w x y)

def projectionTagQueryUniqueSentence {m} (w x y z : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.tag w x y).imp ((ProjectionTraceSyntax.tag w x z).imp ((Formula.equal y z))))).close

theorem source_projectionTagQueryUnique {m} (w x y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagQueryUniqueSentence w x y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.tag w x z) (Context.add (ProjectionTraceSyntax.tag w x y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectionTraceSyntax.tag w x y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectionTraceSyntax.tag w x z) := .hyp (Or.inl rfl)
  exact ProjectionTag.checked_unique hZ w x y z h0 h1 h2

theorem projectionTagQueryUnique_kernel_certificate {m} (w x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagQueryUniqueSentence w x y z)) := TheoryTransport.sentence (source_projectionTagQueryUnique w x y z)

theorem native_projectionTagQueryUnique {m} (w x y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagQueryUniqueSentence w x y z)) := ZFReplay.replay (projectionTagQueryUnique_kernel_certificate w x y z)

def projectionTagAtActualRowSoundSentence {m} (w x y row : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.tagRow w x y row).imp ((ProjectionTraceSyntax.condition w row).imp ((PairingProjectionSyntax.step true true w x y))))).close

theorem source_projectionTagAtActualRowSound {m} (w x y row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionTagAtActualRowSoundSentence w x y row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.condition w row) (Context.add (ProjectionTraceSyntax.tagRow w x y row) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectionTraceSyntax.tagRow w x y row) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectionTraceSyntax.condition w row) := .hyp (Or.inl rfl)
  exact ProjectionTagCases.condition_sound hZ w x y row h0 h1 h2

theorem projectionTagAtActualRowSound_kernel_certificate {m} (w x y row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionTagAtActualRowSoundSentence w x y row)) := TheoryTransport.sentence (source_projectionTagAtActualRowSound w x y row)

theorem native_projectionTagAtActualRowSound {m} (w x y row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionTagAtActualRowSoundSentence w x y row)) := ZFReplay.replay (projectionTagAtActualRowSound_kernel_certificate w x y row)

end PPAC.Migration.Internal.ObjectProjectionTag
