import PPAC.Migration.Internal.PureSyntaxUnaryComplete

/-! 否定及两量词的实际原规则、内部后继界和带对象IH的闭句证书。 -/
namespace PPAC.Migration.Internal.ObjectPureSyntaxUnary
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def unaryInputExpressionIffSentence {m} (kind : Fin 3) (w b f x n : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f x)).imp (((HornExprSyntax.graph (PureSyntaxUnarySyntax.input kind) w (SyntaxAtomSyntax.three b f x) n).iff (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n))))).close

theorem source_unaryInputExpressionIff {m} (kind : Fin 3) (w b f x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryInputExpressionIffSentence kind w b f x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f x)) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f x)) := .hyp (Or.inl rfl)
  exact PureSyntaxUnarySyntax.input_iff hZ kind w n (SyntaxAtomSyntax.three b f x) h0 h1

theorem unaryInputExpressionIff_kernel_certificate {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryInputExpressionIffSentence kind w b f x n)) := TheoryTransport.sentence (source_unaryInputExpressionIff kind w b f x n)

theorem native_unaryInputExpressionIff {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryInputExpressionIffSentence kind w b f x n)) := ZFReplay.replay (unaryInputExpressionIff_kernel_certificate kind w b f x n)

def unaryKnownTypeIffSentence {m} (kind : Fin 3) (w b f x n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n).imp (((FormulaCodeSyntax.formulaCode w n b f).iff (FormulaCodeBranchSyntax.singleTypes (PureSyntaxUnarySyntax.advance kind) w b f x))))).close

theorem source_unaryKnownTypeIff {m} (kind : Fin 3) (w b f x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryKnownTypeIffSentence kind w b f x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) := .hyp (Or.inl rfl)
  exact PureSyntaxUnarySyntax.known_iff hZ kind w b f x n h0 h1

theorem unaryKnownTypeIff_kernel_certificate {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryKnownTypeIffSentence kind w b f x n)) := TheoryTransport.sentence (source_unaryKnownTypeIff kind w b f x n)

theorem native_unaryKnownTypeIff {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryKnownTypeIffSentence kind w b f x n)) := ZFReplay.replay (unaryKnownTypeIff_kernel_certificate kind w b f x n)

def unaryActualApplicationSoundSentence {m} (kind : Fin 3) (w b f n r R : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxFormulaInductionSyntax.allIH w n).imp ((RestrictionSyntax.subset R w).imp ((PureSyntaxTrace.closed w R).imp ((PureSyntaxTrace.formulaRow w b f n r).imp ((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.unaryRule (PureSyntaxUnarySyntax.tag kind) (PureSyntaxUnarySyntax.advance kind)) w r R).imp ((FormulaCodeSyntax.formulaCode w n b f)))))))).close

theorem source_unaryActualApplicationSound {m} (kind : Fin 3) (w b f n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryActualApplicationSoundSentence kind w b f n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.unaryRule (PureSyntaxUnarySyntax.tag kind) (PureSyntaxUnarySyntax.advance kind)) w r R) (Context.add (PureSyntaxTrace.formulaRow w b f n r) (Context.add (PureSyntaxTrace.closed w R) (Context.add (RestrictionSyntax.subset R w) (Context.add (PureSyntaxFormulaInductionSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (PureSyntaxFormulaInductionSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (RestrictionSyntax.subset R w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureSyntaxTrace.closed w R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PureSyntaxTrace.formulaRow w b f n r) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.unaryRule (PureSyntaxUnarySyntax.tag kind) (PureSyntaxUnarySyntax.advance kind)) w r R) := .hyp (Or.inl rfl)
  exact PureSyntaxUnaryRule.application_sound hZ kind w b f n r R h0 h1 h2 h3 h4 h5

theorem unaryActualApplicationSound_kernel_certificate {m} (kind : Fin 3) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryActualApplicationSoundSentence kind w b f n r R)) := TheoryTransport.sentence (source_unaryActualApplicationSound kind w b f n r R)

theorem native_unaryActualApplicationSound {m} (kind : Fin 3) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryActualApplicationSoundSentence kind w b f n r R)) := ZFReplay.replay (unaryActualApplicationSound_kernel_certificate kind w b f n r R)

def unaryActualChildTraceExtendedSentence {m} (kind : Fin 3) (w b f x n r p B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f x)).imp ((SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n).imp ((HornExprSyntax.graph (PureSyntaxUnarySyntax.boundExpr (PureSyntaxUnarySyntax.advance kind)) w (SyntaxAtomSyntax.three b f x) B).imp ((PureSyntaxTrace.formulaRow w b f n r).imp ((PureSyntaxTrace.formulaRow w B f x p).imp ((PureSyntaxTrace.condition w p).imp ((PureSyntaxTrace.condition w r))))))))).close

theorem source_unaryActualChildTraceExtended {m} (kind : Fin 3) (w b f x n r p B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryActualChildTraceExtendedSentence kind w b f x n r p B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.condition w p) (Context.add (PureSyntaxTrace.formulaRow w B f x p) (Context.add (PureSyntaxTrace.formulaRow w b f n r) (Context.add (HornExprSyntax.graph (PureSyntaxUnarySyntax.boundExpr (PureSyntaxUnarySyntax.advance kind)) w (SyntaxAtomSyntax.three b f x) B) (Context.add (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) (Context.add (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f x)) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w (SyntaxAtomSyntax.three b f x)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (HornExprSyntax.graph (PureSyntaxUnarySyntax.boundExpr (PureSyntaxUnarySyntax.advance kind)) w (SyntaxAtomSyntax.three b f x) B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (PureSyntaxTrace.formulaRow w b f n r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (PureSyntaxTrace.formulaRow w B f x p) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PureSyntaxTrace.condition w p) := .hyp (Or.inl rfl)
  exact PureSyntaxUnaryComplete.condition_from_row hZ kind w n r p B (SyntaxAtomSyntax.three b f x) h0 h1 h2 h3 h4 h5 h6

theorem unaryActualChildTraceExtended_kernel_certificate {m} (kind : Fin 3) (w b f x n r p B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryActualChildTraceExtendedSentence kind w b f x n r p B)) := TheoryTransport.sentence (source_unaryActualChildTraceExtended kind w b f x n r p B)

theorem native_unaryActualChildTraceExtended {m} (kind : Fin 3) (w b f x n r p B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryActualChildTraceExtendedSentence kind w b f x n r p B)) := ZFReplay.replay (unaryActualChildTraceExtended_kernel_certificate kind w b f x n r p B)

def unaryQueryFromActualChildSentence {m} (kind : Fin 3) (w b f x n B : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.contexts w b f).imp ((HornExprSyntax.graph (PureSyntaxUnarySyntax.boundExpr (PureSyntaxUnarySyntax.advance kind)) w (SyntaxAtomSyntax.three b f x) B).imp ((FormulaCodeSyntax.formulaCode w x B f).imp ((PureSyntaxTrace.formula w B f x).imp ((SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n).imp ((PureSyntaxTrace.formula w b f n)))))))).close

theorem source_unaryQueryFromActualChild {m} (kind : Fin 3) (w b f x n B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryQueryFromActualChildSentence kind w b f x n B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) (Context.add (PureSyntaxTrace.formula w B f x) (Context.add (FormulaCodeSyntax.formulaCode w x B f) (Context.add (HornExprSyntax.graph (PureSyntaxUnarySyntax.boundExpr (PureSyntaxUnarySyntax.advance kind)) w (SyntaxAtomSyntax.three b f x) B) (Context.add (SyntaxTermSyntax.contexts w b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxTermSyntax.contexts w b f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (HornExprSyntax.graph (PureSyntaxUnarySyntax.boundExpr (PureSyntaxUnarySyntax.advance kind)) w (SyntaxAtomSyntax.three b f x) B) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w x B f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PureSyntaxTrace.formula w B f x) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) := .hyp (Or.inl rfl)
  exact PureSyntaxUnaryComplete.checked_from_child hZ kind w b f x n B h0 h1 h2 h3 h4 h5

theorem unaryQueryFromActualChild_kernel_certificate {m} (kind : Fin 3) (w b f x n B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryQueryFromActualChildSentence kind w b f x n B)) := TheoryTransport.sentence (source_unaryQueryFromActualChild kind w b f x n B)

theorem native_unaryQueryFromActualChild {m} (kind : Fin 3) (w b f x n B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryQueryFromActualChildSentence kind w b f x n B)) := ZFReplay.replay (unaryQueryFromActualChild_kernel_certificate kind w b f x n B)

def unaryQueryFromInternalStepSentence {m} (kind : Fin 3) (w b f x n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxFormulaInductionSyntax.allIH w n).imp ((SyntaxTermSyntax.contexts w b f).imp ((FormulaCodeRecursiveSyntax.stepCheck (PureSyntaxUnarySyntax.advance kind) w x b f).imp ((SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n).imp ((PureSyntaxTrace.formula w b f n))))))).close

theorem source_unaryQueryFromInternalStep {m} (kind : Fin 3) (w b f x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryQueryFromInternalStepSentence kind w b f x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) (Context.add (FormulaCodeRecursiveSyntax.stepCheck (PureSyntaxUnarySyntax.advance kind) w x b f) (Context.add (SyntaxTermSyntax.contexts w b f) (Context.add (PureSyntaxFormulaInductionSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (PureSyntaxFormulaInductionSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxTermSyntax.contexts w b f) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeRecursiveSyntax.stepCheck (PureSyntaxUnarySyntax.advance kind) w x b f) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) := .hyp (Or.inl rfl)
  exact PureSyntaxUnaryComplete.checked_from_step hZ kind w b f x n h0 h1 h2 h3 h4

theorem unaryQueryFromInternalStep_kernel_certificate {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryQueryFromInternalStepSentence kind w b f x n)) := TheoryTransport.sentence (source_unaryQueryFromInternalStep kind w b f x n)

theorem native_unaryQueryFromInternalStep {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryQueryFromInternalStepSentence kind w b f x n)) := ZFReplay.replay (unaryQueryFromInternalStep_kernel_certificate kind w b f x n)

def unaryQueryFromStrictInductionSentence {m} (kind : Fin 3) (w b f x n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxFormulaInductionSyntax.allIH w n).imp ((FormulaCodeSyntax.formulaCode w n b f).imp ((SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n).imp ((PureSyntaxTrace.formula w b f n)))))).close

theorem source_unaryQueryFromStrictInduction {m} (kind : Fin 3) (w b f x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unaryQueryFromStrictInductionSentence kind w b f x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) (Context.add (FormulaCodeSyntax.formulaCode w n b f) (Context.add (PureSyntaxFormulaInductionSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PureSyntaxFormulaInductionSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n b f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode (PureSyntaxUnarySyntax.tag kind) w x n) := .hyp (Or.inl rfl)
  exact PureSyntaxUnaryComplete.typed_unary_checked hZ kind w b f x n h0 h1 h2 h3

theorem unaryQueryFromStrictInduction_kernel_certificate {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unaryQueryFromStrictInductionSentence kind w b f x n)) := TheoryTransport.sentence (source_unaryQueryFromStrictInduction kind w b f x n)

theorem native_unaryQueryFromStrictInduction {m} (kind : Fin 3) (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unaryQueryFromStrictInductionSentence kind w b f x n)) := ZFReplay.replay (unaryQueryFromStrictInduction_kernel_certificate kind w b f x n)

end PPAC.Migration.Internal.ObjectPureSyntaxUnary
