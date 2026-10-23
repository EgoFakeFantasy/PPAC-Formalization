import PPAC.Migration.Internal.PureSyntaxBinaryComplete

/-! 四种二元逻辑规则及查询构造的原核证书；统一对象IH尚未消去。 -/
namespace PPAC.Migration.Internal.ObjectPureSyntaxBinary
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def formulaCorrectInstanceSentence {m} (w n b f : Fin m) : Source.Sentence := ((PureSyntaxFormulaInductionSyntax.correct w n).imp (((PureSyntaxTrace.formula w b f n).iff (FormulaCodeSyntax.formulaCode w n b f)))).close

theorem source_formulaCorrectInstance {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaCorrectInstanceSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxFormulaInductionSyntax.correct w n) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (PureSyntaxFormulaInductionSyntax.correct w n) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaInductionSyntax.correct_at w n b f h0

theorem formulaCorrectInstance_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaCorrectInstanceSentence w n b f)) := TheoryTransport.sentence (source_formulaCorrectInstance w n b f)

theorem native_formulaCorrectInstance {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaCorrectInstanceSentence w n b f)) := ZFReplay.replay (formulaCorrectInstance_kernel_certificate w n b f)

def formulaStrictIHInstanceSentence {m} (w n x b f : Fin m) : Source.Sentence := ((PureSyntaxFormulaInductionSyntax.allIH w n).imp ((Formula.mem x n).imp (((PureSyntaxTrace.formula w b f x).iff (FormulaCodeSyntax.formulaCode w x b f))))).close

theorem source_formulaStrictIHInstance {m} (w n x b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaStrictIHInstanceSentence w n x b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem x n) (Context.add (PureSyntaxFormulaInductionSyntax.allIH w n) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (PureSyntaxFormulaInductionSyntax.allIH w n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem x n) := .hyp (Or.inl rfl)
  exact PureSyntaxFormulaInductionSyntax.correct_at w x b f (PureSyntaxFormulaInductionSyntax.allIH_at w n x h0 h1)

theorem formulaStrictIHInstance_kernel_certificate {m} (w n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaStrictIHInstanceSentence w n x b f)) := TheoryTransport.sentence (source_formulaStrictIHInstance w n x b f)

theorem native_formulaStrictIHInstance {m} (w n x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaStrictIHInstanceSentence w n x b f)) := ZFReplay.replay (formulaStrictIHInstance_kernel_certificate w n x b f)

def binaryInputExpressionIffSentence {m} (kind : Fin 4) (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w (PureSyntaxTrace.four b f x y)).imp (((HornExprSyntax.graph (PureSyntaxBinaryRule.input kind) w (PureSyntaxTrace.four b f x y) n).iff (SyntaxLogicalSyntax.binaryCode kind w x y n))))).close

theorem source_binaryInputExpressionIff {m} (kind : Fin 4) (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryInputExpressionIffSentence kind w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 4 w (PureSyntaxTrace.four b f x y)) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w (PureSyntaxTrace.four b f x y)) := .hyp (Or.inl rfl)
  exact PureSyntaxBinaryRule.input_iff hZ kind w n (PureSyntaxTrace.four b f x y) h0 h1

theorem binaryInputExpressionIff_kernel_certificate {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryInputExpressionIffSentence kind w b f x y n)) := TheoryTransport.sentence (source_binaryInputExpressionIff kind w b f x y n)

theorem native_binaryInputExpressionIff {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryInputExpressionIffSentence kind w b f x y n)) := ZFReplay.replay (binaryInputExpressionIff_kernel_certificate kind w b f x y n)

def binaryKnownTypeIffSentence {m} (kind : Fin 4) (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp (((FormulaCodeSyntax.formulaCode w n b f).iff (FormulaCodeBranchSyntax.binaryTypes w b f x y))))).close

theorem source_binaryKnownTypeIff {m} (kind : Fin 4) (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryKnownTypeIffSentence kind w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact PureSyntaxBinaryRule.known_iff hZ kind w b f x y n h0 h1

theorem binaryKnownTypeIff_kernel_certificate {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryKnownTypeIffSentence kind w b f x y n)) := TheoryTransport.sentence (source_binaryKnownTypeIff kind w b f x y n)

theorem native_binaryKnownTypeIff {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryKnownTypeIffSentence kind w b f x y n)) := ZFReplay.replay (binaryKnownTypeIff_kernel_certificate kind w b f x y n)

def binaryActualApplicationSoundSentence {m} (kind : Fin 4) (w b f n r R : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxFormulaInductionSyntax.allIH w n).imp ((RestrictionSyntax.subset R w).imp ((PureSyntaxTrace.closed w R).imp ((PureSyntaxTrace.formulaRow w b f n r).imp ((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) w r R).imp ((FormulaCodeSyntax.formulaCode w n b f)))))))).close

theorem source_binaryActualApplicationSound {m} (kind : Fin 4) (w b f n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryActualApplicationSoundSentence kind w b f n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) w r R) (Context.add (PureSyntaxTrace.formulaRow w b f n r) (Context.add (PureSyntaxTrace.closed w R) (Context.add (RestrictionSyntax.subset R w) (Context.add (PureSyntaxFormulaInductionSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
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
  have h5 : Derives Δ (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.binaryRule (SyntaxLogicalSyntax.binaryTag kind)) w r R) := .hyp (Or.inl rfl)
  exact PureSyntaxBinaryRule.application_sound hZ kind w b f n r R h0 h1 h2 h3 h4 h5

theorem binaryActualApplicationSound_kernel_certificate {m} (kind : Fin 4) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryActualApplicationSoundSentence kind w b f n r R)) := TheoryTransport.sentence (source_binaryActualApplicationSound kind w b f n r R)

theorem native_binaryActualApplicationSound {m} (kind : Fin 4) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryActualApplicationSoundSentence kind w b f n r R)) := ZFReplay.replay (binaryActualApplicationSound_kernel_certificate kind w b f n r R)

def binaryActualChildTracesMergedSentence {m} (kind : Fin 4) (w b f x y n r p q : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w (PureSyntaxTrace.four b f x y)).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((PureSyntaxTrace.formulaRow w b f n r).imp ((PureSyntaxTrace.formulaRow w b f x p).imp ((PureSyntaxTrace.formulaRow w b f y q).imp ((PureSyntaxTrace.condition w p).imp ((PureSyntaxTrace.condition w q).imp ((PureSyntaxTrace.condition w r)))))))))).close

theorem source_binaryActualChildTracesMerged {m} (kind : Fin 4) (w b f x y n r p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryActualChildTracesMergedSentence kind w b f x y n r p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.condition w q) (Context.add (PureSyntaxTrace.condition w p) (Context.add (PureSyntaxTrace.formulaRow w b f y q) (Context.add (PureSyntaxTrace.formulaRow w b f x p) (Context.add (PureSyntaxTrace.formulaRow w b f n r) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (HornExprSyntax.environmentNat 4 w (PureSyntaxTrace.four b f x y)) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w (PureSyntaxTrace.four b f x y)) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (PureSyntaxTrace.formulaRow w b f n r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (PureSyntaxTrace.formulaRow w b f x p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (PureSyntaxTrace.formulaRow w b f y q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (PureSyntaxTrace.condition w p) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (PureSyntaxTrace.condition w q) := .hyp (Or.inl rfl)
  exact PureSyntaxBinaryComplete.condition_from_rows hZ kind w n r p q (PureSyntaxTrace.four b f x y) h0 h1 h2 h3 h4 h5 h6 h7

theorem binaryActualChildTracesMerged_kernel_certificate {m} (kind : Fin 4) (w b f x y n r p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryActualChildTracesMergedSentence kind w b f x y n r p q)) := TheoryTransport.sentence (source_binaryActualChildTracesMerged kind w b f x y n r p q)

theorem native_binaryActualChildTracesMerged {m} (kind : Fin 4) (w b f x y n r p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryActualChildTracesMergedSentence kind w b f x y n r p q)) := ZFReplay.replay (binaryActualChildTracesMerged_kernel_certificate kind w b f x y n r p q)

def binaryQueryFromActualChildrenSentence {m} (kind : Fin 4) (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w x b f).imp ((FormulaCodeSyntax.formulaCode w y b f).imp ((PureSyntaxTrace.formula w b f x).imp ((PureSyntaxTrace.formula w b f y).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((PureSyntaxTrace.formula w b f n)))))))).close

theorem source_binaryQueryFromActualChildren {m} (kind : Fin 4) (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryQueryFromActualChildrenSentence kind w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (PureSyntaxTrace.formula w b f y) (Context.add (PureSyntaxTrace.formula w b f x) (Context.add (FormulaCodeSyntax.formulaCode w y b f) (Context.add (FormulaCodeSyntax.formulaCode w x b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w x b f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w y b f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (PureSyntaxTrace.formula w b f x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (PureSyntaxTrace.formula w b f y) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact PureSyntaxBinaryComplete.checked_from_children hZ kind w b f x y n h0 h1 h2 h3 h4 h5

theorem binaryQueryFromActualChildren_kernel_certificate {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryQueryFromActualChildrenSentence kind w b f x y n)) := TheoryTransport.sentence (source_binaryQueryFromActualChildren kind w b f x y n)

theorem native_binaryQueryFromActualChildren {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryQueryFromActualChildrenSentence kind w b f x y n)) := ZFReplay.replay (binaryQueryFromActualChildren_kernel_certificate kind w b f x y n)

def binaryQueryFromStrictInductionSentence {m} (kind : Fin 4) (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxFormulaInductionSyntax.allIH w n).imp ((FormulaCodeSyntax.formulaCode w n b f).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((PureSyntaxTrace.formula w b f n)))))).close

theorem source_binaryQueryFromStrictInduction {m} (kind : Fin 4) (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryQueryFromStrictInductionSentence kind w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (FormulaCodeSyntax.formulaCode w n b f) (Context.add (PureSyntaxFormulaInductionSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PureSyntaxFormulaInductionSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n b f) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact PureSyntaxBinaryComplete.typed_binary_checked hZ kind w b f x y n h0 h1 h2 h3

theorem binaryQueryFromStrictInduction_kernel_certificate {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryQueryFromStrictInductionSentence kind w b f x y n)) := TheoryTransport.sentence (source_binaryQueryFromStrictInduction kind w b f x y n)

theorem native_binaryQueryFromStrictInduction {m} (kind : Fin 4) (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryQueryFromStrictInductionSentence kind w b f x y n)) := ZFReplay.replay (binaryQueryFromStrictInduction_kernel_certificate kind w b f x y n)

end PPAC.Migration.Internal.ObjectPureSyntaxBinary
