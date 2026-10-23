import PPAC.Migration.Internal.PureSyntaxEqualityComplete

/-! 纯公式常量与等式的真实规则及查询构造；完整公式查询桥尚未证明。 -/
namespace PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def constantInputExpressionIffSentence {m} (truth : Bool) (w n e0 e1 : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w (SyntaxAtomSyntax.two e0 e1)).imp (((HornExprSyntax.graph (PureSyntaxConstantRule.input truth) w (SyntaxAtomSyntax.two e0 e1) n).iff (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n))))).close

theorem source_constantInputExpressionIff {m} (truth : Bool) (w n e0 e1 : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constantInputExpressionIffSentence truth w n e0 e1) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w (SyntaxAtomSyntax.two e0 e1)) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w (SyntaxAtomSyntax.two e0 e1)) := .hyp (Or.inl rfl)
  exact PureSyntaxConstantRule.input_iff hZ truth w n (SyntaxAtomSyntax.two e0 e1) h0 h1

theorem constantInputExpressionIff_kernel_certificate {m} (truth : Bool) (w n e0 e1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constantInputExpressionIffSentence truth w n e0 e1)) := TheoryTransport.sentence (source_constantInputExpressionIff truth w n e0 e1)

theorem native_constantInputExpressionIff {m} (truth : Bool) (w n e0 e1 : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constantInputExpressionIffSentence truth w n e0 e1)) := ZFReplay.replay (constantInputExpressionIff_kernel_certificate truth w n e0 e1)

def constantApplicationIffNullarySentence {m} (truth : Bool) (w b f n r R : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxTrace.formulaRow w b f n r).imp (((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R).iff (SyntaxAtomSyntax.nullary truth w b f n))))).close

theorem source_constantApplicationIffNullary {m} (truth : Bool) (w b f n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constantApplicationIffNullarySentence truth w b f n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.formulaRow w b f n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (PureSyntaxTrace.formulaRow w b f n r) := .hyp (Or.inl rfl)
  exact PureSyntaxConstantComplete.application_iff_nullary hZ truth w b f n r R h0 h1

theorem constantApplicationIffNullary_kernel_certificate {m} (truth : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constantApplicationIffNullarySentence truth w b f n r R)) := TheoryTransport.sentence (source_constantApplicationIffNullary truth w b f n r R)

theorem native_constantApplicationIffNullary {m} (truth : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constantApplicationIffNullarySentence truth w b f n r R)) := ZFReplay.replay (constantApplicationIffNullary_kernel_certificate truth w b f n r R)

def constantApplicationSoundSentence {m} (truth : Bool) (w b f n r R : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxTrace.formulaRow w b f n r).imp ((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R).imp ((FormulaCodeSyntax.formulaCode w n b f))))).close

theorem source_constantApplicationSound {m} (truth : Bool) (w b f n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constantApplicationSoundSentence truth w b f n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R) (Context.add (PureSyntaxTrace.formulaRow w b f n r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (PureSyntaxTrace.formulaRow w b f n r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectFormulaSyntax.constantRule (SyntaxAtomSyntax.nullaryTag truth)) w r R) := .hyp (Or.inl rfl)
  exact PureSyntaxConstantRule.application_sound hZ truth w b f n r R h0 h1 h2

theorem constantApplicationSound_kernel_certificate {m} (truth : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constantApplicationSoundSentence truth w b f n r R)) := TheoryTransport.sentence (source_constantApplicationSound truth w b f n r R)

theorem native_constantApplicationSound {m} (truth : Bool) (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constantApplicationSoundSentence truth w b f n r R)) := ZFReplay.replay (constantApplicationSound_kernel_certificate truth w b f n r R)

def constantQueryConstructedSentence {m} (truth : Bool) (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.nullary truth w b f n).imp ((PureSyntaxTrace.formula w b f n)))).close

theorem source_constantQueryConstructed {m} (truth : Bool) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (constantQueryConstructedSentence truth w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.nullary truth w b f n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxAtomSyntax.nullary truth w b f n) := .hyp (Or.inl rfl)
  exact PureSyntaxConstantComplete.checked_nullary hZ truth w b f n h0 h1

theorem constantQueryConstructed_kernel_certificate {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (constantQueryConstructedSentence truth w b f n)) := TheoryTransport.sentence (source_constantQueryConstructed truth w b f n)

theorem native_constantQueryConstructed {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (constantQueryConstructedSentence truth w b f n)) := ZFReplay.replay (constantQueryConstructed_kernel_certificate truth w b f n)

def typedConstantQueryConstructedSentence {m} (truth : Bool) (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n b f).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp ((PureSyntaxTrace.formula w b f n))))).close

theorem source_typedConstantQueryConstructed {m} (truth : Bool) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedConstantQueryConstructedSentence truth w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (FormulaCodeSyntax.formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n b f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact PureSyntaxConstantComplete.typed_constant_checked hZ truth w b f n h0 h1 h2

theorem typedConstantQueryConstructed_kernel_certificate {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedConstantQueryConstructedSentence truth w b f n)) := TheoryTransport.sentence (source_typedConstantQueryConstructed truth w b f n)

theorem native_typedConstantQueryConstructed {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedConstantQueryConstructedSentence truth w b f n)) := ZFReplay.replay (typedConstantQueryConstructed_kernel_certificate truth w b f n)

def equalityInputExpressionIffSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w (PureSyntaxTrace.four b f x y)).imp (((HornExprSyntax.graph PureSyntaxEqualityRule.input w (PureSyntaxTrace.four b f x y) n).iff (SyntaxAtomSyntax.equalCode w x y n))))).close

theorem source_equalityInputExpressionIff {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityInputExpressionIffSentence w b f x y n) := by
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
  exact PureSyntaxEqualityRule.input_iff hZ w n (PureSyntaxTrace.four b f x y) h0 h1

theorem equalityInputExpressionIff_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityInputExpressionIffSentence w b f x y n)) := TheoryTransport.sentence (source_equalityInputExpressionIff w b f x y n)

theorem native_equalityInputExpressionIff {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityInputExpressionIffSentence w b f x y n)) := ZFReplay.replay (equalityInputExpressionIff_kernel_certificate w b f x y n)

def equalityApplicationSoundSentence {m} (w b f n r R : Fin m) : Source.Sentence := ((omega w).imp ((PureSyntaxTrace.closed w R).imp ((PureSyntaxTrace.formulaRow w b f n r).imp ((HornApplicationSyntax.application YesMetaZFC.Automation.ObjectFormulaSyntax.equalityRule w r R).imp ((FormulaCodeSyntax.formulaCode w n b f)))))).close

theorem source_equalityApplicationSound {m} (w b f n r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityApplicationSoundSentence w b f n r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectFormulaSyntax.equalityRule w r R) (Context.add (PureSyntaxTrace.formulaRow w b f n r) (Context.add (PureSyntaxTrace.closed w R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (PureSyntaxTrace.closed w R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (PureSyntaxTrace.formulaRow w b f n r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornApplicationSyntax.application YesMetaZFC.Automation.ObjectFormulaSyntax.equalityRule w r R) := .hyp (Or.inl rfl)
  exact PureSyntaxEqualityRule.application_sound hZ w b f n r R h0 h1 h2 h3

theorem equalityApplicationSound_kernel_certificate {m} (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityApplicationSoundSentence w b f n r R)) := TheoryTransport.sentence (source_equalityApplicationSound w b f n r R)

theorem native_equalityApplicationSound {m} (w b f n r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityApplicationSoundSentence w b f n r R)) := ZFReplay.replay (equalityApplicationSound_kernel_certificate w b f n r R)

def equalityQueryConstructedSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTermSyntax.term w b f x).imp ((SyntaxTermSyntax.term w b f y).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((PureSyntaxTrace.formula w b f n)))))).close

theorem source_equalityQueryConstructed {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityQueryConstructedSentence w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxTermSyntax.term w b f y) (Context.add (SyntaxTermSyntax.term w b f x) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTermSyntax.term w b f x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxTermSyntax.term w b f y) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inl rfl)
  exact PureSyntaxEqualityComplete.checked_equality hZ w b f x y n h0 h1 h2 h3

theorem equalityQueryConstructed_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityQueryConstructedSentence w b f x y n)) := TheoryTransport.sentence (source_equalityQueryConstructed w b f x y n)

theorem native_equalityQueryConstructed {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityQueryConstructedSentence w b f x y n)) := ZFReplay.replay (equalityQueryConstructed_kernel_certificate w b f x y n)

def typedEqualityQueryConstructedSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n b f).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((PureSyntaxTrace.formula w b f n))))).close

theorem source_typedEqualityQueryConstructed {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (typedEqualityQueryConstructedSentence w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (FormulaCodeSyntax.formulaCode w n b f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n b f) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inl rfl)
  exact PureSyntaxEqualityComplete.typed_equality_checked hZ w b f x y n h0 h1 h2

theorem typedEqualityQueryConstructed_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (typedEqualityQueryConstructedSentence w b f x y n)) := TheoryTransport.sentence (source_typedEqualityQueryConstructed w b f x y n)

theorem native_typedEqualityQueryConstructed {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (typedEqualityQueryConstructedSentence w b f x y n)) := ZFReplay.replay (typedEqualityQueryConstructed_kernel_certificate w b f x y n)

def equalityActualChildTracesMergedSentence {m} (w b f x y n r p q : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w (PureSyntaxTrace.four b f x y)).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((PureSyntaxTrace.formulaRow w b f n r).imp ((PureSyntaxTrace.termRow w b f x p).imp ((PureSyntaxTrace.termRow w b f y q).imp ((PureSyntaxTrace.condition w p).imp ((PureSyntaxTrace.condition w q).imp ((PureSyntaxTrace.condition w r)))))))))).close

theorem source_equalityActualChildTracesMerged {m} (w b f x y n r p q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityActualChildTracesMergedSentence w b f x y n r p q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureSyntaxTrace.condition w q) (Context.add (PureSyntaxTrace.condition w p) (Context.add (PureSyntaxTrace.termRow w b f y q) (Context.add (PureSyntaxTrace.termRow w b f x p) (Context.add (PureSyntaxTrace.formulaRow w b f n r) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (HornExprSyntax.environmentNat 4 w (PureSyntaxTrace.four b f x y)) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h2 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (PureSyntaxTrace.formulaRow w b f n r) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (PureSyntaxTrace.termRow w b f x p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (PureSyntaxTrace.termRow w b f y q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (PureSyntaxTrace.condition w p) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (PureSyntaxTrace.condition w q) := .hyp (Or.inl rfl)
  exact PureSyntaxEqualityComplete.condition_from_rows hZ w n r p q (PureSyntaxTrace.four b f x y) h0 h1 h2 h3 h4 h5 h6 h7

theorem equalityActualChildTracesMerged_kernel_certificate {m} (w b f x y n r p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityActualChildTracesMergedSentence w b f x y n r p q)) := TheoryTransport.sentence (source_equalityActualChildTracesMerged w b f x y n r p q)

theorem native_equalityActualChildTracesMerged {m} (w b f x y n r p q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityActualChildTracesMergedSentence w b f x y n r p q)) := ZFReplay.replay (equalityActualChildTracesMerged_kernel_certificate w b f x y n r p q)

end PPAC.Migration.Internal.ObjectPureSyntaxFormulaAtoms
