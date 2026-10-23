import PPAC.Migration.Internal.OriginalLogicalProgram

/-! 非量词连接词的实际历史条件桥、完整分派及源子码类型的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectOriginalLogicalProgram
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def logicalHistoryAgreementAtSentence {m} (w mode depth parameter h R S a b c d n x X : Fin m) : Source.Sentence := ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n).imp ((Formula.mem x n).imp ((FormulaCodeSyntax.formulaCode w x a b).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter x X).iff (FormulaTransformHistorySyntax.read w h x R S a b c d X)))))).close

theorem source_logicalHistoryAgreementAt {m} (w mode depth parameter h R S a b c d n x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalHistoryAgreementAtSentence w mode depth parameter h R S a b c d n x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w x a b) (Context.add (Formula.mem x n) (Context.add (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w x a b) := .hyp (Or.inl rfl)
  exact OriginalFormulaHistoryAgreementSyntax.agreement_at w mode depth parameter h R S a b c d n x X h0 h1 h2

theorem logicalHistoryAgreementAt_kernel_certificate {m} (w mode depth parameter h R S a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalHistoryAgreementAtSentence w mode depth parameter h R S a b c d n x X)) := TheoryTransport.sentence (source_logicalHistoryAgreementAt w mode depth parameter h R S a b c d n x X)

theorem native_logicalHistoryAgreementAt {m} (w mode depth parameter h R S a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalHistoryAgreementAtSentence w mode depth parameter h R S a b c d n x X)) := ZFReplay.replay (logicalHistoryAgreementAt_kernel_certificate w mode depth parameter h R S a b c d n x X)

def negationChildFormulaCodeSentence {m} (w a b n x : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((FormulaCodeSyntax.formulaCode w x a b))))).close

theorem source_negationChildFormulaCode {m} (w a b n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationChildFormulaCodeSentence w a b n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inl rfl)
  exact OriginalLogicalChildTypes.negation hZ w a b n x h0 h1 h2

theorem negationChildFormulaCode_kernel_certificate {m} (w a b n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationChildFormulaCodeSentence w a b n x)) := TheoryTransport.sentence (source_negationChildFormulaCode w a b n x)

theorem native_negationChildFormulaCode {m} (w a b n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationChildFormulaCodeSentence w a b n x)) := ZFReplay.replay (negationChildFormulaCode_kernel_certificate w a b n x)

def binaryChildrenFormulaCodeSentence {m} (kind : Fin 4) (w a b n x y : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp (((FormulaCodeSyntax.formulaCode w x a b).conj (FormulaCodeSyntax.formulaCode w y a b)))))).close

theorem source_binaryChildrenFormulaCode {m} (kind : Fin 4) (w a b n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryChildrenFormulaCodeSentence kind w a b n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact OriginalLogicalChildTypes.binary hZ kind w a b n x y h0 h1 h2

theorem binaryChildrenFormulaCode_kernel_certificate {m} (kind : Fin 4) (w a b n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryChildrenFormulaCodeSentence kind w a b n x y)) := TheoryTransport.sentence (source_binaryChildrenFormulaCode kind w a b n x y)

theorem native_binaryChildrenFormulaCode {m} (kind : Fin 4) (w a b n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryChildrenFormulaCodeSentence kind w a b n x y)) := ZFReplay.replay (binaryChildrenFormulaCode_kernel_certificate kind w a b n x y)

def negationLocalHistoryIffSentence {m} (w mode depth parameter h R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n).imp (((OriginalFormulaCaseSyntax.unaryCase 4 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.single 4 false w h R S a b c d n q)))))).close

theorem source_negationLocalHistoryIff {m} (w mode depth parameter h R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationLocalHistoryIffSentence w mode depth parameter h R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) := .hyp (Or.inl rfl)
  exact OriginalLogicalCaseBridge.negation_iff hZ w mode depth parameter h R S a b c d n q h0 h1 h2

theorem negationLocalHistoryIff_kernel_certificate {m} (w mode depth parameter h R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationLocalHistoryIffSentence w mode depth parameter h R S a b c d n q)) := TheoryTransport.sentence (source_negationLocalHistoryIff w mode depth parameter h R S a b c d n q)

theorem native_negationLocalHistoryIff {m} (w mode depth parameter h R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationLocalHistoryIffSentence w mode depth parameter h R S a b c d n q)) := ZFReplay.replay (negationLocalHistoryIff_kernel_certificate w mode depth parameter h R S a b c d n q)

def negationWholeRunDispatchIffSentence {m} (three : Bool)  (w mode depth parameter n q x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaCaseSyntax.unaryCase 4 w mode depth parameter n q))))))).close

theorem source_negationWholeRunDispatchIff {m} (three : Bool)  (w mode depth parameter n q x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationWholeRunDispatchIffSentence three w mode depth parameter n q x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inl rfl)
  exact OriginalLogicalRunDispatch.run_iff_negation hZ three w mode depth parameter n q x h0 h1 (.conjL h2) (.conjR h2) h3

theorem negationWholeRunDispatchIff_kernel_certificate {m} (three : Bool)  (w mode depth parameter n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationWholeRunDispatchIffSentence three w mode depth parameter n q x)) := TheoryTransport.sentence (source_negationWholeRunDispatchIff three w mode depth parameter n q x)

theorem native_negationWholeRunDispatchIff {m} (three : Bool)  (w mode depth parameter n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationWholeRunDispatchIffSentence three w mode depth parameter n q x)) := ZFReplay.replay (negationWholeRunDispatchIff_kernel_certificate three w mode depth parameter n q x)

def negationWholeRunHistoryConditionalIffSentence {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.single 4 false w h R S a b c d n q))))))))).close

theorem source_negationWholeRunHistoryConditionalIff {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationWholeRunHistoryConditionalIffSentence three w mode depth parameter h R S a b c d n q x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) := .hyp (Or.inl rfl)
  exact OriginalLogicalProgram.negation_iff hZ three w mode depth parameter h R S a b c d n q x h0 h1 h2 h3 h4 h5

theorem negationWholeRunHistoryConditionalIff_kernel_certificate {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationWholeRunHistoryConditionalIffSentence three w mode depth parameter h R S a b c d n q x)) := TheoryTransport.sentence (source_negationWholeRunHistoryConditionalIff three w mode depth parameter h R S a b c d n q x)

theorem native_negationWholeRunHistoryConditionalIff {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationWholeRunHistoryConditionalIffSentence three w mode depth parameter h R S a b c d n q x)) := ZFReplay.replay (negationWholeRunHistoryConditionalIff_kernel_certificate three w mode depth parameter h R S a b c d n q x)

def binaryLocalHistoryIffSentence {m} (kind : Fin 4) (w mode depth parameter h R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n).imp (((OriginalFormulaCaseSyntax.binaryCase (SyntaxLogicalSyntax.binaryTag kind) 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.binary kind w h R S a b c d n q)))))).close

theorem source_binaryLocalHistoryIff {m} (kind : Fin 4) (w mode depth parameter h R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryLocalHistoryIffSentence kind w mode depth parameter h R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) := .hyp (Or.inl rfl)
  exact OriginalLogicalCaseBridge.binary_iff hZ kind w mode depth parameter h R S a b c d n q h0 h1 h2

theorem binaryLocalHistoryIff_kernel_certificate {m} (kind : Fin 4) (w mode depth parameter h R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryLocalHistoryIffSentence kind w mode depth parameter h R S a b c d n q)) := TheoryTransport.sentence (source_binaryLocalHistoryIff kind w mode depth parameter h R S a b c d n q)

theorem native_binaryLocalHistoryIff {m} (kind : Fin 4) (w mode depth parameter h R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryLocalHistoryIffSentence kind w mode depth parameter h R S a b c d n q)) := ZFReplay.replay (binaryLocalHistoryIff_kernel_certificate kind w mode depth parameter h R S a b c d n q)

def binaryWholeRunDispatchIffSentence {m} (three : Bool) (kind : Fin 4) (w mode depth parameter n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaCaseSyntax.binaryCase (SyntaxLogicalSyntax.binaryTag kind) 3 w mode depth parameter n q))))))).close

theorem source_binaryWholeRunDispatchIff {m} (three : Bool) (kind : Fin 4) (w mode depth parameter n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryWholeRunDispatchIffSentence three kind w mode depth parameter n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact OriginalLogicalRunDispatch.run_iff_binary hZ three kind w mode depth parameter n q x y h0 h1 (.conjL h2) (.conjR h2) h3

theorem binaryWholeRunDispatchIff_kernel_certificate {m} (three : Bool) (kind : Fin 4) (w mode depth parameter n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryWholeRunDispatchIffSentence three kind w mode depth parameter n q x y)) := TheoryTransport.sentence (source_binaryWholeRunDispatchIff three kind w mode depth parameter n q x y)

theorem native_binaryWholeRunDispatchIff {m} (three : Bool) (kind : Fin 4) (w mode depth parameter n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryWholeRunDispatchIffSentence three kind w mode depth parameter n q x y)) := ZFReplay.replay (binaryWholeRunDispatchIff_kernel_certificate three kind w mode depth parameter n q x y)

def binaryWholeRunHistoryConditionalIffSentence {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.binary kind w h R S a b c d n q))))))))).close

theorem source_binaryWholeRunHistoryConditionalIff {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryWholeRunHistoryConditionalIffSentence three kind w mode depth parameter h R S a b c d n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n) := .hyp (Or.inl rfl)
  exact OriginalLogicalProgram.binary_iff hZ three kind w mode depth parameter h R S a b c d n q x y h0 h1 h2 h3 h4 h5

theorem binaryWholeRunHistoryConditionalIff_kernel_certificate {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryWholeRunHistoryConditionalIffSentence three kind w mode depth parameter h R S a b c d n q x y)) := TheoryTransport.sentence (source_binaryWholeRunHistoryConditionalIff three kind w mode depth parameter h R S a b c d n q x y)

theorem native_binaryWholeRunHistoryConditionalIff {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryWholeRunHistoryConditionalIffSentence three kind w mode depth parameter h R S a b c d n q x y)) := ZFReplay.replay (binaryWholeRunHistoryConditionalIff_kernel_certificate three kind w mode depth parameter h R S a b c d n q x y)

end PPAC.Migration.Internal.ObjectOriginalLogicalProgram
