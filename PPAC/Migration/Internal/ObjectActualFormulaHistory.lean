import PPAC.Migration.Internal.OriginalLogicalFromInduction

/-! 实际递归历史读取、对象归纳比较构造及内部历史存在的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectActualFormulaHistory
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def actualHistoryReadExecutedIffSentence {m} (w h D x R S a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((OrdinalSyntax.ordinal D).imp ((Formula.mem x D).imp ((FormulaTransformRecursionSyntax.graph w h D).imp (((FormulaTransformHistorySyntax.read w h x R S a b c d q).iff (FormulaTransformExecutionSyntax.executed w R S a b c d x q))))))).close

theorem source_actualHistoryReadExecutedIff {m} (w h D x R S a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualHistoryReadExecutedIffSentence w h D x R S a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h D) (Context.add (Formula.mem x D) (Context.add (OrdinalSyntax.ordinal D) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OrdinalSyntax.ordinal D) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem x D) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (FormulaTransformRecursionSyntax.graph w h D) := .hyp (Or.inl rfl)
  exact OriginalHistoryRead.read_iff_executed hZ w h D x R S a b c d q h0 h1 h2 h3

theorem actualHistoryReadExecutedIff_kernel_certificate {m} (w h D x R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualHistoryReadExecutedIffSentence w h D x R S a b c d q)) := TheoryTransport.sentence (source_actualHistoryReadExecutedIff w h D x R S a b c d q)

theorem native_actualHistoryReadExecutedIff {m} (w h D x R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualHistoryReadExecutedIffSentence w h D x R S a b c d q)) := ZFReplay.replay (actualHistoryReadExecutedIff_kernel_certificate w h D x R S a b c d q)

def prefixInductionAtSentence {m} (w mode depth parameter R S a b c d n x X : Fin m) : Source.Sentence := ((OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n).imp ((Formula.mem x n).imp ((FormulaCodeSyntax.formulaCode w x a b).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter x X).iff (FormulaTransformExecutionSyntax.executed w R S a b c d x X)))))).close

theorem source_prefixInductionAt {m} (w mode depth parameter R S a b c d n x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (prefixInductionAtSentence w mode depth parameter R S a b c d n x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w x a b) (Context.add (Formula.mem x n) (Context.add (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w x a b) := .hyp (Or.inl rfl)
  exact OriginalFormulaInductionSyntax.prefixIH_at w mode depth parameter R S a b c d n x X h0 h1 h2

theorem prefixInductionAt_kernel_certificate {m} (w mode depth parameter R S a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (prefixInductionAtSentence w mode depth parameter R S a b c d n x X)) := TheoryTransport.sentence (source_prefixInductionAt w mode depth parameter R S a b c d n x X)

theorem native_prefixInductionAt {m} (w mode depth parameter R S a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (prefixInductionAtSentence w mode depth parameter R S a b c d n x X)) := ZFReplay.replay (prefixInductionAt_kernel_certificate w mode depth parameter R S a b c d n x X)

def actualHistoryAgreementFromInductionSentence {m} (w mode depth parameter h R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((OrdinalSyntax.ordinal n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp ((OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n).imp ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n)))))).close

theorem source_actualHistoryAgreementFromInduction {m} (w mode depth parameter h R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualHistoryAgreementFromInductionSentence w mode depth parameter h R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) (Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) := .hyp (Or.inl rfl)
  exact OriginalHistoryFromInduction.from_graph hZ w mode depth parameter h R S a b c d n h0 h1 h2 h3

theorem actualHistoryAgreementFromInduction_kernel_certificate {m} (w mode depth parameter h R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualHistoryAgreementFromInductionSentence w mode depth parameter h R S a b c d n)) := TheoryTransport.sentence (source_actualHistoryAgreementFromInduction w mode depth parameter h R S a b c d n)

theorem native_actualHistoryAgreementFromInduction {m} (w mode depth parameter h R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualHistoryAgreementFromInductionSentence w mode depth parameter h R S a b c d n)) := ZFReplay.replay (actualHistoryAgreementFromInduction_kernel_certificate w mode depth parameter h R S a b c d n)

def agreedActualHistoryExistsSentence {m} (w mode depth parameter R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n).imp ((OriginalFormulaInductionSyntax.agreedHistory w mode depth parameter R S a b c d n))))).close

theorem source_agreedActualHistoryExists {m} (w mode depth parameter R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (agreedActualHistoryExistsSentence w mode depth parameter R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) := .hyp (Or.inl rfl)
  exact OriginalHistoryFromInduction.exists_agreed_history hZ w mode depth parameter R S a b c d n h0 h1 h2

theorem agreedActualHistoryExists_kernel_certificate {m} (w mode depth parameter R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (agreedActualHistoryExistsSentence w mode depth parameter R S a b c d n)) := TheoryTransport.sentence (source_agreedActualHistoryExists w mode depth parameter R S a b c d n)

theorem native_agreedActualHistoryExists {m} (w mode depth parameter R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (agreedActualHistoryExistsSentence w mode depth parameter R S a b c d n)) := ZFReplay.replay (agreedActualHistoryExists_kernel_certificate w mode depth parameter R S a b c d n)

def negationActualHistoryFromInductionIffSentence {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp ((OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.single 4 false w h R S a b c d n q)))))))))).close

theorem source_negationActualHistoryFromInductionIff {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationActualHistoryFromInductionIffSentence three w mode depth parameter h R S a b c d n q x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) (Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) := .hyp (Or.inl rfl)
  exact OriginalLogicalFromInduction.negation_iff hZ three w mode depth parameter h R S a b c d n q x h0 h1 h2 h3 h4 h5 h6

theorem negationActualHistoryFromInductionIff_kernel_certificate {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationActualHistoryFromInductionIffSentence three w mode depth parameter h R S a b c d n q x)) := TheoryTransport.sentence (source_negationActualHistoryFromInductionIff three w mode depth parameter h R S a b c d n q x)

theorem native_negationActualHistoryFromInductionIff {m} (three : Bool)  (w mode depth parameter h R S a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationActualHistoryFromInductionIffSentence three w mode depth parameter h R S a b c d n q x)) := ZFReplay.replay (negationActualHistoryFromInductionIff_kernel_certificate three w mode depth parameter h R S a b c d n q x)

def binaryActualHistoryFromInductionIffSentence {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp ((OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.binary kind w h R S a b c d n q)))))))))).close

theorem source_binaryActualHistoryFromInductionIff {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryActualHistoryFromInductionIffSentence three kind w mode depth parameter h R S a b c d n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) (Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n) := .hyp (Or.inl rfl)
  exact OriginalLogicalFromInduction.binary_iff hZ three kind w mode depth parameter h R S a b c d n q x y h0 h1 h2 h3 h4 h5 h6

theorem binaryActualHistoryFromInductionIff_kernel_certificate {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryActualHistoryFromInductionIffSentence three kind w mode depth parameter h R S a b c d n q x y)) := TheoryTransport.sentence (source_binaryActualHistoryFromInductionIff three kind w mode depth parameter h R S a b c d n q x y)

theorem native_binaryActualHistoryFromInductionIff {m} (three : Bool) (kind : Fin 4) (w mode depth parameter h R S a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryActualHistoryFromInductionIffSentence three kind w mode depth parameter h R S a b c d n q x y)) := ZFReplay.replay (binaryActualHistoryFromInductionIff_kernel_certificate three kind w mode depth parameter h R S a b c d n q x y)

end PPAC.Migration.Internal.ObjectActualFormulaHistory
