import PPAC.Migration.Internal.OriginalBinderProgram

/-! 原两个量词子运行、真实advanced程序、完整分派及统一对象归纳接口的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectOriginalBinderProgram
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def naturalSuccessorWitnessSentence {m} (w x : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((stepIn w x)))).close

theorem source_naturalSuccessorWitness {m} (w x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalSuccessorWitnessSentence w x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inl rfl)
  exact OriginalBinderStepSyntax.successor_exists w x h0 h1

theorem naturalSuccessorWitness_kernel_certificate {m} (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalSuccessorWitnessSentence w x)) := TheoryTransport.sentence (source_naturalSuccessorWitness w x)

theorem native_naturalSuccessorWitness {m} (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalSuccessorWitnessSentence w x)) := ZFReplay.replay (naturalSuccessorWitness_kernel_certificate w x)

def liftedChildExecutionAlignmentIffSentence {m} (w K S H A b C c x X : Fin m) : Source.Sentence := ((Formula.equal A C).imp ((Formula.equal H S).imp (((FormulaTransformExecutionSyntax.executed w K S A b A c x X).iff (FormulaTransformExecutionSyntax.executed w K H A b C c x X))))).close

theorem source_liftedChildExecutionAlignmentIff {m} (w K S H A b C c x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (liftedChildExecutionAlignmentIffSentence w K S H A b C c x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.equal H S) (Context.add (Formula.equal A C) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (Formula.equal A C) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.equal H S) := .hyp (Or.inl rfl)
  exact OriginalBinderReadAtLift.aligned_execution_iff w K S H A b C c x X h0 h1

theorem liftedChildExecutionAlignmentIff_kernel_certificate {m} (w K S H A b C c x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (liftedChildExecutionAlignmentIffSentence w K S H A b C c x X)) := TheoryTransport.sentence (source_liftedChildExecutionAlignmentIff w K S H A b C c x X)

theorem native_liftedChildExecutionAlignmentIff {m} (w K S H A b C c x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (liftedChildExecutionAlignmentIffSentence w K S H A b C c x X)) := ZFReplay.replay (liftedChildExecutionAlignmentIff_kernel_certificate w K S H A b C c x X)

def quantifierChildReadAtLiftIffSentence {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X A C K H D : Fin m) : Source.Sentence := ((omega w).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H).imp (((OriginalTransformRowSyntax.run 3 w mode D (OriginalOperationFrameSyntax.parameter three P S) x X).iff (FormulaTransformHistorySyntax.read w h x K H A b C c X))))))))))).close

theorem source_quantifierChildReadAtLiftIff {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X A C K H D : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierChildReadAtLiftIffSentence three universal w n mode depth P a b c I J R S h x X A C K H D) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H) (Context.add (successor D depth) (Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H) := .hyp (Or.inl rfl)
  exact OriginalBinderReadAtLift.read_at_lift_iff hZ three universal w n mode depth P a b c I J R S h x X A C K H D h0 h1 h2 h3 h4 h5 h6 h7

theorem quantifierChildReadAtLiftIff_kernel_certificate {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierChildReadAtLiftIffSentence three universal w n mode depth P a b c I J R S h x X A C K H D)) := TheoryTransport.sentence (source_quantifierChildReadAtLiftIff three universal w n mode depth P a b c I J R S h x X A C K H D)

theorem native_quantifierChildReadAtLiftIff {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierChildReadAtLiftIffSentence three universal w n mode depth P a b c I J R S h x X A C K H D)) := ZFReplay.replay (quantifierChildReadAtLiftIff_kernel_certificate three universal w n mode depth P a b c I J R S h x X A C K H D)

def quantifierStepAdvancedIffSentence {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X : Fin m) : Source.Sentence := ((omega w).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalBinderStepSyntax.step w mode depth (OriginalOperationFrameSyntax.parameter three P S) x X).iff (FormulaTransformHistorySyntax.advanced w h x R S a b a c X))))))))).close

theorem source_quantifierStepAdvancedIff {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierStepAdvancedIffSentence three universal w n mode depth P a b c I J R S h x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact OriginalBinderAdvance.step_iff_advanced hZ three universal w n mode depth P a b c I J R S h x X h0 h1 h2 h3 h4 h5

theorem quantifierStepAdvancedIff_kernel_certificate {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierStepAdvancedIffSentence three universal w n mode depth P a b c I J R S h x X)) := TheoryTransport.sentence (source_quantifierStepAdvancedIff three universal w n mode depth P a b c I J R S h x X)

theorem native_quantifierStepAdvancedIff {m} (three universal : Bool) (w n mode depth P a b c I J R S h x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierStepAdvancedIffSentence three universal w n mode depth P a b c I J R S h x X)) := ZFReplay.replay (quantifierStepAdvancedIff_kernel_certificate three universal w n mode depth P a b c I J R S h x X)

def quantifierLocalCaseIffSentence {m} (three universal : Bool) (w n mode depth P a b c I J R S h q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalFormulaCaseSyntax.binderCase (SyntaxLogicalSyntax.quantifierTag universal) w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b a c n q)))))))).close

theorem source_quantifierLocalCaseIff {m} (three universal : Bool) (w n mode depth P a b c I J R S h q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierLocalCaseIffSentence three universal w n mode depth P a b c I J R S h q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact OriginalBinderCaseBridge.quantified_iff hZ three universal w n mode depth P a b c I J R S h q h0 h1 h2 h3 h4

theorem quantifierLocalCaseIff_kernel_certificate {m} (three universal : Bool) (w n mode depth P a b c I J R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierLocalCaseIffSentence three universal w n mode depth P a b c I J R S h q)) := TheoryTransport.sentence (source_quantifierLocalCaseIff three universal w n mode depth P a b c I J R S h q)

theorem native_quantifierLocalCaseIff {m} (three universal : Bool) (w n mode depth P a b c I J R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierLocalCaseIffSentence three universal w n mode depth P a b c I J R S h q)) := ZFReplay.replay (quantifierLocalCaseIff_kernel_certificate three universal w n mode depth P a b c I J R S h q)

def quantifierWholeRunDispatchIffSentence {m} (three universal : Bool) (w mode depth parameter n q x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode).imp ((OriginalTermTraceSyntax.metadata w depth parameter).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp (((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (OriginalFormulaCaseSyntax.binderCase (SyntaxLogicalSyntax.quantifierTag universal) w mode depth parameter n q))))))).close

theorem source_quantifierWholeRunDispatchIff {m} (three universal : Bool) (w mode depth parameter n q x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierWholeRunDispatchIffSentence three universal w mode depth parameter n q x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (OriginalTermTraceSyntax.metadata w depth parameter) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth parameter) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inl rfl)
  exact OriginalBinderRunDispatch.run_iff_quantified hZ three universal w mode depth parameter n q x h0 h1 (.conjL h2) (.conjR h2) h3

theorem quantifierWholeRunDispatchIff_kernel_certificate {m} (three universal : Bool) (w mode depth parameter n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierWholeRunDispatchIffSentence three universal w mode depth parameter n q x)) := TheoryTransport.sentence (source_quantifierWholeRunDispatchIff three universal w mode depth parameter n q x)

theorem native_quantifierWholeRunDispatchIff {m} (three universal : Bool) (w mode depth parameter n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierWholeRunDispatchIffSentence three universal w mode depth parameter n q x)) := ZFReplay.replay (quantifierWholeRunDispatchIff_kernel_certificate three universal w mode depth parameter n q x)

def quantifierWholeRunFromUniformInductionIffSentence {m} (three universal : Bool) (w n mode depth P a b c I J R S h x q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b a c n q))))))))).close

theorem source_quantifierWholeRunFromUniformInductionIff {m} (three universal : Bool) (w n mode depth P a b c I J R S h x q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierWholeRunFromUniformInductionIffSentence three universal w n mode depth P a b c I J R S h x q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact OriginalBinderProgram.quantified_iff hZ three universal w n mode depth P a b c I J R S h x q h0 h1 h2 h3 h4 h5

theorem quantifierWholeRunFromUniformInductionIff_kernel_certificate {m} (three universal : Bool) (w n mode depth P a b c I J R S h x q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierWholeRunFromUniformInductionIffSentence three universal w n mode depth P a b c I J R S h x q)) := TheoryTransport.sentence (source_quantifierWholeRunFromUniformInductionIff three universal w n mode depth P a b c I J R S h x q)

theorem native_quantifierWholeRunFromUniformInductionIff {m} (three universal : Bool) (w n mode depth P a b c I J R S h x q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierWholeRunFromUniformInductionIffSentence three universal w n mode depth P a b c I J R S h x q)) := ZFReplay.replay (quantifierWholeRunFromUniformInductionIff_kernel_certificate three universal w n mode depth P a b c I J R S h x q)

end PPAC.Migration.Internal.ObjectOriginalBinderProgram
