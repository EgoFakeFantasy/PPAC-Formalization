import PPAC.Migration.Internal.OriginalUniformInductionRules

/-! 实际可提升模式环境、全参数对象归纳实例与真实量词环境闭包的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectUniformOperationFrames
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def freeConversionFromActualConvertedSentence {m} (w J S b a c : Fin m) : Source.Sentence := ((omega w).imp ((IndexTermImageCodeSyntax.converted false w J S b a c).imp ((SyntaxFreeSubstSyntax.codeConversion w b c S J)))).close

theorem source_freeConversionFromActualConverted {m} (w J S b a c : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeConversionFromActualConvertedSentence w J S b a c) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.converted false w J S b a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a c) := .hyp (Or.inl rfl)
  exact OriginalFreeImageConversion.from_converted hZ w J S b a c h0 h1

theorem freeConversionFromActualConverted_kernel_certificate {m} (w J S b a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeConversionFromActualConvertedSentence w J S b a c)) := TheoryTransport.sentence (source_freeConversionFromActualConverted w J S b a c)

theorem native_freeConversionFromActualConverted {m} (w J S b a c : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeConversionFromActualConvertedSentence w J S b a c)) := ZFReplay.replay (freeConversionFromActualConverted_kernel_certificate w J S b a c)

def frameEnvironmentSentence {m} (three : Bool) (w mode depth P a b c I J R S : Fin m) : Source.Sentence := ((omega w).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((IndexTermImageCodeSyntax.environment w I J R S a b a c)))).close

theorem source_frameEnvironment {m} (three : Bool) (w mode depth P a b c I J R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (frameEnvironmentSentence three w mode depth P a b c I J R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inl rfl)
  exact OriginalOperationFrameRules.environment hZ three w mode depth P a b c I J R S h0 h1

theorem frameEnvironment_kernel_certificate {m} (three : Bool) (w mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (frameEnvironmentSentence three w mode depth P a b c I J R S)) := TheoryTransport.sentence (source_frameEnvironment three w mode depth P a b c I J R S)

theorem native_frameEnvironment {m} (three : Bool) (w mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (frameEnvironmentSentence three w mode depth P a b c I J R S)) := ZFReplay.replay (frameEnvironment_kernel_certificate three w mode depth P a b c I J R S)

def weakenFrameFromExistingEnvironmentSentence {m} (w mode depth P a b c I J R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 0 mode).imp ((OriginalTermTraceSyntax.metadata w depth P).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeShiftSyntax.shiftCode w b c J).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((IndexTermImageCodeSyntax.converted false w J S b a c).imp ((OriginalOperationFrameSyntax.frame false w mode depth P a b c I J R S))))))))).close

theorem source_weakenFrameFromExistingEnvironment {m} (w mode depth P a b c I J R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakenFrameFromExistingEnvironmentSentence w mode depth P a b c I J R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.converted false w J S b a c) (Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxFreeShiftSyntax.shiftCode w b c J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth P) (Context.add (SyntaxNumeralSyntax.numeral 0 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 0 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTermTraceSyntax.metadata w depth P) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxFreeShiftSyntax.shiftCode w b c J) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (IndexTermImageCodeSyntax.converted false w J S b a c) := .hyp (Or.inl rfl)
  exact OriginalOperationFrameRules.from_weaken hZ w mode depth P a b c I J R S h0 h1 h2 h3 h4 h5 h6

theorem weakenFrameFromExistingEnvironment_kernel_certificate {m} (w mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakenFrameFromExistingEnvironmentSentence w mode depth P a b c I J R S)) := TheoryTransport.sentence (source_weakenFrameFromExistingEnvironment w mode depth P a b c I J R S)

theorem native_weakenFrameFromExistingEnvironment {m} (w mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakenFrameFromExistingEnvironmentSentence w mode depth P a b c I J R S)) := ZFReplay.replay (weakenFrameFromExistingEnvironment_kernel_certificate w mode depth P a b c I J R S)

def replaceFrameFromFreeConversionSentence {m} (w mode depth P a b c I J R S : Fin m) : Source.Sentence := ((SyntaxNumeralSyntax.numeral 3 mode).imp ((OriginalTermTraceSyntax.metadata w depth S).imp ((SyntaxIdentityMapSyntax.identityCode w a I).imp ((SyntaxFreeSubstSyntax.codeConversion w b c S J).imp ((IndexTermImageCodeSyntax.converted true w I R a a c).imp ((OriginalOperationFrameSyntax.frame true w mode depth P a b c I J R S))))))).close

theorem source_replaceFrameFromFreeConversion {m} (w mode depth P a b c I J R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (replaceFrameFromFreeConversionSentence w mode depth P a b c I J R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.converted true w I R a a c) (Context.add (SyntaxFreeSubstSyntax.codeConversion w b c S J) (Context.add (SyntaxIdentityMapSyntax.identityCode w a I) (Context.add (OriginalTermTraceSyntax.metadata w depth S) (Context.add (SyntaxNumeralSyntax.numeral 3 mode) (Source.SetLanguage.ZF.at m)))))
  have h0 : Derives Δ (SyntaxNumeralSyntax.numeral 3 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (OriginalTermTraceSyntax.metadata w depth S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w a I) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w b c S J) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (IndexTermImageCodeSyntax.converted true w I R a a c) := .hyp (Or.inl rfl)
  exact OriginalOperationFrameRules.from_replace w mode depth P a b c I J R S h0 h1 h2 h3 h4

theorem replaceFrameFromFreeConversion_kernel_certificate {m} (w mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (replaceFrameFromFreeConversionSentence w mode depth P a b c I J R S)) := TheoryTransport.sentence (source_replaceFrameFromFreeConversion w mode depth P a b c I J R S)

theorem native_replaceFrameFromFreeConversion {m} (w mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (replaceFrameFromFreeConversionSentence w mode depth P a b c I J R S)) := ZFReplay.replay (replaceFrameFromFreeConversion_kernel_certificate w mode depth P a b c I J R S)

def frameAtomicWholeProgramIffSentence {m} (three : Bool) (w mode depth P a b c I J R S h n q : Fin m) : Source.Sentence := ((omega w).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((SyntaxAtomSyntax.atomic w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b a c h n q)))))).close

theorem source_frameAtomicWholeProgramIff {m} (three : Bool) (w mode depth P a b c I J R S h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (frameAtomicWholeProgramIffSentence three w mode depth P a b c I J R S h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact OriginalOperationFrameRules.atomic_program_iff hZ three w mode depth P a b c I J R S h n q h0 h1 h2

theorem frameAtomicWholeProgramIff_kernel_certificate {m} (three : Bool) (w mode depth P a b c I J R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (frameAtomicWholeProgramIffSentence three w mode depth P a b c I J R S h n q)) := TheoryTransport.sentence (source_frameAtomicWholeProgramIff three w mode depth P a b c I J R S h n q)

theorem native_frameAtomicWholeProgramIff {m} (three : Bool) (w mode depth P a b c I J R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (frameAtomicWholeProgramIffSentence three w mode depth P a b c I J R S h n q)) := ZFReplay.replay (frameAtomicWholeProgramIff_kernel_certificate three w mode depth P a b c I J R S h n q)

def binderEnvironmentAtSentence {m} (three : Bool) (w mode depth P a b c I J R S A C M K H D : Fin m) : Source.Sentence := ((omega w).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((successor D depth).imp ((SyntaxMapLiftSyntax.codedLift w a a I A C M).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H).imp (((Formula.equal A C).conj ((Formula.equal H S).conj (OriginalOperationFrameSyntax.frame three w mode D P A b c M J K S))))))))).close

theorem source_binderEnvironmentAt {m} (three : Bool) (w mode depth P a b c I J R S A C M K H D : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderEnvironmentAtSentence three w mode depth P a b c I J R S A C M K H D) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H) (Context.add (SyntaxMapLiftSyntax.codedLift w a a I A C M) (Context.add (successor D depth) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a a I A C M) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H) := .hyp (Or.inl rfl)
  exact OriginalOperationFrameRules.binder_at hZ three w mode depth P a b c I J R S A C M K H D h0 h1 h2 h3 h4

theorem binderEnvironmentAt_kernel_certificate {m} (three : Bool) (w mode depth P a b c I J R S A C M K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderEnvironmentAtSentence three w mode depth P a b c I J R S A C M K H D)) := TheoryTransport.sentence (source_binderEnvironmentAt three w mode depth P a b c I J R S A C M K H D)

theorem native_binderEnvironmentAt {m} (three : Bool) (w mode depth P a b c I J R S A C M K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderEnvironmentAtSentence three w mode depth P a b c I J R S A C M K H D)) := ZFReplay.replay (binderEnvironmentAt_kernel_certificate three w mode depth P a b c I J R S A C M K H D)

def binderEnvironmentExistsSentence {m} (three : Bool) (w mode depth P a b c I J R S A C K H D : Fin m) : Source.Sentence := ((omega w).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H).imp ((OriginalOperationFrameSyntax.liftedFrame three w mode depth P a b c I J R S A C K H D)))))).close

theorem source_binderEnvironmentExists {m} (three : Bool) (w mode depth P a b c I J R S A C K H D : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderEnvironmentExistsSentence three w mode depth P a b c I J R S A C K H D) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H) (Context.add (successor D depth) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H) := .hyp (Or.inl rfl)
  exact OriginalOperationFrameRules.binder_step hZ three w mode depth P a b c I J R S A C K H D h0 h1 h2 h3

theorem binderEnvironmentExists_kernel_certificate {m} (three : Bool) (w mode depth P a b c I J R S A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderEnvironmentExistsSentence three w mode depth P a b c I J R S A C K H D)) := TheoryTransport.sentence (source_binderEnvironmentExists three w mode depth P a b c I J R S A C K H D)

theorem native_binderEnvironmentExists {m} (three : Bool) (w mode depth P a b c I J R S A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderEnvironmentExistsSentence three w mode depth P a b c I J R S A C K H D)) := ZFReplay.replay (binderEnvironmentExists_kernel_certificate three w mode depth P a b c I J R S A C K H D)

def uniformCorrectAtSentence {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : Source.Sentence := ((OriginalUniformInductionSyntax.correct three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp (((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff (FormulaTransformExecutionSyntax.executed w R S a b a c n q)))))).close

theorem source_uniformCorrectAt {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniformCorrectAtSentence three w n mode depth P a b c I J R S q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.correct three w n) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (OriginalUniformInductionSyntax.correct three w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inl rfl)
  exact OriginalUniformInductionSyntax.correct_at three w n mode depth P a b c I J R S q h0 h1 h2

theorem uniformCorrectAt_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniformCorrectAtSentence three w n mode depth P a b c I J R S q)) := TheoryTransport.sentence (source_uniformCorrectAt three w n mode depth P a b c I J R S q)

theorem native_uniformCorrectAt {m} (three : Bool) (w n mode depth P a b c I J R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniformCorrectAtSentence three w n mode depth P a b c I J R S q)) := ZFReplay.replay (uniformCorrectAt_kernel_certificate three w n mode depth P a b c I J R S q)

def uniformPrefixAtSentence {m} (three : Bool) (w n x : Fin m) : Source.Sentence := ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((Formula.mem x n).imp ((OriginalUniformInductionSyntax.correct three w x)))).close

theorem source_uniformPrefixAt {m} (three : Bool) (w n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniformPrefixAtSentence three w n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem x n) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem x n) := .hyp (Or.inl rfl)
  exact OriginalUniformInductionSyntax.allFramesIH_at three w n x h0 h1

theorem uniformPrefixAt_kernel_certificate {m} (three : Bool) (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniformPrefixAtSentence three w n x)) := TheoryTransport.sentence (source_uniformPrefixAt three w n x)

theorem native_uniformPrefixAt {m} (three : Bool) (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniformPrefixAtSentence three w n x)) := ZFReplay.replay (uniformPrefixAt_kernel_certificate three w n x)

def uniformPrefixAtFrameSentence {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : Source.Sentence := ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((OriginalFormulaInductionSyntax.prefixIH w mode depth (OriginalOperationFrameSyntax.parameter three P S) R S a b a c n)))).close

theorem source_uniformPrefixAtFrame {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniformPrefixAtFrameSentence three w n mode depth P a b c I J R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inl rfl)
  exact OriginalUniformInductionRules.prefix_at_frame three w n mode depth P a b c I J R S h0 h1

theorem uniformPrefixAtFrame_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniformPrefixAtFrameSentence three w n mode depth P a b c I J R S)) := TheoryTransport.sentence (source_uniformPrefixAtFrame three w n mode depth P a b c I J R S)

theorem native_uniformPrefixAtFrame {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniformPrefixAtFrameSentence three w n mode depth P a b c I J R S)) := ZFReplay.replay (uniformPrefixAtFrame_kernel_certificate three w n mode depth P a b c I J R S)

def actualHistoryAgreementAtUniformFrameSentence {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : Source.Sentence := ((omega w).imp ((OrdinalSyntax.ordinal n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth (OriginalOperationFrameSyntax.parameter three P S) h R S a b a c n))))))).close

theorem source_actualHistoryAgreementAtUniformFrame {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualHistoryAgreementAtUniformFrameSentence three w n mode depth P a b c I J R S h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inl rfl)
  exact OriginalUniformInductionRules.agreement_at_frame hZ three w n mode depth P a b c I J R S h h0 h1 h2 h3 h4

theorem actualHistoryAgreementAtUniformFrame_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualHistoryAgreementAtUniformFrameSentence three w n mode depth P a b c I J R S h)) := TheoryTransport.sentence (source_actualHistoryAgreementAtUniformFrame three w n mode depth P a b c I J R S h)

theorem native_actualHistoryAgreementAtUniformFrame {m} (three : Bool) (w n mode depth P a b c I J R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualHistoryAgreementAtUniformFrameSentence three w n mode depth P a b c I J R S h)) := ZFReplay.replay (actualHistoryAgreementAtUniformFrame_kernel_certificate three w n mode depth P a b c I J R S h)

def actualHistoryExistsAtUniformFrameSentence {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((OriginalFormulaInductionSyntax.agreedHistory w mode depth (OriginalOperationFrameSyntax.parameter three P S) R S a b a c n)))))).close

theorem source_actualHistoryExistsAtUniformFrame {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualHistoryExistsAtUniformFrameSentence three w n mode depth P a b c I J R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalUniformInductionSyntax.allFramesIH three w n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) := .hyp (Or.inl rfl)
  exact OriginalUniformInductionRules.agreed_history_at_frame hZ three w n mode depth P a b c I J R S h0 h1 h2 h3

theorem actualHistoryExistsAtUniformFrame_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualHistoryExistsAtUniformFrameSentence three w n mode depth P a b c I J R S)) := TheoryTransport.sentence (source_actualHistoryExistsAtUniformFrame three w n mode depth P a b c I J R S)

theorem native_actualHistoryExistsAtUniformFrame {m} (three : Bool) (w n mode depth P a b c I J R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualHistoryExistsAtUniformFrameSentence three w n mode depth P a b c I J R S)) := ZFReplay.replay (actualHistoryExistsAtUniformFrame_kernel_certificate three w n mode depth P a b c I J R S)

def binderPrefixFromUniformInductionSentence {m} (three : Bool) (w n mode depth P a b c I J R S A C K H D : Fin m) : Source.Sentence := ((omega w).imp ((OriginalUniformInductionSyntax.allFramesIH three w n).imp ((OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H).imp (((Formula.equal A C).conj ((Formula.equal H S).conj (OriginalFormulaInductionSyntax.prefixIH w mode D (OriginalOperationFrameSyntax.parameter three P S) K S A b A c n))))))))).close

theorem source_binderPrefixFromUniformInduction {m} (three : Bool) (w n mode depth P a b c I J R S A C K H D : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binderPrefixFromUniformInductionSentence three w n mode depth P a b c I J R S A C K H D) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H) (Context.add (successor D depth) (Context.add (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S) (Context.add (OriginalUniformInductionSyntax.allFramesIH three w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h3 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H) := .hyp (Or.inl rfl)
  exact OriginalUniformInductionRules.binder_prefix hZ three w n mode depth P a b c I J R S A C K H D h0 h1 h2 h3 h4

theorem binderPrefixFromUniformInduction_kernel_certificate {m} (three : Bool) (w n mode depth P a b c I J R S A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binderPrefixFromUniformInductionSentence three w n mode depth P a b c I J R S A C K H D)) := TheoryTransport.sentence (source_binderPrefixFromUniformInduction three w n mode depth P a b c I J R S A C K H D)

theorem native_binderPrefixFromUniformInduction {m} (three : Bool) (w n mode depth P a b c I J R S A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binderPrefixFromUniformInductionSentence three w n mode depth P a b c I J R S A C K H D)) := ZFReplay.replay (binderPrefixFromUniformInduction_kernel_certificate three w n mode depth P a b c I J R S A C K H D)

end PPAC.Migration.Internal.ObjectUniformOperationFrames
