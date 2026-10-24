import PPAC.Migration.Internal.InstantiateTopFormulaOperation

/-! 原mode2全内部项纤维／列表／完整公式与实际InstantiateTop操作的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectInstantiateFormula
open Source SourceAlgebra SourceLogic OmegaSyntax InstantiateOperationFrameSyntax InstantiateUniformInductionSyntax

def modeTwoAllTypedTermAgreementSentence {m} (w mode depth P a b c e R S n : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((SyntaxTermSyntax.term w a b n).imp ((OriginalNumericTermValueSyntax.agreement w mode depth P R S n))))).close

theorem source_modeTwoAllTypedTermAgreement {m} (w mode depth P a b c e R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoAllTypedTermAgreementSentence w mode depth P a b c e R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact InstantiateFrameTermFiber.agreement hZ w mode depth P a b c e R S n h0 h1 h2

theorem modeTwoAllTypedTermAgreement_kernel_certificate {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoAllTypedTermAgreementSentence w mode depth P a b c e R S n)) := TheoryTransport.sentence (source_modeTwoAllTypedTermAgreement w mode depth P a b c e R S n)

theorem native_modeTwoAllTypedTermAgreement {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoAllTypedTermAgreementSentence w mode depth P a b c e R S n)) := ZFReplay.replay (modeTwoAllTypedTermAgreement_kernel_certificate w mode depth P a b c e R S n)

def modeTwoAllTypedTermUniqueFiberSentence {m} (w mode depth P a b c e R S n : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((SyntaxTermSyntax.term w a b n).imp ((OriginalNumericTermValueSyntax.fiber w mode depth P c e n))))).close

theorem source_modeTwoAllTypedTermUniqueFiber {m} (w mode depth P a b c e R S n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoAllTypedTermUniqueFiberSentence w mode depth P a b c e R S n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.term w a b n) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermSyntax.term w a b n) := .hyp (Or.inl rfl)
  exact InstantiateFrameTermFiber.fiber hZ w mode depth P a b c e R S n h0 h1 h2

theorem modeTwoAllTypedTermUniqueFiber_kernel_certificate {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoAllTypedTermUniqueFiberSentence w mode depth P a b c e R S n)) := TheoryTransport.sentence (source_modeTwoAllTypedTermUniqueFiber w mode depth P a b c e R S n)

theorem native_modeTwoAllTypedTermUniqueFiber {m} (w mode depth P a b c e R S n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoAllTypedTermUniqueFiberSentence w mode depth P a b c e R S n)) := ZFReplay.replay (modeTwoAllTypedTermUniqueFiber_kernel_certificate w mode depth P a b c e R S n)

def modeTwoTermPromiseDerivedSentence {m} (w mode depth P a b c e R S : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((OriginalNumericTermValueSyntax.promise w mode depth P a b c e)))).close

theorem source_modeTwoTermPromiseDerived {m} (w mode depth P a b c e R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoTermPromiseDerivedSentence w mode depth P a b c e R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact InstantiateFrameTermFiber.promise hZ w mode depth P a b c e R S h0 h1

theorem modeTwoTermPromiseDerived_kernel_certificate {m} (w mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoTermPromiseDerivedSentence w mode depth P a b c e R S)) := TheoryTransport.sentence (source_modeTwoTermPromiseDerived w mode depth P a b c e R S)

theorem native_modeTwoTermPromiseDerived {m} (w mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoTermPromiseDerivedSentence w mode depth P a b c e R S)) := ZFReplay.replay (modeTwoTermPromiseDerived_kernel_certificate w mode depth P a b c e R S)

def modeTwoArgumentFieldsProgramIffSentence {m} (w mode depth P a b c e R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalArgumentFieldSyntax.fields w mode depth P k n q).iff (ArgumentProgramFieldSyntax.fields w R S k n q)))))).close

theorem source_modeTwoArgumentFieldsProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoArgumentFieldsProgramIffSentence w mode depth P a b c e R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact InstantiateFrameArguments.fields_iff hZ w mode depth P a b c e R S n q k h0 h1 h2

theorem modeTwoArgumentFieldsProgramIff_kernel_certificate {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoArgumentFieldsProgramIffSentence w mode depth P a b c e R S n q k)) := TheoryTransport.sentence (source_modeTwoArgumentFieldsProgramIff w mode depth P a b c e R S n q k)

theorem native_modeTwoArgumentFieldsProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoArgumentFieldsProgramIffSentence w mode depth P a b c e R S n q k)) := ZFReplay.replay (modeTwoArgumentFieldsProgramIff_kernel_certificate w mode depth P a b c e R S n q k)

def modeTwoWholeArgumentProgramIffSentence {m} (w mode depth P a b c e R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (((OriginalTransformRowSyntax.run 2 w mode depth P n q).iff (ArgumentProgramFieldSyntax.mapped w R S k c e n q)))))).close

theorem source_modeTwoWholeArgumentProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoWholeArgumentProgramIffSentence w mode depth P a b c e R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedImageCodeSyntax.termList w k a b n) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxMixedImageCodeSyntax.termList w k a b n) := .hyp (Or.inl rfl)
  exact InstantiateFrameArguments.run_iff hZ w mode depth P a b c e R S n q k h0 h1 h2

theorem modeTwoWholeArgumentProgramIff_kernel_certificate {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoWholeArgumentProgramIffSentence w mode depth P a b c e R S n q k)) := TheoryTransport.sentence (source_modeTwoWholeArgumentProgramIff w mode depth P a b c e R S n q k)

theorem native_modeTwoWholeArgumentProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoWholeArgumentProgramIffSentence w mode depth P a b c e R S n q k)) := ZFReplay.replay (modeTwoWholeArgumentProgramIff_kernel_certificate w mode depth P a b c e R S n q k)

def modeTwoGuardedArgumentProgramIffSentence {m} (w mode depth P a b c e R S n q k : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((((SyntaxMixedImageCodeSyntax.termList w k a b n).conj (OriginalTransformRowSyntax.run 2 w mode depth P n q)).iff
      ((SyntaxMixedImageCodeSyntax.termList w k a b n).conj (ArgumentProgramFieldSyntax.mapped w R S k c e n q)))))).close

theorem source_modeTwoGuardedArgumentProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoGuardedArgumentProgramIffSentence w mode depth P a b c e R S n q k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact InstantiateFrameArguments.guarded_iff hZ w mode depth P a b c e R S n q k h0 h1

theorem modeTwoGuardedArgumentProgramIff_kernel_certificate {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoGuardedArgumentProgramIffSentence w mode depth P a b c e R S n q k)) := TheoryTransport.sentence (source_modeTwoGuardedArgumentProgramIff w mode depth P a b c e R S n q k)

theorem native_modeTwoGuardedArgumentProgramIff {m} (w mode depth P a b c e R S n q k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoGuardedArgumentProgramIffSentence w mode depth P a b c e R S n q k)) := ZFReplay.replay (modeTwoGuardedArgumentProgramIff_kernel_certificate w mode depth P a b c e R S n q k)

def modeTwoFourAtomicRunIffSentence {m} (w mode depth P a b c e R S n q : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((SyntaxAtomSyntax.atomic w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaAtomicProgramSyntax.run w R S a b c e n q)))))).close

theorem source_modeTwoFourAtomicRunIff {m} (w mode depth P a b c e R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoFourAtomicRunIffSentence w mode depth P a b c e R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact InstantiateFrameAtomic.run_iff hZ w mode depth P a b c e R S n q h0 h1 h2

theorem modeTwoFourAtomicRunIff_kernel_certificate {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoFourAtomicRunIffSentence w mode depth P a b c e R S n q)) := TheoryTransport.sentence (source_modeTwoFourAtomicRunIff w mode depth P a b c e R S n q)

theorem native_modeTwoFourAtomicRunIff {m} (w mode depth P a b c e R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoFourAtomicRunIffSentence w mode depth P a b c e R S n q)) := ZFReplay.replay (modeTwoFourAtomicRunIff_kernel_certificate w mode depth P a b c e R S n q)

def modeTwoFourAtomicProgramIffSentence {m} (w mode depth P a b c e R S h n q : Fin m) : Source.Sentence := ((omega w).imp ((frame w mode depth P a b c e R S).imp ((SyntaxAtomSyntax.atomic w a b n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaAtomicProgramSyntax.program w R S a b c e h n q)))))).close

theorem source_modeTwoFourAtomicProgramIff {m} (w mode depth P a b c e R S h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoFourAtomicProgramIffSentence w mode depth P a b c e R S h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact InstantiateFrameAtomic.program_iff hZ w mode depth P a b c e R S h n q h0 h1 h2

theorem modeTwoFourAtomicProgramIff_kernel_certificate {m} (w mode depth P a b c e R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoFourAtomicProgramIffSentence w mode depth P a b c e R S h n q)) := TheoryTransport.sentence (source_modeTwoFourAtomicProgramIff w mode depth P a b c e R S h n q)

theorem native_modeTwoFourAtomicProgramIff {m} (w mode depth P a b c e R S h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoFourAtomicProgramIffSentence w mode depth P a b c e R S h n q)) := ZFReplay.replay (modeTwoFourAtomicProgramIff_kernel_certificate w mode depth P a b c e R S h n q)

def modeTwoActualBinderPrefixFromInductionSentence {m} (w n mode depth P a b c e R S A C K H D : Fin m) : Source.Sentence := ((omega w).imp ((InstantiateUniformInductionSyntax.allFramesIH w n).imp ((frame w mode depth P a b c e R S).imp ((successor D depth).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H).imp ((OriginalFormulaInductionSyntax.prefixIH w mode D P K H A b C e n))))))).close

theorem source_modeTwoActualBinderPrefixFromInduction {m} (w n mode depth P a b c e R S A C K H D : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualBinderPrefixFromInductionSentence w n mode depth P a b c e R S A C K H D) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) (Context.add (successor D depth) (Context.add (frame w mode depth P a b c e R S) (Context.add (InstantiateUniformInductionSyntax.allFramesIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (InstantiateUniformInductionSyntax.allFramesIH w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor D depth) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H) := .hyp (Or.inl rfl)
  exact InstantiateUniformInductionRules.binder_prefix hZ w n mode depth P a b c e R S A C K H D h0 h1 h2 h3 h4

theorem modeTwoActualBinderPrefixFromInduction_kernel_certificate {m} (w n mode depth P a b c e R S A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualBinderPrefixFromInductionSentence w n mode depth P a b c e R S A C K H D)) := TheoryTransport.sentence (source_modeTwoActualBinderPrefixFromInduction w n mode depth P a b c e R S A C K H D)

theorem native_modeTwoActualBinderPrefixFromInduction {m} (w n mode depth P a b c e R S A C K H D : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualBinderPrefixFromInductionSentence w n mode depth P a b c e R S A C K H D)) := ZFReplay.replay (modeTwoActualBinderPrefixFromInduction_kernel_certificate w n mode depth P a b c e R S A C K H D)

def modeTwoAllElevenProgramFromInductionIffSentence {m} (w n mode depth P a b c e R S h q : Fin m) : Source.Sentence := ((omega w).imp ((InstantiateUniformInductionSyntax.allFramesIH w n).imp ((InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q)))))))).close

theorem source_modeTwoAllElevenProgramFromInductionIff {m} (w n mode depth P a b c e R S h q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoAllElevenProgramFromInductionIffSentence w n mode depth P a b c e R S h q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (InstantiateUniformInductionSyntax.allFramesIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (InstantiateUniformInductionSyntax.allFramesIH w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact InstantiateFullFormulaProgram.program_iff hZ w n mode depth P a b c e R S h q h0 h1 h2 h3 h4

theorem modeTwoAllElevenProgramFromInductionIff_kernel_certificate {m} (w n mode depth P a b c e R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoAllElevenProgramFromInductionIffSentence w n mode depth P a b c e R S h q)) := TheoryTransport.sentence (source_modeTwoAllElevenProgramFromInductionIff w n mode depth P a b c e R S h q)

theorem native_modeTwoAllElevenProgramFromInductionIff {m} (w n mode depth P a b c e R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoAllElevenProgramFromInductionIffSentence w n mode depth P a b c e R S h q)) := ZFReplay.replay (modeTwoAllElevenProgramFromInductionIff_kernel_certificate w n mode depth P a b c e R S h q)

def modeTwoUniformCorrectnessProgressiveSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((SetInductionSyntax.progressive (InstantiateFormulaCorrectnessInduction.matrix ) (fun _ : Fin 1 => w)))).close

theorem source_modeTwoUniformCorrectnessProgressive {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoUniformCorrectnessProgressiveSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact InstantiateFormulaCorrectnessInduction.progressive hZ w h0

theorem modeTwoUniformCorrectnessProgressive_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoUniformCorrectnessProgressiveSentence w)) := TheoryTransport.sentence (source_modeTwoUniformCorrectnessProgressive w)

theorem native_modeTwoUniformCorrectnessProgressive {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoUniformCorrectnessProgressiveSentence w)) := ZFReplay.replay (modeTwoUniformCorrectnessProgressive_kernel_certificate w)

def modeTwoAllInternalFormulaCorrectSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((Formula.all (correct w.castSucc (Fin.last m))))).close

theorem source_modeTwoAllInternalFormulaCorrect {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoAllInternalFormulaCorrectSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact InstantiateFormulaCorrectnessInduction.all_correct hZ w h0

theorem modeTwoAllInternalFormulaCorrect_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoAllInternalFormulaCorrectSentence w)) := TheoryTransport.sentence (source_modeTwoAllInternalFormulaCorrect w)

theorem native_modeTwoAllInternalFormulaCorrect {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoAllInternalFormulaCorrectSentence w)) := ZFReplay.replay (modeTwoAllInternalFormulaCorrect_kernel_certificate w)

def modeTwoAllInternalRootsCorrectSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((correct w n))).close

theorem source_modeTwoAllInternalRootsCorrect {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoAllInternalRootsCorrectSentence w n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact InstantiateFormulaCorrectnessInduction.at_root hZ w n h0

theorem modeTwoAllInternalRootsCorrect_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoAllInternalRootsCorrectSentence w n)) := TheoryTransport.sentence (source_modeTwoAllInternalRootsCorrect w n)

theorem native_modeTwoAllInternalRootsCorrect {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoAllInternalRootsCorrectSentence w n)) := ZFReplay.replay (modeTwoAllInternalRootsCorrect_kernel_certificate w n)

def modeTwoAllInternalWholeFormulaExecutionIffSentence {m} (w n mode depth P a b c e R S q : Fin m) : Source.Sentence := ((omega w).imp ((InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
      (FormulaTransformExecutionSyntax.executed w R S a b c e n q)))))).close

theorem source_modeTwoAllInternalWholeFormulaExecutionIff {m} (w n mode depth P a b c e R S q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoAllInternalWholeFormulaExecutionIffSentence w n mode depth P a b c e R S q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inl rfl)
  exact InstantiateFormulaCorrectnessInduction.run_iff_execution hZ w n mode depth P a b c e R S q h0 h1 h2

theorem modeTwoAllInternalWholeFormulaExecutionIff_kernel_certificate {m} (w n mode depth P a b c e R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoAllInternalWholeFormulaExecutionIffSentence w n mode depth P a b c e R S q)) := TheoryTransport.sentence (source_modeTwoAllInternalWholeFormulaExecutionIff w n mode depth P a b c e R S q)

theorem native_modeTwoAllInternalWholeFormulaExecutionIff {m} (w n mode depth P a b c e R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoAllInternalWholeFormulaExecutionIffSentence w n mode depth P a b c e R S q)) := ZFReplay.replay (modeTwoAllInternalWholeFormulaExecutionIff_kernel_certificate w n mode depth P a b c e R S q)

def modeTwoAllInternalWholeFormulaProgramIffSentence {m} (w n mode depth P a b c e R S h q : Fin m) : Source.Sentence := ((omega w).imp ((InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
      (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S a b c e h n q))))))).close

theorem source_modeTwoAllInternalWholeFormulaProgramIff {m} (w n mode depth P a b c e R S h q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoAllInternalWholeFormulaProgramIffSentence w n mode depth P a b c e R S h q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact InstantiateFormulaCorrectnessInduction.run_iff_program hZ w n mode depth P a b c e R S h q h0 h1 h2 h3

theorem modeTwoAllInternalWholeFormulaProgramIff_kernel_certificate {m} (w n mode depth P a b c e R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoAllInternalWholeFormulaProgramIffSentence w n mode depth P a b c e R S h q)) := TheoryTransport.sentence (source_modeTwoAllInternalWholeFormulaProgramIff w n mode depth P a b c e R S h q)

theorem native_modeTwoAllInternalWholeFormulaProgramIff {m} (w n mode depth P a b c e R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoAllInternalWholeFormulaProgramIffSentence w n mode depth P a b c e R S h q)) := ZFReplay.replay (modeTwoAllInternalWholeFormulaProgramIff_kernel_certificate w n mode depth P a b c e R S h q)

def modeTwoActualHistoryAgreementDischargedSentence {m} (w n mode depth P a b c e R S h : Fin m) : Source.Sentence := ((omega w).imp ((OrdinalSyntax.ordinal n).imp ((FormulaTransformRecursionSyntax.graph w h n).imp ((InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((OriginalFormulaHistoryAgreementSyntax.agreement w mode depth P h R S a b c e n)))))).close

theorem source_modeTwoActualHistoryAgreementDischarged {m} (w n mode depth P a b c e R S h : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualHistoryAgreementDischargedSentence w n mode depth P a b c e R S h) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact InstantiateFormulaCorrectnessInduction.actual_history_agreement hZ w n mode depth P a b c e R S h h0 h1 h2 h3

theorem modeTwoActualHistoryAgreementDischarged_kernel_certificate {m} (w n mode depth P a b c e R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualHistoryAgreementDischargedSentence w n mode depth P a b c e R S h)) := TheoryTransport.sentence (source_modeTwoActualHistoryAgreementDischarged w n mode depth P a b c e R S h)

theorem native_modeTwoActualHistoryAgreementDischarged {m} (w n mode depth P a b c e R S h : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualHistoryAgreementDischargedSentence w n mode depth P a b c e R S h)) := ZFReplay.replay (modeTwoActualHistoryAgreementDischarged_kernel_certificate w n mode depth P a b c e R S h)

def modeTwoAgreedActualHistoryExistsDischargedSentence {m} (w n mode depth P a b c e R S : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S).imp ((OriginalFormulaInductionSyntax.agreedHistory w mode depth P R S a b c e n))))).close

theorem source_modeTwoAgreedActualHistoryExistsDischarged {m} (w n mode depth P a b c e R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoAgreedActualHistoryExistsDischargedSentence w n mode depth P a b c e R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) (Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (InstantiateOperationFrameSyntax.frame w mode depth P a b c e R S) := .hyp (Or.inl rfl)
  exact InstantiateFormulaCorrectnessInduction.agreed_history_exists hZ w n mode depth P a b c e R S h0 h1 h2

theorem modeTwoAgreedActualHistoryExistsDischarged_kernel_certificate {m} (w n mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoAgreedActualHistoryExistsDischargedSentence w n mode depth P a b c e R S)) := TheoryTransport.sentence (source_modeTwoAgreedActualHistoryExistsDischarged w n mode depth P a b c e R S)

theorem native_modeTwoAgreedActualHistoryExistsDischarged {m} (w n mode depth P a b c e R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoAgreedActualHistoryExistsDischargedSentence w n mode depth P a b c e R S)) := ZFReplay.replay (modeTwoAgreedActualHistoryExistsDischarged_kernel_certificate w n mode depth P a b c e R S)

def modeTwoActualRootWholeFormulaExecutionIffSentence {m} (w n mode z P b A R S q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp ((FormulaCodeSyntax.formulaCode w n A b).imp (((OriginalTransformRowSyntax.run 3 w mode z P n q).iff
      (FormulaTransformExecutionSyntax.executed w R S A b z b n q)))))))).close

theorem source_modeTwoActualRootWholeFormulaExecutionIff {m} (w n mode z P b A R S q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualRootWholeFormulaExecutionIffSentence w n mode z P b A R S q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n A b) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (FormulaCodeSyntax.formulaCode w n A b) := .hyp (Or.inl rfl)
  exact InstantiateTopFormula.run_iff_execution hZ w n mode z P b A R S q h0 h1 h2 h3 h4

theorem modeTwoActualRootWholeFormulaExecutionIff_kernel_certificate {m} (w n mode z P b A R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualRootWholeFormulaExecutionIffSentence w n mode z P b A R S q)) := TheoryTransport.sentence (source_modeTwoActualRootWholeFormulaExecutionIff w n mode z P b A R S q)

theorem native_modeTwoActualRootWholeFormulaExecutionIff {m} (w n mode z P b A R S q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualRootWholeFormulaExecutionIffSentence w n mode z P b A R S q)) := ZFReplay.replay (modeTwoActualRootWholeFormulaExecutionIff_kernel_certificate w n mode z P b A R S q)

def modeTwoActualRootWholeFormulaProgramIffSentence {m} (w n mode z P b A R S h q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp ((FormulaCodeSyntax.formulaCode w n A b).imp ((FormulaTransformRecursionSyntax.graph w h n).imp (((OriginalTransformRowSyntax.run 3 w mode z P n q).iff
      (FormulaTransformProgramSyntax.run FormulaTransformProgramSyntax.formulaProgram w R S A b z b h n q))))))))).close

theorem source_modeTwoActualRootWholeFormulaProgramIff {m} (w n mode z P b A R S h q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualRootWholeFormulaProgramIffSentence w n mode z P b A R S h q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaTransformRecursionSyntax.graph w h n) (Context.add (FormulaCodeSyntax.formulaCode w n A b) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (FormulaCodeSyntax.formulaCode w n A b) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (FormulaTransformRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact InstantiateTopFormula.run_iff_program hZ w n mode z P b A R S h q h0 h1 h2 h3 h4 h5

theorem modeTwoActualRootWholeFormulaProgramIff_kernel_certificate {m} (w n mode z P b A R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualRootWholeFormulaProgramIffSentence w n mode z P b A R S h q)) := TheoryTransport.sentence (source_modeTwoActualRootWholeFormulaProgramIff w n mode z P b A R S h q)

theorem native_modeTwoActualRootWholeFormulaProgramIff {m} (w n mode z P b A R S h q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualRootWholeFormulaProgramIffSentence w n mode z P b A R S h q)) := ZFReplay.replay (modeTwoActualRootWholeFormulaProgramIff_kernel_certificate w n mode z P b A R S h q)

def modeTwoActualInstantiateTopAtCodesIffSentence {m} (w mode z P b A R S n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((empty z).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S).imp ((FormulaCodeSyntax.formulaCode w n A b).imp (((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (SyntaxTopFormulaSyntax.instantiated w z b A P n q)))))))).close

theorem source_modeTwoActualInstantiateTopAtCodesIff {m} (w mode z P b A R S n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualInstantiateTopAtCodesIffSentence w mode z P b A R S n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n A b) (Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w z b A P R S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (FormulaCodeSyntax.formulaCode w n A b) := .hyp (Or.inl rfl)
  exact InstantiateTopFormulaOperation.at_codes_iff hZ w mode z P b A R S n q h0 h1 h2 h3 h4

theorem modeTwoActualInstantiateTopAtCodesIff_kernel_certificate {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualInstantiateTopAtCodesIffSentence w mode z P b A R S n q)) := TheoryTransport.sentence (source_modeTwoActualInstantiateTopAtCodesIff w mode z P b A R S n q)

theorem native_modeTwoActualInstantiateTopAtCodesIff {m} (w mode z P b A R S n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualInstantiateTopAtCodesIffSentence w mode z P b A R S n q)) := ZFReplay.replay (modeTwoActualInstantiateTopAtCodesIff_kernel_certificate w mode z P b A R S n q)

def modeTwoActualInstantiateTopIffSentence {m} (w mode z P b A n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((empty z).imp ((SyntaxTopEnvironmentSyntax.instantiateInput w z b A P).imp ((FormulaCodeSyntax.formulaCode w n A b).imp (((OriginalTransformRowSyntax.run 3 w mode z P n q).iff (SyntaxTopFormulaSyntax.instantiated w z b A P n q)))))))).close

theorem source_modeTwoActualInstantiateTopIff {m} (w mode z P b A n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualInstantiateTopIffSentence w mode z P b A n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n A b) (Context.add (SyntaxTopEnvironmentSyntax.instantiateInput w z b A P) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateInput w z b A P) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (FormulaCodeSyntax.formulaCode w n A b) := .hyp (Or.inl rfl)
  exact InstantiateTopFormulaOperation.run_iff hZ w mode z P b A n q h0 h1 h2 h3 h4

theorem modeTwoActualInstantiateTopIff_kernel_certificate {m} (w mode z P b A n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualInstantiateTopIffSentence w mode z P b A n q)) := TheoryTransport.sentence (source_modeTwoActualInstantiateTopIff w mode z P b A n q)

theorem native_modeTwoActualInstantiateTopIff {m} (w mode z P b A n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualInstantiateTopIffSentence w mode z P b A n q)) := ZFReplay.replay (modeTwoActualInstantiateTopIff_kernel_certificate w mode z P b A n q)

def modeTwoActualInstantiateTopSourceTypeSentence {m} (w z P b A n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiated w z b A P n q).imp ((FormulaCodeSyntax.formulaCode w n A b)))).close

theorem source_modeTwoActualInstantiateTopSourceType {m} (w z P b A n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualInstantiateTopSourceTypeSentence w z P b A n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiated w z b A P n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w z b A P n q) := .hyp (Or.inl rfl)
  exact InstantiateTopFormulaOperation.source_type hZ w z P b A n q h0 h1

theorem modeTwoActualInstantiateTopSourceType_kernel_certificate {m} (w z P b A n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualInstantiateTopSourceTypeSentence w z P b A n q)) := TheoryTransport.sentence (source_modeTwoActualInstantiateTopSourceType w z P b A n q)

theorem native_modeTwoActualInstantiateTopSourceType {m} (w z P b A n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualInstantiateTopSourceTypeSentence w z P b A n q)) := ZFReplay.replay (modeTwoActualInstantiateTopSourceType_kernel_certificate w z P b A n q)

def modeTwoActualInstantiateTopGuardedIffSentence {m} (w mode z P b A n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral 2 mode).imp ((empty z).imp ((SyntaxTopEnvironmentSyntax.instantiateInput w z b A P).imp ((((FormulaCodeSyntax.formulaCode w n A b).conj (OriginalTransformRowSyntax.run 3 w mode z P n q)).iff (SyntaxTopFormulaSyntax.instantiated w z b A P n q))))))).close

theorem source_modeTwoActualInstantiateTopGuardedIff {m} (w mode z P b A n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (modeTwoActualInstantiateTopGuardedIffSentence w mode z P b A n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopEnvironmentSyntax.instantiateInput w z b A P) (Context.add (empty z) (Context.add (SyntaxNumeralSyntax.numeral 2 mode) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral 2 mode) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxTopEnvironmentSyntax.instantiateInput w z b A P) := .hyp (Or.inl rfl)
  exact InstantiateTopFormulaOperation.guarded_iff hZ w mode z P b A n q h0 h1 h2 h3

theorem modeTwoActualInstantiateTopGuardedIff_kernel_certificate {m} (w mode z P b A n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (modeTwoActualInstantiateTopGuardedIffSentence w mode z P b A n q)) := TheoryTransport.sentence (source_modeTwoActualInstantiateTopGuardedIff w mode z P b A n q)

theorem native_modeTwoActualInstantiateTopGuardedIff {m} (w mode z P b A n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (modeTwoActualInstantiateTopGuardedIffSentence w mode z P b A n q)) := ZFReplay.replay (modeTwoActualInstantiateTopGuardedIff_kernel_certificate w mode z P b A n q)

end PPAC.Migration.Internal.ObjectInstantiateFormula
