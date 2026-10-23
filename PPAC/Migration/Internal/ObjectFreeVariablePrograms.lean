import PPAC.Migration.Internal.WeakenFreeProgramValue

/-! 原自由替换/弱化的全内部独立程序特化、原列表同码和实际唯一输出的原核证书。 -/
namespace PPAC.Migration.Internal.ObjectFreeVariablePrograms
open Source SourceAlgebra SourceLogic OmegaSyntax

def freeImageGraphSentence {m} (w r f a c d : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem c w).imp ((SyntaxFreeSubstSyntax.conversion w f a d r).imp ((SyntaxVariableImageSyntax.mapped false w r a c d f))))).close

theorem source_freeImageGraph {m} (w r f a c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeImageGraphSentence w r f a c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.conversion w f a d r) (Context.add (Formula.mem c w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem c w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.conversion w f a d r) := .hyp (Or.inl rfl)
  exact FreeSubstImageGraph.mapped hZ w r f a c d h0 h1 h2

theorem freeImageGraph_kernel_certificate {m} (w r f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeImageGraphSentence w r f a c d)) := TheoryTransport.sentence (source_freeImageGraph w r f a c d)

theorem native_freeImageGraph {m} (w r f a c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeImageGraphSentence w r f a c d)) := ZFReplay.replay (freeImageGraph_kernel_certificate w r f a c d)

def freeSameListCodeSentence {m} (w a c d L J : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem c w).imp ((SyntaxFreeSubstSyntax.codeConversion w a d L J).imp ((IndexTermImageCodeSyntax.converted false w J L a c d))))).close

theorem source_freeSameListCode {m} (w a c d L J : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeSameListCodeSentence w a c d L J) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.codeConversion w a d L J) (Context.add (Formula.mem c w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem c w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a d L J) := .hyp (Or.inl rfl)
  exact FreeSubstImageCode.same_code hZ w a c d L J h0 h1 h2

theorem freeSameListCode_kernel_certificate {m} (w a c d L J : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeSameListCodeSentence w a c d L J)) := TheoryTransport.sentence (source_freeSameListCode w a c d L J)

theorem native_freeSameListCode {m} (w a c d L J : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeSameListCodeSentence w a c d L J)) := ZFReplay.replay (freeSameListCode_kernel_certificate w a c d L J)

def freeSameListCodeUniqueSentence {m} (w a c d L J T : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem c w).imp ((SyntaxFreeSubstSyntax.codeConversion w a d L J).imp ((IndexTermImageCodeSyntax.converted false w J T a c d).imp ((Formula.equal T L)))))).close

theorem source_freeSameListCodeUnique {m} (w a c d L J T : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeSameListCodeUniqueSentence w a c d L J T) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (IndexTermImageCodeSyntax.converted false w J T a c d) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a d L J) (Context.add (Formula.mem c w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem c w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a d L J) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (IndexTermImageCodeSyntax.converted false w J T a c d) := .hyp (Or.inl rfl)
  exact FreeSubstImageCode.converted_unique_same_code hZ w a c d L J T h0 h1 h2 h3

theorem freeSameListCodeUnique_kernel_certificate {m} (w a c d L J T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeSameListCodeUniqueSentence w a c d L J T)) := TheoryTransport.sentence (source_freeSameListCodeUnique w a c d L J T)

theorem native_freeSameListCodeUnique {m} (w a c d L J T : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeSameListCodeUniqueSentence w a c d L J T)) := ZFReplay.replay (freeSameListCodeUnique_kernel_certificate w a c d L J T)

def boundIdentityImageExistsSentence {m} (w b c I : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem c w).imp ((SyntaxIdentityMapSyntax.identityCode w b I).imp ((IndexTermImageCodeSyntax.existsCode true w I b b c))))).close

theorem source_boundIdentityImageExists {m} (w b c I : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundIdentityImageExistsSentence w b c I) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxIdentityMapSyntax.identityCode w b I) (Context.add (Formula.mem c w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem c w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b I) := .hyp (Or.inl rfl)
  exact FreeSubstImageCode.identity_image_exists hZ w b c I h0 h1 h2

theorem boundIdentityImageExists_kernel_certificate {m} (w b c I : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundIdentityImageExistsSentence w b c I)) := TheoryTransport.sentence (source_boundIdentityImageExists w b c I)

theorem native_boundIdentityImageExists {m} (w b c I : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundIdentityImageExistsSentence w b c I)) := ZFReplay.replay (boundIdentityImageExists_kernel_certificate w b c I)

def freeForwardSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).imp ((FreeSubstProgramSyntax.executed w b a c L n q)))).close

theorem source_freeForward {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeForwardSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q) := .hyp (Or.inl rfl)
  exact FreeSubstProgramCorrectness.forward hZ w b a c L n q h0 h1

theorem freeForward_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeForwardSentence w b a c L n q)) := TheoryTransport.sentence (source_freeForward w b a c L n q)

theorem native_freeForward {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeForwardSentence w b a c L n q)) := ZFReplay.replay (freeForward_kernel_certificate w b a c L n q)

def freeReverseSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((FreeSubstProgramSyntax.executed w b a c L n q).imp ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q)))).close

theorem source_freeReverse {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeReverseSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeSubstProgramSyntax.executed w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeSubstProgramSyntax.executed w b a c L n q) := .hyp (Or.inl rfl)
  exact FreeSubstProgramCorrectness.reverse hZ w b a c L n q h0 h1

theorem freeReverse_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeReverseSentence w b a c L n q)) := TheoryTransport.sentence (source_freeReverse w b a c L n q)

theorem native_freeReverse {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeReverseSentence w b a c L n q)) := ZFReplay.replay (freeReverse_kernel_certificate w b a c L n q)

def freeExecutionIffSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp (((FreeSubstProgramSyntax.executed w b a c L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q)))).close

theorem source_freeExecutionIff {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeExecutionIffSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeSubstProgramCorrectness.executed_iff hZ w b a c L n q h0

theorem freeExecutionIff_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeExecutionIffSentence w b a c L n q)) := TheoryTransport.sentence (source_freeExecutionIff w b a c L n q)

theorem native_freeExecutionIff {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeExecutionIffSentence w b a c L n q)) := ZFReplay.replay (freeExecutionIff_kernel_certificate w b a c L n q)

def freeInputOfExecutionSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((FreeSubstProgramSyntax.executed w b a c L n q).imp ((FreeSubstProgramValueSyntax.inputGuard w b a c L n)))).close

theorem source_freeInputOfExecution {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeInputOfExecutionSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeSubstProgramSyntax.executed w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeSubstProgramSyntax.executed w b a c L n q) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.input_of_execution hZ w b a c L n q h0 h1

theorem freeInputOfExecution_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeInputOfExecutionSentence w b a c L n q)) := TheoryTransport.sentence (source_freeInputOfExecution w b a c L n q)

theorem native_freeInputOfExecution {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeInputOfExecutionSentence w b a c L n q)) := ZFReplay.replay (freeInputOfExecution_kernel_certificate w b a c L n q)

def freeSourceTypeSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((FreeSubstProgramSyntax.executed w b a c L n q).imp ((FormulaCodeSyntax.formulaCode w n b a)))).close

theorem source_freeSourceType {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeSourceTypeSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeSubstProgramSyntax.executed w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeSubstProgramSyntax.executed w b a c L n q) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.source_type hZ w b a c L n q h0 h1

theorem freeSourceType_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeSourceTypeSentence w b a c L n q)) := TheoryTransport.sentence (source_freeSourceType w b a c L n q)

theorem native_freeSourceType {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeSourceTypeSentence w b a c L n q)) := ZFReplay.replay (freeSourceType_kernel_certificate w b a c L n q)

def freeTargetTypeSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((FreeSubstProgramSyntax.executed w b a c L n q).imp ((FormulaCodeSyntax.formulaCode w q b c)))).close

theorem source_freeTargetType {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeTargetTypeSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeSubstProgramSyntax.executed w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeSubstProgramSyntax.executed w b a c L n q) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.target_type hZ w b a c L n q h0 h1

theorem freeTargetType_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeTargetTypeSentence w b a c L n q)) := TheoryTransport.sentence (source_freeTargetType w b a c L n q)

theorem native_freeTargetType {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeTargetTypeSentence w b a c L n q)) := ZFReplay.replay (freeTargetType_kernel_certificate w b a c L n q)

def freeOutputNaturalSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((FreeSubstProgramSyntax.executed w b a c L n q).imp ((Formula.mem q w)))).close

theorem source_freeOutputNatural {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeOutputNaturalSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeSubstProgramSyntax.executed w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeSubstProgramSyntax.executed w b a c L n q) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.output_natural hZ w b a c L n q h0 h1

theorem freeOutputNatural_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeOutputNaturalSentence w b a c L n q)) := TheoryTransport.sentence (source_freeOutputNatural w b a c L n q)

theorem native_freeOutputNatural {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeOutputNaturalSentence w b a c L n q)) := ZFReplay.replay (freeOutputNatural_kernel_certificate w b a c L n q)

def freeUniqueOutputSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((FreeSubstProgramSyntax.executed w b a c L n q).imp ((FreeSubstProgramValueSyntax.uniqueOutput w b a c L n q)))).close

theorem source_freeUniqueOutput {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeUniqueOutputSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeSubstProgramSyntax.executed w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeSubstProgramSyntax.executed w b a c L n q) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.unique_output hZ w b a c L n q h0 h1

theorem freeUniqueOutput_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeUniqueOutputSentence w b a c L n q)) := TheoryTransport.sentence (source_freeUniqueOutput w b a c L n q)

theorem native_freeUniqueOutput {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeUniqueOutputSentence w b a c L n q)) := ZFReplay.replay (freeUniqueOutput_kernel_certificate w b a c L n q)

def freeAtCandidateSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((FreeSubstProgramSyntax.executed w b a c L n q).imp ((FreeSubstProgramValueSyntax.value w b a c L n q)))).close

theorem source_freeAtCandidate {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeAtCandidateSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeSubstProgramSyntax.executed w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeSubstProgramSyntax.executed w b a c L n q) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.at_candidate hZ w b a c L n q h0 h1

theorem freeAtCandidate_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeAtCandidateSentence w b a c L n q)) := TheoryTransport.sentence (source_freeAtCandidate w b a c L n q)

theorem native_freeAtCandidate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeAtCandidateSentence w b a c L n q)) := ZFReplay.replay (freeAtCandidate_kernel_certificate w b a c L n q)

def freeUniqueSentence {m} (w b a c L n q v : Fin m) : Source.Sentence := ((omega w).imp ((FreeSubstProgramSyntax.executed w b a c L n q).imp ((FreeSubstProgramSyntax.executed w b a c L n v).imp ((Formula.equal q v))))).close

theorem source_freeUnique {m} (w b a c L n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeUniqueSentence w b a c L n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeSubstProgramSyntax.executed w b a c L n v) (Context.add (FreeSubstProgramSyntax.executed w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (FreeSubstProgramSyntax.executed w b a c L n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FreeSubstProgramSyntax.executed w b a c L n v) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.unique hZ w b a c L n q v h0 h1 h2

theorem freeUnique_kernel_certificate {m} (w b a c L n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeUniqueSentence w b a c L n q v)) := TheoryTransport.sentence (source_freeUnique w b a c L n q v)

theorem native_freeUnique {m} (w b a c L n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeUniqueSentence w b a c L n q v)) := ZFReplay.replay (freeUnique_kernel_certificate w b a c L n q v)

def freeActualFiberSentence {m} (w b a c L n : Fin m) : Source.Sentence := ((omega w).imp ((FreeSubstProgramValueSyntax.inputGuard w b a c L n).imp ((FreeSubstProgramValueSyntax.fiber w b a c L n)))).close

theorem source_freeActualFiber {m} (w b a c L n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeActualFiberSentence w b a c L n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FreeSubstProgramValueSyntax.inputGuard w b a c L n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FreeSubstProgramValueSyntax.inputGuard w b a c L n) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.actual_fiber hZ w b a c L n h0 h1

theorem freeActualFiber_kernel_certificate {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeActualFiberSentence w b a c L n)) := TheoryTransport.sentence (source_freeActualFiber w b a c L n)

theorem native_freeActualFiber {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeActualFiberSentence w b a c L n)) := ZFReplay.replay (freeActualFiber_kernel_certificate w b a c L n)

def freeFiberIffInputSentence {m} (w b a c L n : Fin m) : Source.Sentence := ((omega w).imp (((FreeSubstProgramValueSyntax.fiber w b a c L n).iff (FreeSubstProgramValueSyntax.inputGuard w b a c L n)))).close

theorem source_freeFiberIffInput {m} (w b a c L n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeFiberIffInputSentence w b a c L n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.fiber_iff_input hZ w b a c L n h0

theorem freeFiberIffInput_kernel_certificate {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeFiberIffInputSentence w b a c L n)) := TheoryTransport.sentence (source_freeFiberIffInput w b a c L n)

theorem native_freeFiberIffInput {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeFiberIffInputSentence w b a c L n)) := ZFReplay.replay (freeFiberIffInput_kernel_certificate w b a c L n)

def freeRejectEnvironmentSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxFreeSubstSyntax.termList w a c L).neg).imp (((FreeSubstProgramSyntax.executed w b a c L n q).neg)))).close

theorem source_freeRejectEnvironment {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeRejectEnvironmentSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxFreeSubstSyntax.termList w a c L).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((SyntaxFreeSubstSyntax.termList w a c L).neg) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.reject_environment hZ w b a c L n q h0 h1

theorem freeRejectEnvironment_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeRejectEnvironmentSentence w b a c L n q)) := TheoryTransport.sentence (source_freeRejectEnvironment w b a c L n q)

theorem native_freeRejectEnvironment {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeRejectEnvironmentSentence w b a c L n q)) := ZFReplay.replay (freeRejectEnvironment_kernel_certificate w b a c L n q)

def freeRejectSourceSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaCodeSyntax.formulaCode w n b a).neg).imp (((FreeSubstProgramSyntax.executed w b a c L n q).neg)))).close

theorem source_freeRejectSource {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeRejectSourceSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FormulaCodeSyntax.formulaCode w n b a).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FormulaCodeSyntax.formulaCode w n b a).neg) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.reject_source hZ w b a c L n q h0 h1

theorem freeRejectSource_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeRejectSourceSentence w b a c L n q)) := TheoryTransport.sentence (source_freeRejectSource w b a c L n q)

theorem native_freeRejectSource {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeRejectSourceSentence w b a c L n q)) := ZFReplay.replay (freeRejectSource_kernel_certificate w b a c L n q)

def freeRejectInputSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp (((FreeSubstProgramValueSyntax.inputGuard w b a c L n).neg).imp (((FreeSubstProgramSyntax.executed w b a c L n q).neg)))).close

theorem source_freeRejectInput {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeRejectInputSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FreeSubstProgramValueSyntax.inputGuard w b a c L n).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FreeSubstProgramValueSyntax.inputGuard w b a c L n).neg) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.reject_input hZ w b a c L n q h0 h1

theorem freeRejectInput_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeRejectInputSentence w b a c L n q)) := TheoryTransport.sentence (source_freeRejectInput w b a c L n q)

theorem native_freeRejectInput {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeRejectInputSentence w b a c L n q)) := ZFReplay.replay (freeRejectInput_kernel_certificate w b a c L n q)

def freeRejectTargetSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaCodeSyntax.formulaCode w q b c).neg).imp (((FreeSubstProgramSyntax.executed w b a c L n q).neg)))).close

theorem source_freeRejectTarget {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeRejectTargetSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FormulaCodeSyntax.formulaCode w q b c).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FormulaCodeSyntax.formulaCode w q b c).neg) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.reject_target hZ w b a c L n q h0 h1

theorem freeRejectTarget_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeRejectTargetSentence w b a c L n q)) := TheoryTransport.sentence (source_freeRejectTarget w b a c L n q)

theorem native_freeRejectTarget {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeRejectTargetSentence w b a c L n q)) := ZFReplay.replay (freeRejectTarget_kernel_certificate w b a c L n q)

def freeRejectOutputNaturalSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem q w).neg).imp (((FreeSubstProgramSyntax.executed w b a c L n q).neg)))).close

theorem source_freeRejectOutputNatural {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeRejectOutputNaturalSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem q w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem q w).neg) := .hyp (Or.inl rfl)
  exact FreeSubstProgramValue.reject_output_natural hZ w b a c L n q h0 h1

theorem freeRejectOutputNatural_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeRejectOutputNaturalSentence w b a c L n q)) := TheoryTransport.sentence (source_freeRejectOutputNatural w b a c L n q)

theorem native_freeRejectOutputNatural {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeRejectOutputNaturalSentence w b a c L n q)) := ZFReplay.replay (freeRejectOutputNatural_kernel_certificate w b a c L n q)

def weakForwardSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxWeakenFreeSyntax.weakened w a b B n q).imp ((WeakenFreeProgramSyntax.executed w a b B n q)))).close

theorem source_weakForward {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakForwardSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxWeakenFreeSyntax.weakened w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxWeakenFreeSyntax.weakened w a b B n q) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramCorrectness.forward hZ w a b B n q h0 h1

theorem weakForward_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakForwardSentence w a b B n q)) := TheoryTransport.sentence (source_weakForward w a b B n q)

theorem native_weakForward {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakForwardSentence w a b B n q)) := ZFReplay.replay (weakForward_kernel_certificate w a b B n q)

def weakReverseSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((WeakenFreeProgramSyntax.executed w a b B n q).imp ((SyntaxWeakenFreeSyntax.weakened w a b B n q)))).close

theorem source_weakReverse {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakReverseSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (WeakenFreeProgramSyntax.executed w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (WeakenFreeProgramSyntax.executed w a b B n q) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramCorrectness.reverse hZ w a b B n q h0 h1

theorem weakReverse_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakReverseSentence w a b B n q)) := TheoryTransport.sentence (source_weakReverse w a b B n q)

theorem native_weakReverse {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakReverseSentence w a b B n q)) := ZFReplay.replay (weakReverse_kernel_certificate w a b B n q)

def weakExecutionIffSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp (((WeakenFreeProgramSyntax.executed w a b B n q).iff (SyntaxWeakenFreeSyntax.weakened w a b B n q)))).close

theorem source_weakExecutionIff {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakExecutionIffSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramCorrectness.executed_iff hZ w a b B n q h0

theorem weakExecutionIff_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakExecutionIffSentence w a b B n q)) := TheoryTransport.sentence (source_weakExecutionIff w a b B n q)

theorem native_weakExecutionIff {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakExecutionIffSentence w a b B n q)) := ZFReplay.replay (weakExecutionIff_kernel_certificate w a b B n q)

def weakInputOfExecutionSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((WeakenFreeProgramSyntax.executed w a b B n q).imp ((WeakenFreeProgramValueSyntax.inputGuard w a b B n)))).close

theorem source_weakInputOfExecution {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakInputOfExecutionSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (WeakenFreeProgramSyntax.executed w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (WeakenFreeProgramSyntax.executed w a b B n q) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.input_of_execution hZ w a b B n q h0 h1

theorem weakInputOfExecution_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakInputOfExecutionSentence w a b B n q)) := TheoryTransport.sentence (source_weakInputOfExecution w a b B n q)

theorem native_weakInputOfExecution {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakInputOfExecutionSentence w a b B n q)) := ZFReplay.replay (weakInputOfExecution_kernel_certificate w a b B n q)

def weakSourceTypeSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((WeakenFreeProgramSyntax.executed w a b B n q).imp ((FormulaCodeSyntax.formulaCode w n a b)))).close

theorem source_weakSourceType {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakSourceTypeSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (WeakenFreeProgramSyntax.executed w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (WeakenFreeProgramSyntax.executed w a b B n q) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.source_type hZ w a b B n q h0 h1

theorem weakSourceType_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakSourceTypeSentence w a b B n q)) := TheoryTransport.sentence (source_weakSourceType w a b B n q)

theorem native_weakSourceType {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakSourceTypeSentence w a b B n q)) := ZFReplay.replay (weakSourceType_kernel_certificate w a b B n q)

def weakTargetTypeSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((WeakenFreeProgramSyntax.executed w a b B n q).imp ((FormulaCodeSyntax.formulaCode w q a B)))).close

theorem source_weakTargetType {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakTargetTypeSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (WeakenFreeProgramSyntax.executed w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (WeakenFreeProgramSyntax.executed w a b B n q) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.target_type hZ w a b B n q h0 h1

theorem weakTargetType_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakTargetTypeSentence w a b B n q)) := TheoryTransport.sentence (source_weakTargetType w a b B n q)

theorem native_weakTargetType {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakTargetTypeSentence w a b B n q)) := ZFReplay.replay (weakTargetType_kernel_certificate w a b B n q)

def weakOutputNaturalSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((WeakenFreeProgramSyntax.executed w a b B n q).imp ((Formula.mem q w)))).close

theorem source_weakOutputNatural {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakOutputNaturalSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (WeakenFreeProgramSyntax.executed w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (WeakenFreeProgramSyntax.executed w a b B n q) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.output_natural hZ w a b B n q h0 h1

theorem weakOutputNatural_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakOutputNaturalSentence w a b B n q)) := TheoryTransport.sentence (source_weakOutputNatural w a b B n q)

theorem native_weakOutputNatural {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakOutputNaturalSentence w a b B n q)) := ZFReplay.replay (weakOutputNatural_kernel_certificate w a b B n q)

def weakUniqueOutputSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((WeakenFreeProgramSyntax.executed w a b B n q).imp ((WeakenFreeProgramValueSyntax.uniqueOutput w a b B n q)))).close

theorem source_weakUniqueOutput {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakUniqueOutputSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (WeakenFreeProgramSyntax.executed w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (WeakenFreeProgramSyntax.executed w a b B n q) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.unique_output hZ w a b B n q h0 h1

theorem weakUniqueOutput_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakUniqueOutputSentence w a b B n q)) := TheoryTransport.sentence (source_weakUniqueOutput w a b B n q)

theorem native_weakUniqueOutput {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakUniqueOutputSentence w a b B n q)) := ZFReplay.replay (weakUniqueOutput_kernel_certificate w a b B n q)

def weakAtCandidateSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp ((WeakenFreeProgramSyntax.executed w a b B n q).imp ((WeakenFreeProgramValueSyntax.value w a b B n q)))).close

theorem source_weakAtCandidate {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakAtCandidateSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (WeakenFreeProgramSyntax.executed w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (WeakenFreeProgramSyntax.executed w a b B n q) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.at_candidate hZ w a b B n q h0 h1

theorem weakAtCandidate_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakAtCandidateSentence w a b B n q)) := TheoryTransport.sentence (source_weakAtCandidate w a b B n q)

theorem native_weakAtCandidate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakAtCandidateSentence w a b B n q)) := ZFReplay.replay (weakAtCandidate_kernel_certificate w a b B n q)

def weakUniqueSentence {m} (w a b B n q v : Fin m) : Source.Sentence := ((omega w).imp ((WeakenFreeProgramSyntax.executed w a b B n q).imp ((WeakenFreeProgramSyntax.executed w a b B n v).imp ((Formula.equal q v))))).close

theorem source_weakUnique {m} (w a b B n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakUniqueSentence w a b B n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (WeakenFreeProgramSyntax.executed w a b B n v) (Context.add (WeakenFreeProgramSyntax.executed w a b B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (WeakenFreeProgramSyntax.executed w a b B n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (WeakenFreeProgramSyntax.executed w a b B n v) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.unique hZ w a b B n q v h0 h1 h2

theorem weakUnique_kernel_certificate {m} (w a b B n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakUniqueSentence w a b B n q v)) := TheoryTransport.sentence (source_weakUnique w a b B n q v)

theorem native_weakUnique {m} (w a b B n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakUniqueSentence w a b B n q v)) := ZFReplay.replay (weakUnique_kernel_certificate w a b B n q v)

def weakActualFiberSentence {m} (w a b B n : Fin m) : Source.Sentence := ((omega w).imp ((WeakenFreeProgramValueSyntax.inputGuard w a b B n).imp ((WeakenFreeProgramValueSyntax.fiber w a b B n)))).close

theorem source_weakActualFiber {m} (w a b B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakActualFiberSentence w a b B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (WeakenFreeProgramValueSyntax.inputGuard w a b B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (WeakenFreeProgramValueSyntax.inputGuard w a b B n) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.actual_fiber hZ w a b B n h0 h1

theorem weakActualFiber_kernel_certificate {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakActualFiberSentence w a b B n)) := TheoryTransport.sentence (source_weakActualFiber w a b B n)

theorem native_weakActualFiber {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakActualFiberSentence w a b B n)) := ZFReplay.replay (weakActualFiber_kernel_certificate w a b B n)

def weakFiberIffInputSentence {m} (w a b B n : Fin m) : Source.Sentence := ((omega w).imp (((WeakenFreeProgramValueSyntax.fiber w a b B n).iff (WeakenFreeProgramValueSyntax.inputGuard w a b B n)))).close

theorem source_weakFiberIffInput {m} (w a b B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakFiberIffInputSentence w a b B n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.fiber_iff_input hZ w a b B n h0

theorem weakFiberIffInput_kernel_certificate {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakFiberIffInputSentence w a b B n)) := TheoryTransport.sentence (source_weakFiberIffInput w a b B n)

theorem native_weakFiberIffInput {m} (w a b B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakFiberIffInputSentence w a b B n)) := ZFReplay.replay (weakFiberIffInput_kernel_certificate w a b B n)

def weakRejectEnvironmentSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp (((OmegaSyntax.successor B b).neg).imp (((WeakenFreeProgramSyntax.executed w a b B n q).neg)))).close

theorem source_weakRejectEnvironment {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakRejectEnvironmentSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((OmegaSyntax.successor B b).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((OmegaSyntax.successor B b).neg) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.reject_successor hZ w a b B n q h0 h1

theorem weakRejectEnvironment_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakRejectEnvironmentSentence w a b B n q)) := TheoryTransport.sentence (source_weakRejectEnvironment w a b B n q)

theorem native_weakRejectEnvironment {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakRejectEnvironmentSentence w a b B n q)) := ZFReplay.replay (weakRejectEnvironment_kernel_certificate w a b B n q)

def weakRejectSourceSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaCodeSyntax.formulaCode w n a b).neg).imp (((WeakenFreeProgramSyntax.executed w a b B n q).neg)))).close

theorem source_weakRejectSource {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakRejectSourceSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FormulaCodeSyntax.formulaCode w n a b).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FormulaCodeSyntax.formulaCode w n a b).neg) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.reject_source hZ w a b B n q h0 h1

theorem weakRejectSource_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakRejectSourceSentence w a b B n q)) := TheoryTransport.sentence (source_weakRejectSource w a b B n q)

theorem native_weakRejectSource {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakRejectSourceSentence w a b B n q)) := ZFReplay.replay (weakRejectSource_kernel_certificate w a b B n q)

def weakRejectInputSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp (((WeakenFreeProgramValueSyntax.inputGuard w a b B n).neg).imp (((WeakenFreeProgramSyntax.executed w a b B n q).neg)))).close

theorem source_weakRejectInput {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakRejectInputSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((WeakenFreeProgramValueSyntax.inputGuard w a b B n).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((WeakenFreeProgramValueSyntax.inputGuard w a b B n).neg) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.reject_input hZ w a b B n q h0 h1

theorem weakRejectInput_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakRejectInputSentence w a b B n q)) := TheoryTransport.sentence (source_weakRejectInput w a b B n q)

theorem native_weakRejectInput {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakRejectInputSentence w a b B n q)) := ZFReplay.replay (weakRejectInput_kernel_certificate w a b B n q)

def weakRejectTargetSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp (((FormulaCodeSyntax.formulaCode w q a B).neg).imp (((WeakenFreeProgramSyntax.executed w a b B n q).neg)))).close

theorem source_weakRejectTarget {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakRejectTargetSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((FormulaCodeSyntax.formulaCode w q a B).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((FormulaCodeSyntax.formulaCode w q a B).neg) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.reject_target hZ w a b B n q h0 h1

theorem weakRejectTarget_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakRejectTargetSentence w a b B n q)) := TheoryTransport.sentence (source_weakRejectTarget w a b B n q)

theorem native_weakRejectTarget {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakRejectTargetSentence w a b B n q)) := ZFReplay.replay (weakRejectTarget_kernel_certificate w a b B n q)

def weakRejectOutputNaturalSentence {m} (w a b B n q : Fin m) : Source.Sentence := ((omega w).imp (((Formula.mem q w).neg).imp (((WeakenFreeProgramSyntax.executed w a b B n q).neg)))).close

theorem source_weakRejectOutputNatural {m} (w a b B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakRejectOutputNaturalSentence w a b B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem q w).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((Formula.mem q w).neg) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.reject_output_natural hZ w a b B n q h0 h1

theorem weakRejectOutputNatural_kernel_certificate {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakRejectOutputNaturalSentence w a b B n q)) := TheoryTransport.sentence (source_weakRejectOutputNatural w a b B n q)

theorem native_weakRejectOutputNatural {m} (w a b B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakRejectOutputNaturalSentence w a b B n q)) := ZFReplay.replay (weakRejectOutputNatural_kernel_certificate w a b B n q)

def weakActualSuccessorStateSentence {m} (w a b n : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeSyntax.formulaCode w n a b).imp ((WeakenFreeProgramValueSyntax.actualState w a b n)))).close

theorem source_weakActualSuccessorState {m} (w a b n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (weakActualSuccessorStateSentence w a b n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inl rfl)
  exact WeakenFreeProgramValue.actual_state hZ w a b n h0 h1

theorem weakActualSuccessorState_kernel_certificate {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (weakActualSuccessorStateSentence w a b n)) := TheoryTransport.sentence (source_weakActualSuccessorState w a b n)

theorem native_weakActualSuccessorState {m} (w a b n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (weakActualSuccessorStateSentence w a b n)) := ZFReplay.replay (weakActualSuccessorState_kernel_certificate w a b n)

end PPAC.Migration.Internal.ObjectFreeVariablePrograms
