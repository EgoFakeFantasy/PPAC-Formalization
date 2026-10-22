import PPAC.Migration.Internal.SyntaxFormulaFreeSubstAtoms
import PPAC.Migration.Internal.SyntaxFormulaFreeSubstTerms
import PPAC.Migration.Internal.SyntaxFormulaFreeSubstLogicalInternal

/-! 原项码列表参数的全公式free替换及原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectFormulaFreeSubst
open Source SourceAlgebra SourceLogic OmegaSyntax

def inputSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).imp ((SyntaxFormulaFreeSubstSyntax.input w b a c L n)))).close

theorem source_input {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (inputSentence w b a c L n q) := by
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
  exact SyntaxFormulaFreeSubstOutput.input_of_substituted hZ w b a c L n q h0 h1

theorem input_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (inputSentence w b a c L n q)) := TheoryTransport.sentence (source_input w b a c L n q)

theorem native_input {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (inputSentence w b a c L n q)) := ZFReplay.replay (input_kernel_certificate w b a c L n q)

def sourceTypeSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).imp ((FormulaCodeSyntax.formulaCode w n b a)))).close

theorem source_sourceType {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceTypeSentence w b a c L n q) := by
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
  exact SyntaxFormulaFreeSubstOutput.source_type hZ w b a c L n q h0 h1

theorem sourceType_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceTypeSentence w b a c L n q)) := TheoryTransport.sentence (source_sourceType w b a c L n q)

theorem native_sourceType {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceTypeSentence w b a c L n q)) := ZFReplay.replay (sourceType_kernel_certificate w b a c L n q)

def targetTypeSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).imp ((FormulaCodeSyntax.formulaCode w q b c))).close

theorem source_targetType {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetTypeSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstOutput.target_type w b a c L n q h0

theorem targetType_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetTypeSentence w b a c L n q)) := TheoryTransport.sentence (source_targetType w b a c L n q)

theorem native_targetType {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetTypeSentence w b a c L n q)) := ZFReplay.replay (targetType_kernel_certificate w b a c L n q)

def outputNaturalSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).imp ((Formula.mem q w))).close

theorem source_outputNatural {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputNaturalSentence w b a c L n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstOutput.output_natural w b a c L n q h0

theorem outputNatural_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputNaturalSentence w b a c L n q)) := TheoryTransport.sentence (source_outputNatural w b a c L n q)

theorem native_outputNatural {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputNaturalSentence w b a c L n q)) := ZFReplay.replay (outputNatural_kernel_certificate w b a c L n q)

def existsOutputSentence {m} (w b a c L n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaFreeSubstSyntax.input w b a c L n).imp ((SyntaxFormulaFreeSubstSyntax.existsOutput w b a c L n)))).close

theorem source_existsOutput {m} (w b a c L n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsOutputSentence w b a c L n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaFreeSubstSyntax.input w b a c L n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFormulaFreeSubstSyntax.input w b a c L n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstOutput.exists_output hZ w b a c L n h0 h1

theorem existsOutput_kernel_certificate {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsOutputSentence w b a c L n)) := TheoryTransport.sentence (source_existsOutput w b a c L n)

theorem native_existsOutput {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsOutputSentence w b a c L n)) := ZFReplay.replay (existsOutput_kernel_certificate w b a c L n)

def atCodesSentence {m} (w b a c L n q R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (SyntaxRenameJudgmentSyntax.renamed w R S b a b c n q)))))).close

theorem source_atCodes {m} (w b a c L n q R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atCodesSentence w b a c L n q R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L n q R S h0 h1 h2

theorem atCodes_kernel_certificate {m} (w b a c L n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atCodesSentence w b a c L n q R S)) := TheoryTransport.sentence (source_atCodes w b a c L n q R S)

theorem native_atCodes {m} (w b a c L n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atCodesSentence w b a c L n q R S)) := ZFReplay.replay (atCodes_kernel_certificate w b a c L n q R S)

def outputUniqueSentence {m} (w b a c L n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).imp ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n v).imp ((Formula.equal q v))))).close

theorem source_outputUnique {m} (w b a c L n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputUniqueSentence w b a c L n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n v) (Context.add (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFormulaFreeSubstSyntax.substituted w b a c L n v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstUnique.unique hZ w b a c L n q v h0 h1 h2

theorem outputUnique_kernel_certificate {m} (w b a c L n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputUniqueSentence w b a c L n q v)) := TheoryTransport.sentence (source_outputUnique w b a c L n q v)

theorem native_outputUnique {m} (w b a c L n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputUniqueSentence w b a c L n q v)) := ZFReplay.replay (outputUnique_kernel_certificate w b a c L n q v)

def uniqueOutputSentence {m} (w b a c L n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).imp ((SyntaxFormulaFreeSubstSyntax.uniqueOutput w b a c L n q)))).close

theorem source_uniqueOutput {m} (w b a c L n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueOutputSentence w b a c L n q) := by
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
  exact SyntaxFormulaFreeSubstUnique.unique_output hZ w b a c L n q h0 h1

theorem uniqueOutput_kernel_certificate {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueOutputSentence w b a c L n q)) := TheoryTransport.sentence (source_uniqueOutput w b a c L n q)

theorem native_uniqueOutput {m} (w b a c L n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueOutputSentence w b a c L n q)) := ZFReplay.replay (uniqueOutput_kernel_certificate w b a c L n q)

def actualFiberSentence {m} (w b a c L n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaFreeSubstSyntax.input w b a c L n).imp ((SyntaxFormulaFreeSubstSyntax.fiber w b a c L n)))).close

theorem source_actualFiber {m} (w b a c L n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualFiberSentence w b a c L n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaFreeSubstSyntax.input w b a c L n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFormulaFreeSubstSyntax.input w b a c L n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstUnique.actual_fiber hZ w b a c L n h0 h1

theorem actualFiber_kernel_certificate {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualFiberSentence w b a c L n)) := TheoryTransport.sentence (source_actualFiber w b a c L n)

theorem native_actualFiber {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualFiberSentence w b a c L n)) := ZFReplay.replay (actualFiber_kernel_certificate w b a c L n)

def existsInputIffSentence {m} (w b a c L n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxFormulaFreeSubstSyntax.existsOutput w b a c L n).iff (SyntaxFormulaFreeSubstSyntax.input w b a c L n)))).close

theorem source_existsInputIff {m} (w b a c L n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsInputIffSentence w b a c L n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstUnique.exists_iff_input hZ w b a c L n h0

theorem existsInputIff_kernel_certificate {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsInputIffSentence w b a c L n)) := TheoryTransport.sentence (source_existsInputIff w b a c L n)

theorem native_existsInputIff {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsInputIffSentence w b a c L n)) := ZFReplay.replay (existsInputIff_kernel_certificate w b a c L n)

def fiberInputIffSentence {m} (w b a c L n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxFormulaFreeSubstSyntax.fiber w b a c L n).iff (SyntaxFormulaFreeSubstSyntax.input w b a c L n)))).close

theorem source_fiberInputIff {m} (w b a c L n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberInputIffSentence w b a c L n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstUnique.fiber_iff_input hZ w b a c L n h0

theorem fiberInputIff_kernel_certificate {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberInputIffSentence w b a c L n)) := TheoryTransport.sentence (source_fiberInputIff w b a c L n)

theorem native_fiberInputIff {m} (w b a c L n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberInputIffSentence w b a c L n)) := ZFReplay.replay (fiberInputIff_kernel_certificate w b a c L n)

def negationSentence {m} (w b a c L n q x X R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w b a c L x X)))))))).close

theorem source_negation {m} (w b a c L n q x X R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationSentence w b a c L n q x X R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstLogical.negation_iff hZ w b a c L n q x X R S h0 h1 h2 h3 h4

theorem negation_kernel_certificate {m} (w b a c L n q x X R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationSentence w b a c L n q x X R S)) := TheoryTransport.sentence (source_negation w b a c L n q x X R S)

theorem native_negation {m} (w b a c L n q x X R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationSentence w b a c L n q x X R S)) := ZFReplay.replay (negation_kernel_certificate w b a c L n q x X R S)

def binarySentence {m} (kind : Fin 4) (w b a c L n q x y X Y R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L x X).conj (SyntaxFormulaFreeSubstSyntax.substituted w b a c L y Y))))))))).close

theorem source_binary {m} (kind : Fin 4) (w b a c L n q x y X Y R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binarySentence kind w b a c L n q x y X Y R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstLogical.binary_iff hZ kind w b a c L n q x y X Y R S h0 h1 h2 h3 h4

theorem binary_kernel_certificate {m} (kind : Fin 4) (w b a c L n q x y X Y R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binarySentence kind w b a c L n q x y X Y R S)) := TheoryTransport.sentence (source_binary kind w b a c L n q x y X Y R S)

theorem native_binary {m} (kind : Fin 4) (w b a c L n q x y X Y R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binarySentence kind w b a c L n q x y X Y R S)) := ZFReplay.replay (binary_kernel_certificate kind w b a c L n q x y X Y R S)

def quantifiedSentence {m} (universal : Bool) (w b a c L n q x X R S u K : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((successor u b).imp ((SyntaxIdentityMapSyntax.identityCode w u K).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w u a c L x X)))))))))).close

theorem source_quantified {m} (universal : Bool) (w b a c L n q x X R S u K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifiedSentence universal w b a c L n q x X R S u K) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (SyntaxIdentityMapSyntax.identityCode w u K) (Context.add (successor u b) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor u b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w u K) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstLogical.quantified_iff hZ universal w b a c L n q x X R S u K h0 h1 h2 h3 h4 h5 h6

theorem quantified_kernel_certificate {m} (universal : Bool) (w b a c L n q x X R S u K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifiedSentence universal w b a c L n q x X R S u K)) := TheoryTransport.sentence (source_quantified universal w b a c L n q x X R S u K)

theorem native_quantified {m} (universal : Bool) (w b a c L n q x X R S u K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifiedSentence universal w b a c L n q x X R S u K)) := ZFReplay.replay (quantified_kernel_certificate universal w b a c L n q x X R S u K)

def forallSentence {m} (w b a c L n q x X R S u K : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((successor u b).imp ((SyntaxIdentityMapSyntax.identityCode w u K).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxLogicalSyntax.singleCode 9 w X q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w u a c L x X)))))))))).close

theorem source_forall {m} (w b a c L n q x X R S u K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallSentence w b a c L n q x X R S u K) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxIdentityMapSyntax.identityCode w u K) (Context.add (successor u b) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor u b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w u K) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w X q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstLogical.forall_iff hZ w b a c L n q x X R S u K h0 h1 h2 h3 h4 h5 h6

theorem forall_kernel_certificate {m} (w b a c L n q x X R S u K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallSentence w b a c L n q x X R S u K)) := TheoryTransport.sentence (source_forall w b a c L n q x X R S u K)

theorem native_forall {m} (w b a c L n q x X R S u K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallSentence w b a c L n q x X R S u K)) := ZFReplay.replay (forall_kernel_certificate w b a c L n q x X R S u K)

def existsSentence {m} (w b a c L n q x X R S u K : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((successor u b).imp ((SyntaxIdentityMapSyntax.identityCode w u K).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxLogicalSyntax.singleCode 10 w X q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w u a c L x X)))))))))).close

theorem source_exists {m} (w b a c L n q x X R S u K : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsSentence w b a c L n q x X R S u K) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxIdentityMapSyntax.identityCode w u K) (Context.add (successor u b) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (successor u b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w u K) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w X q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstLogical.exists_iff hZ w b a c L n q x X R S u K h0 h1 h2 h3 h4 h5 h6

theorem exists_kernel_certificate {m} (w b a c L n q x X R S u K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsSentence w b a c L n q x X R S u K)) := TheoryTransport.sentence (source_exists w b a c L n q x X R S u K)

theorem native_exists {m} (w b a c L n q x X R S u K : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsSentence w b a c L n q x X R S u K)) := ZFReplay.replay (exists_kernel_certificate w b a c L n q x X R S u K)

def nullarySentence {m} (truth : Bool) (w b a c L n q R S r s : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxMapCodeSyntax.encoded w r b b R).imp ((SyntaxMapCodeSyntax.encoded w s a c S).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (Formula.equal n q))))))))).close

theorem source_nullary {m} (truth : Bool) (w b a c L n q R S r s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullarySentence truth w b a c L n q R S r s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (SyntaxMapCodeSyntax.encoded w s a c S) (Context.add (SyntaxMapCodeSyntax.encoded w r b b R) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r b b R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s a c S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstAtoms.nullary_iff hZ truth w b a c L n q R S r s h0 h1 h2 h3 h4 h5

theorem nullary_kernel_certificate {m} (truth : Bool) (w b a c L n q R S r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullarySentence truth w b a c L n q R S r s)) := TheoryTransport.sentence (source_nullary truth w b a c L n q R S r s)

theorem native_nullary {m} (truth : Bool) (w b a c L n q R S r s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullarySentence truth w b a c L n q R S r s)) := ZFReplay.replay (nullary_kernel_certificate truth w b a c L n q R S r s)

def equalitySentence {m} (w b a c L n q R S r s x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxMapCodeSyntax.encoded w r b b R).imp ((SyntaxMapCodeSyntax.encoded w s a c S).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxAtomSyntax.equalCode w X Y q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (SyntaxRenameKnownFieldsSyntax.equalOperands w r s b a b c x y X Y)))))))))).close

theorem source_equality {m} (w b a c L n q R S r s x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalitySentence w b a c L n q R S r s x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w X Y q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s a c S) (Context.add (SyntaxMapCodeSyntax.encoded w r b b R) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r b b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s a c S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxAtomSyntax.equalCode w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstAtoms.equality_iff hZ w b a c L n q R S r s x y X Y h0 h1 h2 h3 h4 h5 h6

theorem equality_kernel_certificate {m} (w b a c L n q R S r s x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalitySentence w b a c L n q R S r s x y X Y)) := TheoryTransport.sentence (source_equality w b a c L n q R S r s x y X Y)

theorem native_equality {m} (w b a c L n q R S r s x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalitySentence w b a c L n q R S r s x y X Y)) := ZFReplay.replay (equality_kernel_certificate w b a c L n q R S r s x y X Y)

def membershipSentence {m} (w b a c L n q R S r s z Z x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxMapCodeSyntax.encoded w r b b R).imp ((SyntaxMapCodeSyntax.encoded w s a c S).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxAtomSyntax.memberCode w Z X Y q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (SyntaxRenameKnownFieldsSyntax.memberOperands w r s b a b c z Z x y X Y)))))))))).close

theorem source_membership {m} (w b a c L n q R S r s z Z x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipSentence w b a c L n q R S r s z Z x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w Z X Y q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s a c S) (Context.add (SyntaxMapCodeSyntax.encoded w r b b R) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r b b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s a c S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxAtomSyntax.memberCode w Z X Y q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstAtoms.membership_iff hZ w b a c L n q R S r s z Z x y X Y h0 h1 h2 h3 h4 h5 h6

theorem membership_kernel_certificate {m} (w b a c L n q R S r s z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipSentence w b a c L n q R S r s z Z x y X Y)) := TheoryTransport.sentence (source_membership w b a c L n q R S r s z Z x y X Y)

theorem native_membership {m} (w b a c L n q R S r s z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipSentence w b a c L n q R S r s z Z x y X Y)) := ZFReplay.replay (membership_kernel_certificate w b a c L n q R S r s z Z x y X Y)

def boundTermSentence {m} (w b a c R S r s n q i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxIdentityMapSyntax.identityCode w b R).imp ((SyntaxMapCodeSyntax.encoded w r b b R).imp ((SyntaxMapCodeSyntax.encoded w s a c S).imp ((SyntaxVariableSyntax.code true w i n).imp ((SyntaxVariableSyntax.code true w j q).imp (((SyntaxRenameTermSyntax.renamed w r s b a b c n q).iff ((Formula.mem i b).conj (Formula.equal i j)))))))))).close

theorem source_boundTerm {m} (w b a c R S r s n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundTermSentence w b a c R S r s n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code true w j q) (Context.add (SyntaxVariableSyntax.code true w i n) (Context.add (SyntaxMapCodeSyntax.encoded w s a c S) (Context.add (SyntaxMapCodeSyntax.encoded w r b b R) (Context.add (SyntaxIdentityMapSyntax.identityCode w b R) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxIdentityMapSyntax.identityCode w b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r b b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s a c S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxVariableSyntax.code true w i n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxVariableSyntax.code true w j q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstTerms.bound_iff hZ w b a c R S r s n q i j h0 h1 h2 h3 h4 h5

theorem boundTerm_kernel_certificate {m} (w b a c R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundTermSentence w b a c R S r s n q i j)) := TheoryTransport.sentence (source_boundTerm w b a c R S r s n q i j)

theorem native_boundTerm {m} (w b a c R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundTermSentence w b a c R S r s n q i j)) := ZFReplay.replay (boundTerm_kernel_certificate w b a c R S r s n q i j)

def freeTermFieldSentence {m} (w b a c L R S r s n q i j : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFreeSubstSyntax.codeConversion w a c L S).imp ((SyntaxMapCodeSyntax.encoded w r b b R).imp ((SyntaxMapCodeSyntax.encoded w s a c S).imp ((SyntaxVariableSyntax.code false w i n).imp ((SyntaxVariableSyntax.code false w j q).imp (((SyntaxRenameTermSyntax.renamed w r s b a b c n q).iff ((Formula.mem i a).conj (StructuralListFieldSyntax.field w L i q)))))))))).close

theorem source_freeTermField {m} (w b a c L R S r s n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeTermFieldSentence w b a c L R S r s n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxVariableSyntax.code false w j q) (Context.add (SyntaxVariableSyntax.code false w i n) (Context.add (SyntaxMapCodeSyntax.encoded w s a c S) (Context.add (SyntaxMapCodeSyntax.encoded w r b b R) (Context.add (SyntaxFreeSubstSyntax.codeConversion w a c L S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxFreeSubstSyntax.codeConversion w a c L S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r b b R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s a c S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxVariableSyntax.code false w i n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxVariableSyntax.code false w j q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstTerms.free_field_iff hZ w b a c L R S r s n q i j h0 h1 h2 h3 h4 h5

theorem freeTermField_kernel_certificate {m} (w b a c L R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeTermFieldSentence w b a c L R S r s n q i j)) := TheoryTransport.sentence (source_freeTermField w b a c L R S r s n q i j)

theorem native_freeTermField {m} (w b a c L R S r s n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeTermFieldSentence w b a c L R S r s n q i j)) := ZFReplay.replay (freeTermField_kernel_certificate w b a c L R S r s n q i j)

def actualCodesSentence {m} (w b a c L : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp ((SyntaxFormulaFreeSubstLogicalInternal.actualCodes w b a c L))))).close

theorem source_actualCodes {m} (w b a c L : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualCodesSentence w b a c L) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstLogicalInternal.actual_codes_exists hZ w b a c L h0 h1 h2

theorem actualCodes_kernel_certificate {m} (w b a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualCodesSentence w b a c L)) := TheoryTransport.sentence (source_actualCodes w b a c L)

theorem native_actualCodes {m} (w b a c L : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualCodesSentence w b a c L)) := ZFReplay.replay (actualCodes_kernel_certificate w b a c L)

def internalNegationSentence {m} (w b a c L n q x X : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w b a c L x X)))))))).close

theorem source_internalNegation {m} (w b a c L n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (internalNegationSentence w b a c L n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstLogicalInternal.negation_iff hZ w b a c L n q x X h0 h1 h2 h3 h4

theorem internalNegation_kernel_certificate {m} (w b a c L n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (internalNegationSentence w b a c L n q x X)) := TheoryTransport.sentence (source_internalNegation w b a c L n q x X)

theorem native_internalNegation {m} (w b a c L n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (internalNegationSentence w b a c L n q x X)) := ZFReplay.replay (internalNegation_kernel_certificate w b a c L n q x X)

def internalBinarySentence {m} (kind : Fin 4) (w b a c L n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff ((SyntaxFormulaFreeSubstSyntax.substituted w b a c L x X).conj (SyntaxFormulaFreeSubstSyntax.substituted w b a c L y Y))))))))).close

theorem source_internalBinary {m} (kind : Fin 4) (w b a c L n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (internalBinarySentence kind w b a c L n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstLogicalInternal.binary_iff hZ kind w b a c L n q x y X Y h0 h1 h2 h3 h4

theorem internalBinary_kernel_certificate {m} (kind : Fin 4) (w b a c L n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (internalBinarySentence kind w b a c L n q x y X Y)) := TheoryTransport.sentence (source_internalBinary kind w b a c L n q x y X Y)

theorem native_internalBinary {m} (kind : Fin 4) (w b a c L n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (internalBinarySentence kind w b a c L n q x y X Y)) := ZFReplay.replay (internalBinary_kernel_certificate kind w b a c L n q x y X Y)

def internalQuantifiedSentence {m} (universal : Bool) (w b a c L n q x X u : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem b w).imp ((SyntaxFreeSubstSyntax.termList w a c L).imp ((successor u b).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q).imp (((SyntaxFormulaFreeSubstSyntax.substituted w b a c L n q).iff (SyntaxFormulaFreeSubstSyntax.substituted w u a c L x X))))))))).close

theorem source_internalQuantified {m} (universal : Bool) (w b a c L n q x X u : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (internalQuantifiedSentence universal w b a c L n q x X u) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (successor u b) (Context.add (SyntaxFreeSubstSyntax.termList w a c L) (Context.add (Formula.mem b w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (Formula.mem b w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxFreeSubstSyntax.termList w a c L) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (successor u b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) := .hyp (Or.inl rfl)
  exact SyntaxFormulaFreeSubstLogicalInternal.quantified_iff hZ universal w b a c L n q x X u h0 h1 h2 h3 h4 h5

theorem internalQuantified_kernel_certificate {m} (universal : Bool) (w b a c L n q x X u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (internalQuantifiedSentence universal w b a c L n q x X u)) := TheoryTransport.sentence (source_internalQuantified universal w b a c L n q x X u)

theorem native_internalQuantified {m} (universal : Bool) (w b a c L n q x X u : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (internalQuantifiedSentence universal w b a c L n q x X u)) := ZFReplay.replay (internalQuantified_kernel_certificate universal w b a c L n q x X u)

end PPAC.Migration.Internal.ObjectFormulaFreeSubst
