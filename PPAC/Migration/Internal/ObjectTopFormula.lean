import PPAC.Migration.Internal.SyntaxTopFormulaLogicalEndpoints

/-! 首槽公式实际唯一输出与完整构造端点的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectTopFormula
open Source SourceAlgebra SourceLogic OmegaSyntax

def instantiateAtCodesSentence {m} (w a b A t n q R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w R S A b a b n q))))).close

theorem source_instantiateAtCodes {m} (w a b A t n q R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateAtCodesSentence w a b A t n q R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.instantiateCoded w a b A t R S) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaCodes.instantiate_at_codes hZ w a b A t n q R S h0 h1

theorem instantiateAtCodes_kernel_certificate {m} (w a b A t n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateAtCodesSentence w a b A t n q R S)) := TheoryTransport.sentence (source_instantiateAtCodes w a b A t n q R S)

theorem native_instantiateAtCodes {m} (w a b A t n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateAtCodesSentence w a b A t n q R S)) := ZFReplay.replay (instantiateAtCodes_kernel_certificate w a b A t n q R S)

def instantiateEnvironmentSentence {m} (w a b A t n q : Fin m) : Source.Sentence := ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).imp ((SyntaxTopEnvironmentSyntax.instantiateInput w a b A t))).close

theorem source_instantiateEnvironment {m} (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateEnvironmentSentence w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiated w a b A t n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w a b A t n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.instantiate_environment w a b A t n q h0

theorem instantiateEnvironment_kernel_certificate {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateEnvironmentSentence w a b A t n q)) := TheoryTransport.sentence (source_instantiateEnvironment w a b A t n q)

theorem native_instantiateEnvironment {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateEnvironmentSentence w a b A t n q)) := ZFReplay.replay (instantiateEnvironment_kernel_certificate w a b A t n q)

def instantiateSourceTypeSentence {m} (w a b A t n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).imp ((FormulaCodeSyntax.formulaCode w n A b)))).close

theorem source_instantiateSourceType {m} (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateSourceTypeSentence w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiated w a b A t n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w a b A t n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.instantiate_source_type hZ w a b A t n q h0 h1

theorem instantiateSourceType_kernel_certificate {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateSourceTypeSentence w a b A t n q)) := TheoryTransport.sentence (source_instantiateSourceType w a b A t n q)

theorem native_instantiateSourceType {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateSourceTypeSentence w a b A t n q)) := ZFReplay.replay (instantiateSourceType_kernel_certificate w a b A t n q)

def instantiateTargetTypeSentence {m} (w a b A t n q : Fin m) : Source.Sentence := ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).imp ((FormulaCodeSyntax.formulaCode w q a b))).close

theorem source_instantiateTargetType {m} (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateTargetTypeSentence w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiated w a b A t n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w a b A t n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.instantiate_target_type w a b A t n q h0

theorem instantiateTargetType_kernel_certificate {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateTargetTypeSentence w a b A t n q)) := TheoryTransport.sentence (source_instantiateTargetType w a b A t n q)

theorem native_instantiateTargetType {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateTargetTypeSentence w a b A t n q)) := ZFReplay.replay (instantiateTargetType_kernel_certificate w a b A t n q)

def instantiateSourceNaturalSentence {m} (w a b A t n q : Fin m) : Source.Sentence := ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).imp ((Formula.mem n w))).close

theorem source_instantiateSourceNatural {m} (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateSourceNaturalSentence w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiated w a b A t n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w a b A t n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.instantiate_source_natural w a b A t n q h0

theorem instantiateSourceNatural_kernel_certificate {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateSourceNaturalSentence w a b A t n q)) := TheoryTransport.sentence (source_instantiateSourceNatural w a b A t n q)

theorem native_instantiateSourceNatural {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateSourceNaturalSentence w a b A t n q)) := ZFReplay.replay (instantiateSourceNatural_kernel_certificate w a b A t n q)

def instantiateInputSentence {m} (w a b A t n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).imp ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n)))).close

theorem source_instantiateInput {m} (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateInputSentence w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiated w a b A t n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w a b A t n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.instantiate_input hZ w a b A t n q h0 h1

theorem instantiateInput_kernel_certificate {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateInputSentence w a b A t n q)) := TheoryTransport.sentence (source_instantiateInput w a b A t n q)

theorem native_instantiateInput {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateInputSentence w a b A t n q)) := ZFReplay.replay (instantiateInput_kernel_certificate w a b A t n q)

def instantiateTargetNaturalSentence {m} (w a b A t n q : Fin m) : Source.Sentence := ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).imp ((Formula.mem q w))).close

theorem source_instantiateTargetNatural {m} (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateTargetNaturalSentence w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiated w a b A t n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w a b A t n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.instantiate_target_natural w a b A t n q h0

theorem instantiateTargetNatural_kernel_certificate {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateTargetNaturalSentence w a b A t n q)) := TheoryTransport.sentence (source_instantiateTargetNatural w a b A t n q)

theorem native_instantiateTargetNatural {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateTargetNaturalSentence w a b A t n q)) := ZFReplay.replay (instantiateTargetNatural_kernel_certificate w a b A t n q)

def instantiateExistsSentence {m} (w a b A t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).imp ((SyntaxTopFormulaSyntax.instantiateExists w a b A t n)))).close

theorem source_instantiateExists {m} (w a b A t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateExistsSentence w a b A t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaExistence.instantiate_exists hZ w a b A t n h0 h1

theorem instantiateExists_kernel_certificate {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateExistsSentence w a b A t n)) := TheoryTransport.sentence (source_instantiateExists w a b A t n)

theorem native_instantiateExists {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateExistsSentence w a b A t n)) := ZFReplay.replay (instantiateExists_kernel_certificate w a b A t n)

def instantiateUniqueSentence {m} (w a b A t n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).imp ((SyntaxTopFormulaSyntax.instantiated w a b A t n v).imp ((Formula.equal q v))))).close

theorem source_instantiateUnique {m} (w a b A t n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateUniqueSentence w a b A t n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiated w a b A t n v) (Context.add (SyntaxTopFormulaSyntax.instantiated w a b A t n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w a b A t n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w a b A t n v) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaUnique.instantiate_unique hZ w a b A t n q v h0 h1 h2

theorem instantiateUnique_kernel_certificate {m} (w a b A t n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateUniqueSentence w a b A t n q v)) := TheoryTransport.sentence (source_instantiateUnique w a b A t n q v)

theorem native_instantiateUnique {m} (w a b A t n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateUniqueSentence w a b A t n q v)) := ZFReplay.replay (instantiateUnique_kernel_certificate w a b A t n q v)

def instantiateUniqueOutputSentence {m} (w a b A t n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).imp ((SyntaxTopFormulaSyntax.instantiateUnique w a b A t n q)))).close

theorem source_instantiateUniqueOutput {m} (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateUniqueOutputSentence w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiated w a b A t n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiated w a b A t n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaUnique.instantiate_unique_output hZ w a b A t n q h0 h1

theorem instantiateUniqueOutput_kernel_certificate {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateUniqueOutputSentence w a b A t n q)) := TheoryTransport.sentence (source_instantiateUniqueOutput w a b A t n q)

theorem native_instantiateUniqueOutput {m} (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateUniqueOutputSentence w a b A t n q)) := ZFReplay.replay (instantiateUniqueOutput_kernel_certificate w a b A t n q)

def instantiateFiberSentence {m} (w a b A t n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).imp ((SyntaxTopFormulaSyntax.instantiateFiber w a b A t n)))).close

theorem source_instantiateFiber {m} (w a b A t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateFiberSentence w a b A t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaFiber.instantiate_actual_fiber hZ w a b A t n h0 h1

theorem instantiateFiber_kernel_certificate {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateFiberSentence w a b A t n)) := TheoryTransport.sentence (source_instantiateFiber w a b A t n)

theorem native_instantiateFiber {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateFiberSentence w a b A t n)) := ZFReplay.replay (instantiateFiber_kernel_certificate w a b A t n)

def instantiateExistsIffSentence {m} (w a b A t n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopFormulaSyntax.instantiateExists w a b A t n).iff (SyntaxTopFormulaSyntax.instantiateInput w a b A t n)))).close

theorem source_instantiateExistsIff {m} (w a b A t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateExistsIffSentence w a b A t n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaFiber.instantiate_exists_iff hZ w a b A t n h0

theorem instantiateExistsIff_kernel_certificate {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateExistsIffSentence w a b A t n)) := TheoryTransport.sentence (source_instantiateExistsIff w a b A t n)

theorem native_instantiateExistsIff {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateExistsIffSentence w a b A t n)) := ZFReplay.replay (instantiateExistsIff_kernel_certificate w a b A t n)

def instantiateFiberIffSentence {m} (w a b A t n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopFormulaSyntax.instantiateFiber w a b A t n).iff (SyntaxTopFormulaSyntax.instantiateInput w a b A t n)))).close

theorem source_instantiateFiberIff {m} (w a b A t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateFiberIffSentence w a b A t n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaFiber.instantiate_fiber_iff hZ w a b A t n h0

theorem instantiateFiberIff_kernel_certificate {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateFiberIffSentence w a b A t n)) := TheoryTransport.sentence (source_instantiateFiberIff w a b A t n)

theorem native_instantiateFiberIff {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateFiberIffSentence w a b A t n)) := ZFReplay.replay (instantiateFiberIff_kernel_certificate w a b A t n)

def instantiateRejectInputSentence {m} (w a b A t n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).neg).imp (((SyntaxTopFormulaSyntax.instantiateExists w a b A t n).neg)))).close

theorem source_instantiateRejectInput {m} (w a b A t n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateRejectInputSentence w a b A t n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).neg) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaFiber.instantiate_reject_input hZ w a b A t n h0 h1

theorem instantiateRejectInput_kernel_certificate {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateRejectInputSentence w a b A t n)) := TheoryTransport.sentence (source_instantiateRejectInput w a b A t n)

theorem native_instantiateRejectInput {m} (w a b A t n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateRejectInputSentence w a b A t n)) := ZFReplay.replay (instantiateRejectInput_kernel_certificate w a b A t n)

def instantiateNullarySentence {m} (truth : Bool) (w a b A t n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (Formula.equal q n)))))).close

theorem source_instantiateNullary {m} (truth : Bool) (w a b A t n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateNullarySentence truth w a b A t n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaLogicalEndpoints.instantiate_nullary_iff hZ truth w a b A t n q h0 h1 h2

theorem instantiateNullary_kernel_certificate {m} (truth : Bool) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateNullarySentence truth w a b A t n q)) := TheoryTransport.sentence (source_instantiateNullary truth w a b A t n q)

theorem native_instantiateNullary {m} (truth : Bool) (w a b A t n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateNullarySentence truth w a b A t n q)) := ZFReplay.replay (instantiateNullary_kernel_certificate truth w a b A t n q)

def instantiateNegationSentence {m} (w a b A t n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (SyntaxTopFormulaSyntax.instantiated w a b A t x X))))))).close

theorem source_instantiateNegation {m} (w a b A t n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateNegationSentence w a b A t n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaLogicalEndpoints.instantiate_negation_iff hZ w a b A t n q x X h0 h1 h2 h3

theorem instantiateNegation_kernel_certificate {m} (w a b A t n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateNegationSentence w a b A t n q x X)) := TheoryTransport.sentence (source_instantiateNegation w a b A t n q x X)

theorem native_instantiateNegation {m} (w a b A t n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateNegationSentence w a b A t n q x X)) := ZFReplay.replay (instantiateNegation_kernel_certificate w a b A t n q x X)

def instantiateBinarySentence {m} (kind : Fin 4) (w a b A t n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff ((SyntaxTopFormulaSyntax.instantiated w a b A t x X).conj (SyntaxTopFormulaSyntax.instantiated w a b A t y Y)))))))).close

theorem source_instantiateBinary {m} (kind : Fin 4) (w a b A t n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateBinarySentence kind w a b A t n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaLogicalEndpoints.instantiate_binary_iff hZ kind w a b A t n q x y X Y h0 h1 h2 h3

theorem instantiateBinary_kernel_certificate {m} (kind : Fin 4) (w a b A t n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateBinarySentence kind w a b A t n q x y X Y)) := TheoryTransport.sentence (source_instantiateBinary kind w a b A t n q x y X Y)

theorem native_instantiateBinary {m} (kind : Fin 4) (w a b A t n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateBinarySentence kind w a b A t n q x y X Y)) := ZFReplay.replay (instantiateBinary_kernel_certificate kind w a b A t n q x y X Y)

def instantiateEqualSentence {m} (w a b A t n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxAtomSyntax.equalCode w X Y q).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (SyntaxTopFormulaFieldSyntax.instantiateEqual w a b A t x y X Y))))))).close

theorem source_instantiateEqual {m} (w a b A t n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateEqualSentence w a b A t n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w X Y q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxAtomSyntax.equalCode w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaSharedEndpoints.instantiate_equal_iff hZ w a b A t n q x y X Y h0 h1 h2 h3

theorem instantiateEqual_kernel_certificate {m} (w a b A t n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateEqualSentence w a b A t n q x y X Y)) := TheoryTransport.sentence (source_instantiateEqual w a b A t n q x y X Y)

theorem native_instantiateEqual {m} (w a b A t n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateEqualSentence w a b A t n q x y X Y)) := ZFReplay.replay (instantiateEqual_kernel_certificate w a b A t n q x y X Y)

def instantiateMemberSentence {m} (w a b A t n q z Z x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxAtomSyntax.memberCode w Z X Y q).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (SyntaxTopFormulaFieldSyntax.instantiateMember w a b A t z Z x y X Y))))))).close

theorem source_instantiateMember {m} (w a b A t n q z Z x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateMemberSentence w a b A t n q z Z x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w Z X Y q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxAtomSyntax.memberCode w Z X Y q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaSharedEndpoints.instantiate_member_iff hZ w a b A t n q z Z x y X Y h0 h1 h2 h3

theorem instantiateMember_kernel_certificate {m} (w a b A t n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateMemberSentence w a b A t n q z Z x y X Y)) := TheoryTransport.sentence (source_instantiateMember w a b A t n q z Z x y X Y)

theorem native_instantiateMember {m} (w a b A t n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateMemberSentence w a b A t n q z Z x y X Y)) := ZFReplay.replay (instantiateMember_kernel_certificate w a b A t n q z Z x y X Y)

def instantiateQuantifiedSentence {m} (universal : Bool) (w a b A t n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.instantiateInput w a b A t n).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q).imp (((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (SyntaxTopFormulaFieldSyntax.instantiateAdvanced w a b A t x X))))))).close

theorem source_instantiateQuantified {m} (universal : Bool) (w a b A t n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (instantiateQuantifiedSentence universal w a b A t n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.instantiateInput w a b A t n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaSharedEndpoints.instantiate_advanced_iff hZ universal w a b A t n q x X h0 h1 h2 h3

theorem instantiateQuantified_kernel_certificate {m} (universal : Bool) (w a b A t n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (instantiateQuantifiedSentence universal w a b A t n q x X)) := TheoryTransport.sentence (source_instantiateQuantified universal w a b A t n q x X)

theorem native_instantiateQuantified {m} (universal : Bool) (w a b A t n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (instantiateQuantifiedSentence universal w a b A t n q x X)) := ZFReplay.replay (instantiateQuantified_kernel_certificate universal w a b A t n q x X)

def abstractAtCodesSentence {m} (w a b A B n q R S : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a B A b n q))))).close

theorem source_abstractAtCodes {m} (w a b A B n q R S : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractAtCodesSentence w a b A B n q R S) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaCodes.abstract_at_codes hZ w a b A B n q R S h0 h1

theorem abstractAtCodes_kernel_certificate {m} (w a b A B n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractAtCodesSentence w a b A B n q R S)) := TheoryTransport.sentence (source_abstractAtCodes w a b A B n q R S)

theorem native_abstractAtCodes {m} (w a b A B n q R S : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractAtCodesSentence w a b A B n q R S)) := ZFReplay.replay (abstractAtCodes_kernel_certificate w a b A B n q R S)

def abstractEnvironmentSentence {m} (w a b A B n q : Fin m) : Source.Sentence := ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).imp ((SyntaxTopEnvironmentSyntax.abstractInput w a b A B))).close

theorem source_abstractEnvironment {m} (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractEnvironmentSentence w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.abstract_environment w a b A B n q h0

theorem abstractEnvironment_kernel_certificate {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractEnvironmentSentence w a b A B n q)) := TheoryTransport.sentence (source_abstractEnvironment w a b A B n q)

theorem native_abstractEnvironment {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractEnvironmentSentence w a b A B n q)) := ZFReplay.replay (abstractEnvironment_kernel_certificate w a b A B n q)

def abstractSourceTypeSentence {m} (w a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).imp ((FormulaCodeSyntax.formulaCode w n a B)))).close

theorem source_abstractSourceType {m} (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractSourceTypeSentence w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.abstract_source_type hZ w a b A B n q h0 h1

theorem abstractSourceType_kernel_certificate {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractSourceTypeSentence w a b A B n q)) := TheoryTransport.sentence (source_abstractSourceType w a b A B n q)

theorem native_abstractSourceType {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractSourceTypeSentence w a b A B n q)) := ZFReplay.replay (abstractSourceType_kernel_certificate w a b A B n q)

def abstractTargetTypeSentence {m} (w a b A B n q : Fin m) : Source.Sentence := ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).imp ((FormulaCodeSyntax.formulaCode w q A b))).close

theorem source_abstractTargetType {m} (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractTargetTypeSentence w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.abstract_target_type w a b A B n q h0

theorem abstractTargetType_kernel_certificate {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractTargetTypeSentence w a b A B n q)) := TheoryTransport.sentence (source_abstractTargetType w a b A B n q)

theorem native_abstractTargetType {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractTargetTypeSentence w a b A B n q)) := ZFReplay.replay (abstractTargetType_kernel_certificate w a b A B n q)

def abstractSourceNaturalSentence {m} (w a b A B n q : Fin m) : Source.Sentence := ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).imp ((Formula.mem n w))).close

theorem source_abstractSourceNatural {m} (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractSourceNaturalSentence w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.abstract_source_natural w a b A B n q h0

theorem abstractSourceNatural_kernel_certificate {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractSourceNaturalSentence w a b A B n q)) := TheoryTransport.sentence (source_abstractSourceNatural w a b A B n q)

theorem native_abstractSourceNatural {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractSourceNaturalSentence w a b A B n q)) := ZFReplay.replay (abstractSourceNatural_kernel_certificate w a b A B n q)

def abstractInputSentence {m} (w a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).imp ((SyntaxTopFormulaSyntax.abstractInput w a b A B n)))).close

theorem source_abstractInput {m} (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractInputSentence w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.abstract_input hZ w a b A B n q h0 h1

theorem abstractInput_kernel_certificate {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractInputSentence w a b A B n q)) := TheoryTransport.sentence (source_abstractInput w a b A B n q)

theorem native_abstractInput {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractInputSentence w a b A B n q)) := ZFReplay.replay (abstractInput_kernel_certificate w a b A B n q)

def abstractTargetNaturalSentence {m} (w a b A B n q : Fin m) : Source.Sentence := ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).imp ((Formula.mem q w))).close

theorem source_abstractTargetNatural {m} (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractTargetNaturalSentence w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaTyping.abstract_target_natural w a b A B n q h0

theorem abstractTargetNatural_kernel_certificate {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractTargetNaturalSentence w a b A B n q)) := TheoryTransport.sentence (source_abstractTargetNatural w a b A B n q)

theorem native_abstractTargetNatural {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractTargetNaturalSentence w a b A B n q)) := ZFReplay.replay (abstractTargetNatural_kernel_certificate w a b A B n q)

def abstractExistsSentence {m} (w a b A B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).imp ((SyntaxTopFormulaSyntax.abstractExists w a b A B n)))).close

theorem source_abstractExists {m} (w a b A B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractExistsSentence w a b A B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstractInput w a b A B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstractInput w a b A B n) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaExistence.abstract_exists hZ w a b A B n h0 h1

theorem abstractExists_kernel_certificate {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractExistsSentence w a b A B n)) := TheoryTransport.sentence (source_abstractExists w a b A B n)

theorem native_abstractExists {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractExistsSentence w a b A B n)) := ZFReplay.replay (abstractExists_kernel_certificate w a b A B n)

def abstractUniqueSentence {m} (w a b A B n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).imp ((SyntaxTopFormulaSyntax.abstracted w a b A B n v).imp ((Formula.equal q v))))).close

theorem source_abstractUnique {m} (w a b A B n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractUniqueSentence w a b A B n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n v) (Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n v) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaUnique.abstract_unique hZ w a b A B n q v h0 h1 h2

theorem abstractUnique_kernel_certificate {m} (w a b A B n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractUniqueSentence w a b A B n q v)) := TheoryTransport.sentence (source_abstractUnique w a b A B n q v)

theorem native_abstractUnique {m} (w a b A B n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractUniqueSentence w a b A B n q v)) := ZFReplay.replay (abstractUnique_kernel_certificate w a b A B n q v)

def abstractUniqueOutputSentence {m} (w a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).imp ((SyntaxTopFormulaSyntax.abstractUnique w a b A B n q)))).close

theorem source_abstractUniqueOutput {m} (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractUniqueOutputSentence w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstracted w a b A B n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstracted w a b A B n q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaUnique.abstract_unique_output hZ w a b A B n q h0 h1

theorem abstractUniqueOutput_kernel_certificate {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractUniqueOutputSentence w a b A B n q)) := TheoryTransport.sentence (source_abstractUniqueOutput w a b A B n q)

theorem native_abstractUniqueOutput {m} (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractUniqueOutputSentence w a b A B n q)) := ZFReplay.replay (abstractUniqueOutput_kernel_certificate w a b A B n q)

def abstractFiberSentence {m} (w a b A B n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).imp ((SyntaxTopFormulaSyntax.abstractFiber w a b A B n)))).close

theorem source_abstractFiber {m} (w a b A B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractFiberSentence w a b A B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTopFormulaSyntax.abstractInput w a b A B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstractInput w a b A B n) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaFiber.abstract_actual_fiber hZ w a b A B n h0 h1

theorem abstractFiber_kernel_certificate {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractFiberSentence w a b A B n)) := TheoryTransport.sentence (source_abstractFiber w a b A B n)

theorem native_abstractFiber {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractFiberSentence w a b A B n)) := ZFReplay.replay (abstractFiber_kernel_certificate w a b A B n)

def abstractExistsIffSentence {m} (w a b A B n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopFormulaSyntax.abstractExists w a b A B n).iff (SyntaxTopFormulaSyntax.abstractInput w a b A B n)))).close

theorem source_abstractExistsIff {m} (w a b A B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractExistsIffSentence w a b A B n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaFiber.abstract_exists_iff hZ w a b A B n h0

theorem abstractExistsIff_kernel_certificate {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractExistsIffSentence w a b A B n)) := TheoryTransport.sentence (source_abstractExistsIff w a b A B n)

theorem native_abstractExistsIff {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractExistsIffSentence w a b A B n)) := ZFReplay.replay (abstractExistsIff_kernel_certificate w a b A B n)

def abstractFiberIffSentence {m} (w a b A B n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopFormulaSyntax.abstractFiber w a b A B n).iff (SyntaxTopFormulaSyntax.abstractInput w a b A B n)))).close

theorem source_abstractFiberIff {m} (w a b A B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractFiberIffSentence w a b A B n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaFiber.abstract_fiber_iff hZ w a b A B n h0

theorem abstractFiberIff_kernel_certificate {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractFiberIffSentence w a b A B n)) := TheoryTransport.sentence (source_abstractFiberIff w a b A B n)

theorem native_abstractFiberIff {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractFiberIffSentence w a b A B n)) := ZFReplay.replay (abstractFiberIff_kernel_certificate w a b A B n)

def abstractRejectInputSentence {m} (w a b A B n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxTopFormulaSyntax.abstractInput w a b A B n).neg).imp (((SyntaxTopFormulaSyntax.abstractExists w a b A B n).neg)))).close

theorem source_abstractRejectInput {m} (w a b A B n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractRejectInputSentence w a b A B n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).neg) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).neg) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaFiber.abstract_reject_input hZ w a b A B n h0 h1

theorem abstractRejectInput_kernel_certificate {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractRejectInputSentence w a b A B n)) := TheoryTransport.sentence (source_abstractRejectInput w a b A B n)

theorem native_abstractRejectInput {m} (w a b A B n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractRejectInputSentence w a b A B n)) := ZFReplay.replay (abstractRejectInput_kernel_certificate w a b A B n)

def abstractNullarySentence {m} (truth : Bool) (w a b A B n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (Formula.equal q n)))))).close

theorem source_abstractNullary {m} (truth : Bool) (w a b A B n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractNullarySentence truth w a b A B n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (SyntaxTopFormulaSyntax.abstractInput w a b A B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstractInput w a b A B n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaLogicalEndpoints.abstract_nullary_iff hZ truth w a b A B n q h0 h1 h2

theorem abstractNullary_kernel_certificate {m} (truth : Bool) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractNullarySentence truth w a b A B n q)) := TheoryTransport.sentence (source_abstractNullary truth w a b A B n q)

theorem native_abstractNullary {m} (truth : Bool) (w a b A B n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractNullarySentence truth w a b A B n q)) := ZFReplay.replay (abstractNullary_kernel_certificate truth w a b A B n q)

def abstractNegationSentence {m} (w a b A B n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (SyntaxTopFormulaSyntax.abstracted w a b A B x X))))))).close

theorem source_abstractNegation {m} (w a b A B n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractNegationSentence w a b A B n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxTopFormulaSyntax.abstractInput w a b A B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstractInput w a b A B n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaLogicalEndpoints.abstract_negation_iff hZ w a b A B n q x X h0 h1 h2 h3

theorem abstractNegation_kernel_certificate {m} (w a b A B n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractNegationSentence w a b A B n q x X)) := TheoryTransport.sentence (source_abstractNegation w a b A B n q x X)

theorem native_abstractNegation {m} (w a b A B n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractNegationSentence w a b A B n q x X)) := ZFReplay.replay (abstractNegation_kernel_certificate w a b A B n q x X)

def abstractBinarySentence {m} (kind : Fin 4) (w a b A B n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff ((SyntaxTopFormulaSyntax.abstracted w a b A B x X).conj (SyntaxTopFormulaSyntax.abstracted w a b A B y Y)))))))).close

theorem source_abstractBinary {m} (kind : Fin 4) (w a b A B n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractBinarySentence kind w a b A B n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxTopFormulaSyntax.abstractInput w a b A B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstractInput w a b A B n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaLogicalEndpoints.abstract_binary_iff hZ kind w a b A B n q x y X Y h0 h1 h2 h3

theorem abstractBinary_kernel_certificate {m} (kind : Fin 4) (w a b A B n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractBinarySentence kind w a b A B n q x y X Y)) := TheoryTransport.sentence (source_abstractBinary kind w a b A B n q x y X Y)

theorem native_abstractBinary {m} (kind : Fin 4) (w a b A B n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractBinarySentence kind w a b A B n q x y X Y)) := ZFReplay.replay (abstractBinary_kernel_certificate kind w a b A B n q x y X Y)

def abstractEqualSentence {m} (w a b A B n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxAtomSyntax.equalCode w X Y q).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (SyntaxTopFormulaFieldSyntax.abstractEqual w a b A B x y X Y))))))).close

theorem source_abstractEqual {m} (w a b A B n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractEqualSentence w a b A B n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w X Y q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxTopFormulaSyntax.abstractInput w a b A B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstractInput w a b A B n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxAtomSyntax.equalCode w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaSharedEndpoints.abstract_equal_iff hZ w a b A B n q x y X Y h0 h1 h2 h3

theorem abstractEqual_kernel_certificate {m} (w a b A B n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractEqualSentence w a b A B n q x y X Y)) := TheoryTransport.sentence (source_abstractEqual w a b A B n q x y X Y)

theorem native_abstractEqual {m} (w a b A B n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractEqualSentence w a b A B n q x y X Y)) := ZFReplay.replay (abstractEqual_kernel_certificate w a b A B n q x y X Y)

def abstractMemberSentence {m} (w a b A B n q z Z x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxAtomSyntax.memberCode w Z X Y q).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (SyntaxTopFormulaFieldSyntax.abstractMember w a b A B z Z x y X Y))))))).close

theorem source_abstractMember {m} (w a b A B n q z Z x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractMemberSentence w a b A B n q z Z x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w Z X Y q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxTopFormulaSyntax.abstractInput w a b A B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstractInput w a b A B n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxAtomSyntax.memberCode w Z X Y q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaSharedEndpoints.abstract_member_iff hZ w a b A B n q z Z x y X Y h0 h1 h2 h3

theorem abstractMember_kernel_certificate {m} (w a b A B n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractMemberSentence w a b A B n q z Z x y X Y)) := TheoryTransport.sentence (source_abstractMember w a b A B n q z Z x y X Y)

theorem native_abstractMember {m} (w a b A B n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractMemberSentence w a b A B n q z Z x y X Y)) := ZFReplay.replay (abstractMember_kernel_certificate w a b A B n q z Z x y X Y)

def abstractQuantifiedSentence {m} (universal : Bool) (w a b A B n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxTopFormulaSyntax.abstractInput w a b A B n).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q).imp (((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (SyntaxTopFormulaFieldSyntax.abstractAdvanced w a b A B x X))))))).close

theorem source_abstractQuantified {m} (universal : Bool) (w a b A B n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (abstractQuantifiedSentence universal w a b A B n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (SyntaxTopFormulaSyntax.abstractInput w a b A B n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxTopFormulaSyntax.abstractInput w a b A B n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) := .hyp (Or.inl rfl)
  exact SyntaxTopFormulaSharedEndpoints.abstract_advanced_iff hZ universal w a b A B n q x X h0 h1 h2 h3

theorem abstractQuantified_kernel_certificate {m} (universal : Bool) (w a b A B n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (abstractQuantifiedSentence universal w a b A B n q x X)) := TheoryTransport.sentence (source_abstractQuantified universal w a b A B n q x X)

theorem native_abstractQuantified {m} (universal : Bool) (w a b A B n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (abstractQuantifiedSentence universal w a b A B n q x X)) := ZFReplay.replay (abstractQuantified_kernel_certificate universal w a b A B n q x X)

end PPAC.Migration.Internal.ObjectTopFormula
