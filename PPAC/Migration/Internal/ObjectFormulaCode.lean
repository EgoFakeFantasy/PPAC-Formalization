import PPAC.Migration.Internal.FormulaCodeUnknownTag

/-! 无额外载体FormulaCode及全11已知原构造的原nativeZF完整闭句证书。 -/
namespace PPAC.Migration.Internal.ObjectFormulaCode
open Source SourceAlgebra SourceLogic OmegaSyntax PowerSetSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax SyntaxTypeJudgmentSyntax
open SyntaxLogicalSyntax (singleCode binaryCode quantifierTag)
open FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeBranchSyntax

def carrierExistsSentence {m} (w : Fin m) : Source.Sentence := ((existsCarrier w)).close

theorem source_carrierExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (carrierExistsSentence w) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  have hZ : ZFContext.Evidence Δ := by
    exact ZFContext.source_ZF m
  exact FormulaCodeCarrier.exists_carrier hZ w

theorem carrierExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (carrierExistsSentence w)) := TheoryTransport.sentence (source_carrierExists w)

theorem native_carrierExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (carrierExistsSentence w)) := ZFReplay.replay (carrierExists_kernel_certificate w)

def carrierUniqueSentence {m} (w a c d t : Fin m) : Source.Sentence := ((carrier w a c).imp ((carrier w d t).imp (((Formula.equal a d).conj (.equal c t))))).close

theorem source_carrierUnique {m} (w a c d t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (carrierUniqueSentence w a c d t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (carrier w d t) (Context.add (carrier w a c) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (carrier w a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (carrier w d t) := .hyp (Or.inl rfl)
  exact FormulaCodeCarrier.unique hZ w a c d t h0 h1

theorem carrierUnique_kernel_certificate {m} (w a c d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (carrierUniqueSentence w a c d t)) := TheoryTransport.sentence (source_carrierUnique w a c d t)

theorem native_carrierUnique {m} (w a c d t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (carrierUniqueSentence w a c d t)) := ZFReplay.replay (carrierUnique_kernel_certificate w a c d t)

def atCarrierSentence {m} (w a c n b f : Fin m) : Source.Sentence := ((carrier w a c).imp (((formulaCode w n b f).iff (typed w c n b f)))).close

theorem source_atCarrier {m} (w a c n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atCarrierSentence w a c n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (carrier w a c) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (carrier w a c) := .hyp (Or.inl rfl)
  exact FormulaCodeCarrier.code_iff_typed hZ w a c n b f h0

theorem atCarrier_kernel_certificate {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atCarrierSentence w a c n b f)) := TheoryTransport.sentence (source_atCarrier w a c n b f)

theorem native_atCarrier {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atCarrierSentence w a c n b f)) := ZFReplay.replay (atCarrier_kernel_certificate w a c n b f)

def guardsSentence {m} (w n b f : Fin m) : Source.Sentence := ((formulaCode w n b f).imp (((Formula.mem n w).conj (contexts w b f)))).close

theorem source_guards {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (guardsSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeProperties.guards w n b f h0

theorem guards_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (guardsSentence w n b f)) := TheoryTransport.sentence (source_guards w n b f)

theorem native_guards {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (guardsSentence w n b f)) := ZFReplay.replay (guards_kernel_certificate w n b f)

def rejectCodeSentence {m} (w n b f : Fin m) : Source.Sentence := (((Formula.mem n w).neg).imp (((formulaCode w n b f).neg))).close

theorem source_rejectCode {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectCodeSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n w).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inl rfl)
  exact FormulaCodeProperties.reject_code w n b f h0

theorem rejectCode_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectCodeSentence w n b f)) := TheoryTransport.sentence (source_rejectCode w n b f)

theorem native_rejectCode {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectCodeSentence w n b f)) := ZFReplay.replay (rejectCode_kernel_certificate w n b f)

def rejectContextSentence {m} (w n b f : Fin m) : Source.Sentence := (((contexts w b f).neg).imp (((formulaCode w n b f).neg))).close

theorem source_rejectContext {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectContextSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((contexts w b f).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((contexts w b f).neg) := .hyp (Or.inl rfl)
  exact FormulaCodeProperties.reject_context w n b f h0

theorem rejectContext_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectContextSentence w n b f)) := TheoryTransport.sentence (source_rejectContext w n b f)

theorem native_rejectContext {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectContextSentence w n b f)) := ZFReplay.replay (rejectContext_kernel_certificate w n b f)

def omegaIndependentSentence {m} (w v n b f : Fin m) : Source.Sentence := ((omega w).imp ((omega v).imp (((formulaCode w n b f).iff (formulaCode v n b f))))).close

theorem source_omegaIndependent {m} (w v n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (omegaIndependentSentence w v n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (omega v) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (omega v) := .hyp (Or.inl rfl)
  exact FormulaCodeProperties.omega_independent hZ w v n b f h0 h1

theorem omegaIndependent_kernel_certificate {m} (w v n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (omegaIndependentSentence w v n b f)) := TheoryTransport.sentence (source_omegaIndependent w v n b f)

theorem native_omegaIndependent {m} (w v n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (omegaIndependentSentence w v n b f)) := ZFReplay.replay (omegaIndependent_kernel_certificate w v n b f)

def rootTransportSentence {m} (w n b f t : Fin m) : Source.Sentence := ((Formula.equal n t).imp ((formulaCode w n b f).imp ((formulaCode w t b f)))).close

theorem source_rootTransport {m} (w n b f t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rootTransportSentence w n b f t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Context.add (Formula.equal n t) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (Formula.equal n t) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTransport.code_root w n b f t h0 h1

theorem rootTransport_kernel_certificate {m} (w n b f t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rootTransportSentence w n b f t)) := TheoryTransport.sentence (source_rootTransport w n b f t)

theorem native_rootTransport {m} (w n b f t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rootTransportSentence w n b f t)) := ZFReplay.replay (rootTransport_kernel_certificate w n b f t)

def boundTransportSentence {m} (w n b f t : Fin m) : Source.Sentence := ((Formula.equal b t).imp ((formulaCode w n b f).imp ((formulaCode w n t f)))).close

theorem source_boundTransport {m} (w n b f t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundTransportSentence w n b f t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Context.add (Formula.equal b t) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (Formula.equal b t) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTransport.code_bound w n b f t h0 h1

theorem boundTransport_kernel_certificate {m} (w n b f t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundTransportSentence w n b f t)) := TheoryTransport.sentence (source_boundTransport w n b f t)

theorem native_boundTransport {m} (w n b f t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundTransportSentence w n b f t)) := ZFReplay.replay (boundTransport_kernel_certificate w n b f t)

def freeTransportSentence {m} (w n b f t : Fin m) : Source.Sentence := ((Formula.equal f t).imp ((formulaCode w n b f).imp ((formulaCode w n b t)))).close

theorem source_freeTransport {m} (w n b f t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeTransportSentence w n b f t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Context.add (Formula.equal f t) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (Formula.equal f t) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTransport.code_free w n b f t h0 h1

theorem freeTransport_kernel_certificate {m} (w n b f t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeTransportSentence w n b f t)) := TheoryTransport.sentence (source_freeTransport w n b f t)

theorem native_freeTransport {m} (w n b f t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeTransportSentence w n b f t)) := ZFReplay.replay (freeTransport_kernel_certificate w n b f t)

def omegaTransportSentence {m} (w n b f t : Fin m) : Source.Sentence := ((Formula.equal w t).imp ((formulaCode w n b f).imp ((formulaCode t n b f)))).close

theorem source_omegaTransport {m} (w n b f t : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (omegaTransportSentence w n b f t) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (formulaCode w n b f) (Context.add (Formula.equal w t) (Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (Formula.equal w t) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (formulaCode w n b f) := .hyp (Or.inl rfl)
  exact FormulaCodeTransport.code_omega w n b f t h0 h1

theorem omegaTransport_kernel_certificate {m} (w n b f t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (omegaTransportSentence w n b f t)) := TheoryTransport.sentence (source_omegaTransport w n b f t)

theorem native_omegaTransport {m} (w n b f t : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (omegaTransportSentence w n b f t)) := ZFReplay.replay (omegaTransport_kernel_certificate w n b f t)

def advancedTransferSentence {m} (w a c x b f : Fin m) : Source.Sentence := ((carrier w a c).imp (((SyntaxTypeRecursiveSyntax.advancedTyped w c x b f).iff (advancedCode w x b f)))).close

theorem source_advancedTransfer {m} (w a c x b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedTransferSentence w a c x b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (carrier w a c) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (carrier w a c) := .hyp (Or.inl rfl)
  exact FormulaCodeCriterionTransfer.advanced_iff hZ w a c x b f h0

theorem advancedTransfer_kernel_certificate {m} (w a c x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedTransferSentence w a c x b f)) := TheoryTransport.sentence (source_advancedTransfer w a c x b f)

theorem native_advancedTransfer {m} (w a c x b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedTransferSentence w a c x b f)) := ZFReplay.replay (advancedTransfer_kernel_certificate w a c x b f)

def singleTransferSentence {m} (tag : Nat) (advance : Bool) (w a c b f n : Fin m) : Source.Sentence := ((carrier w a c).imp (((SyntaxTypeRecursiveSyntax.singleCase tag advance w c b f n).iff (singleCase tag advance w b f n)))).close

theorem source_singleTransfer {m} (tag : Nat) (advance : Bool) (w a c b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleTransferSentence tag advance w a c b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (carrier w a c) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (carrier w a c) := .hyp (Or.inl rfl)
  exact FormulaCodeCriterionTransfer.single_iff hZ tag advance w a c b f n h0

theorem singleTransfer_kernel_certificate {m} (tag : Nat) (advance : Bool) (w a c b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleTransferSentence tag advance w a c b f n)) := TheoryTransport.sentence (source_singleTransfer tag advance w a c b f n)

theorem native_singleTransfer {m} (tag : Nat) (advance : Bool) (w a c b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleTransferSentence tag advance w a c b f n)) := ZFReplay.replay (singleTransfer_kernel_certificate tag advance w a c b f n)

def binaryTransferSentence {m} (kind : Fin 4) (w a c b f n : Fin m) : Source.Sentence := ((carrier w a c).imp (((SyntaxTypeRecursiveSyntax.binaryCase kind w c b f n).iff (binaryCase kind w b f n)))).close

theorem source_binaryTransfer {m} (kind : Fin 4) (w a c b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryTransferSentence kind w a c b f n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (carrier w a c) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (carrier w a c) := .hyp (Or.inl rfl)
  exact FormulaCodeCriterionTransfer.binary_iff hZ kind w a c b f n h0

theorem binaryTransfer_kernel_certificate {m} (kind : Fin 4) (w a c b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryTransferSentence kind w a c b f n)) := TheoryTransport.sentence (source_binaryTransfer kind w a c b f n)

theorem native_binaryTransfer {m} (kind : Fin 4) (w a c b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryTransferSentence kind w a c b f n)) := ZFReplay.replay (binaryTransfer_kernel_certificate kind w a c b f n)

def criterionTransferSentence {m} (w a c n b f : Fin m) : Source.Sentence := ((carrier w a c).imp (((SyntaxTypeRecursiveSyntax.criterion w c n b f).iff (criterion w n b f)))).close

theorem source_criterionTransfer {m} (w a c n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (criterionTransferSentence w a c n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (carrier w a c) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (carrier w a c) := .hyp (Or.inl rfl)
  exact FormulaCodeCriterionTransfer.criterion_iff hZ w a c n b f h0

theorem criterionTransfer_kernel_certificate {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (criterionTransferSentence w a c n b f)) := TheoryTransport.sentence (source_criterionTransfer w a c n b f)

theorem native_criterionTransfer {m} (w a c n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (criterionTransferSentence w a c n b f)) := ZFReplay.replay (criterionTransfer_kernel_certificate w a c n b f)

def recursiveSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp (((formulaCode w n b f).iff (criterion w n b f)))).close

theorem source_recursive {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursiveSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaCodeRecursive.recursive_iff hZ w n b f h0

theorem recursive_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursiveSentence w n b f)) := TheoryTransport.sentence (source_recursive w n b f)

theorem native_recursive {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursiveSentence w n b f)) := ZFReplay.replay (recursive_kernel_certificate w n b f)

def universalSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((FormulaCodeRecursive.universalLaw w))).close

theorem source_universal {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (universalSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact FormulaCodeRecursive.all_law hZ w h0

theorem universal_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (universalSentence w)) := TheoryTransport.sentence (source_universal w)

theorem native_universal {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (universalSentence w)) := ZFReplay.replay (universal_kernel_certificate w)

def nullaryTypesSentence {m} (truth : Bool) (w b f n : Fin m) : Source.Sentence := ((omega w).imp ((constructor 0 (nullaryTag truth) w Fin.elim0 n).imp (((formulaCode w n b f).iff (contexts w b f))))).close

theorem source_nullaryTypes {m} (truth : Bool) (w b f n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryTypesSentence truth w b f n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (constructor 0 (nullaryTag truth) w Fin.elim0 n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (constructor 0 (nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownAtomic.nullary_iff hZ truth w b f n h0 h1

theorem nullaryTypes_kernel_certificate {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryTypesSentence truth w b f n)) := TheoryTransport.sentence (source_nullaryTypes truth w b f n)

theorem native_nullaryTypes {m} (truth : Bool) (w b f n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryTypesSentence truth w b f n)) := ZFReplay.replay (nullaryTypes_kernel_certificate truth w b f n)

def memberTypesSentence {m} (w b f s x y n : Fin m) : Source.Sentence := ((omega w).imp ((memberCode w s x y n).imp (((formulaCode w n b f).iff (memberTypes w b f s x y))))).close

theorem source_memberTypes {m} (w b f s x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (memberTypesSentence w b f s x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (memberCode w s x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (memberCode w s x y n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownAtomic.member_iff hZ w b f s x y n h0 h1

theorem memberTypes_kernel_certificate {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (memberTypesSentence w b f s x y n)) := TheoryTransport.sentence (source_memberTypes w b f s x y n)

theorem native_memberTypes {m} (w b f s x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (memberTypesSentence w b f s x y n)) := ZFReplay.replay (memberTypes_kernel_certificate w b f s x y n)

def equalTypesSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((equalCode w x y n).imp (((formulaCode w n b f).iff (equalTypes w b f x y))))).close

theorem source_equalTypes {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalTypesSentence w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (equalCode w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (equalCode w x y n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownAtomic.equal_iff hZ w b f x y n h0 h1

theorem equalTypes_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalTypesSentence w b f x y n)) := TheoryTransport.sentence (source_equalTypes w b f x y n)

theorem native_equalTypes {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalTypesSentence w b f x y n)) := ZFReplay.replay (equalTypes_kernel_certificate w b f x y n)

def negationTypesSentence {m} (w b f x n : Fin m) : Source.Sentence := ((omega w).imp ((singleCode 4 w x n).imp (((formulaCode w n b f).iff (singleTypes false w b f x))))).close

theorem source_negationTypes {m} (w b f x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationTypesSentence w b f x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCode 4 w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleCode 4 w x n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownLogical.negation_iff hZ w b f x n h0 h1

theorem negationTypes_kernel_certificate {m} (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationTypesSentence w b f x n)) := TheoryTransport.sentence (source_negationTypes w b f x n)

theorem native_negationTypes {m} (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationTypesSentence w b f x n)) := ZFReplay.replay (negationTypes_kernel_certificate w b f x n)

def binary0TypesSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode 0 w x y n).imp (((formulaCode w n b f).iff (binaryTypes w b f x y))))).close

theorem source_binary0Types {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary0TypesSentence w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCode 0 w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryCode 0 w x y n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownLogical.binary0_iff hZ w b f x y n h0 h1

theorem binary0Types_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary0TypesSentence w b f x y n)) := TheoryTransport.sentence (source_binary0Types w b f x y n)

theorem native_binary0Types {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary0TypesSentence w b f x y n)) := ZFReplay.replay (binary0Types_kernel_certificate w b f x y n)

def binary1TypesSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode 1 w x y n).imp (((formulaCode w n b f).iff (binaryTypes w b f x y))))).close

theorem source_binary1Types {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary1TypesSentence w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCode 1 w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryCode 1 w x y n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownLogical.binary1_iff hZ w b f x y n h0 h1

theorem binary1Types_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary1TypesSentence w b f x y n)) := TheoryTransport.sentence (source_binary1Types w b f x y n)

theorem native_binary1Types {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary1TypesSentence w b f x y n)) := ZFReplay.replay (binary1Types_kernel_certificate w b f x y n)

def binary2TypesSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode 2 w x y n).imp (((formulaCode w n b f).iff (binaryTypes w b f x y))))).close

theorem source_binary2Types {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary2TypesSentence w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCode 2 w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryCode 2 w x y n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownLogical.binary2_iff hZ w b f x y n h0 h1

theorem binary2Types_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary2TypesSentence w b f x y n)) := TheoryTransport.sentence (source_binary2Types w b f x y n)

theorem native_binary2Types {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary2TypesSentence w b f x y n)) := ZFReplay.replay (binary2Types_kernel_certificate w b f x y n)

def binary3TypesSentence {m} (w b f x y n : Fin m) : Source.Sentence := ((omega w).imp ((binaryCode 3 w x y n).imp (((formulaCode w n b f).iff (binaryTypes w b f x y))))).close

theorem source_binary3Types {m} (w b f x y n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binary3TypesSentence w b f x y n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (binaryCode 3 w x y n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (binaryCode 3 w x y n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownLogical.binary3_iff hZ w b f x y n h0 h1

theorem binary3Types_kernel_certificate {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binary3TypesSentence w b f x y n)) := TheoryTransport.sentence (source_binary3Types w b f x y n)

theorem native_binary3Types {m} (w b f x y n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binary3TypesSentence w b f x y n)) := ZFReplay.replay (binary3Types_kernel_certificate w b f x y n)

def forallTypesSentence {m} (w b f x n : Fin m) : Source.Sentence := ((omega w).imp ((singleCode 9 w x n).imp (((formulaCode w n b f).iff (singleTypes true w b f x))))).close

theorem source_forallTypes {m} (w b f x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallTypesSentence w b f x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCode 9 w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleCode 9 w x n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownLogical.forall_iff hZ w b f x n h0 h1

theorem forallTypes_kernel_certificate {m} (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallTypesSentence w b f x n)) := TheoryTransport.sentence (source_forallTypes w b f x n)

theorem native_forallTypes {m} (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallTypesSentence w b f x n)) := ZFReplay.replay (forallTypes_kernel_certificate w b f x n)

def existsTypesSentence {m} (w b f x n : Fin m) : Source.Sentence := ((omega w).imp ((singleCode 10 w x n).imp (((formulaCode w n b f).iff (singleTypes true w b f x))))).close

theorem source_existsTypes {m} (w b f x n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsTypesSentence w b f x n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (singleCode 10 w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (singleCode 10 w x n) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownLogical.exists_iff hZ w b f x n h0 h1

theorem existsTypes_kernel_certificate {m} (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsTypesSentence w b f x n)) := TheoryTransport.sentence (source_existsTypes w b f x n)

theorem native_existsTypes {m} (w b f x n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsTypesSentence w b f x n)) := ZFReplay.replay (existsTypes_kernel_certificate w b f x n)

def quantifierTypesSentence {m} (universal : Bool) (w b f x n k : Fin m) : Source.Sentence := ((omega w).imp ((singleCode (quantifierTag universal) w x n).imp ((successor k b).imp (((formulaCode w n b f).iff ((contexts w b f).conj (formulaCode w x k f))))))).close

theorem source_quantifierTypes {m} (universal : Bool) (w b f x n k : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifierTypesSentence universal w b f x n k) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor k b) (Context.add (singleCode (quantifierTag universal) w x n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (singleCode (quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor k b) := .hyp (Or.inl rfl)
  exact FormulaCodeKnownLogical.quantified_iff hZ universal w b f x n k h0 h1 h2

theorem quantifierTypes_kernel_certificate {m} (universal : Bool) (w b f x n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifierTypesSentence universal w b f x n k)) := TheoryTransport.sentence (source_quantifierTypes universal w b f x n k)

theorem native_quantifierTypes {m} (universal : Bool) (w b f x n k : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifierTypesSentence universal w b f x n k)) := ZFReplay.replay (quantifierTypes_kernel_certificate universal w b f x n k)

def unknownTagSentence {m} (w b f t p n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem t w).imp ((Formula.mem p w).imp ((FormulaCodeUnknownTag.unknownTags 11 t).imp ((StructuralNodeSyntax.raw w t p n).imp (((formulaCode w n b f).neg))))))).close

theorem source_unknownTag {m} (w b f t p n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (unknownTagSentence w b f t p n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (StructuralNodeSyntax.raw w t p n) (Context.add (FormulaCodeUnknownTag.unknownTags 11 t) (Context.add (Formula.mem p w) (Context.add (Formula.mem t w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem t w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (FormulaCodeUnknownTag.unknownTags 11 t) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (StructuralNodeSyntax.raw w t p n) := .hyp (Or.inl rfl)
  exact FormulaCodeUnknownTag.reject hZ w b f t p n h0 h1 h2 h3 h4

theorem unknownTag_kernel_certificate {m} (w b f t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (unknownTagSentence w b f t p n)) := TheoryTransport.sentence (source_unknownTag w b f t p n)

theorem native_unknownTag {m} (w b f t p n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (unknownTagSentence w b f t p n)) := ZFReplay.replay (unknownTag_kernel_certificate w b f t p n)

end PPAC.Migration.Internal.ObjectFormulaCode
