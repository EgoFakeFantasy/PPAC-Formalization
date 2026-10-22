import PPAC.Migration.Internal.SyntaxRenameSystem

/-! 纯对象RenameFormula判断、实际前段查询与全11类递归定律的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxRenameRecursive
open Source SourceAlgebra SourceLogic OmegaSyntax

def introSentence {m} (w r s a b c d n q v : Fin m) : Source.Sentence := ((Formula.mem n w).imp ((SyntaxRenameEvaluationSyntax.evaluation w n v).imp ((SyntaxRenameQuerySyntax.contains w v r s a b c d q).imp ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q))))).close

theorem source_intro {m} (w r s a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (introSentence w r s a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameQuerySyntax.contains w v r s a b c d q) (Context.add (SyntaxRenameEvaluationSyntax.evaluation w n v) (Context.add (Formula.mem n w) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameEvaluationSyntax.evaluation w n v) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameQuerySyntax.contains w v r s a b c d q) := .hyp (Or.inl rfl)
  exact SyntaxRenameJudgmentSyntax.intro_renamed w r s a b c d n q v h0 h1 h2

theorem intro_kernel_certificate {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (introSentence w r s a b c d n q v)) := TheoryTransport.sentence (source_intro w r s a b c d n q v)

theorem native_intro {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (introSentence w r s a b c d n q v)) := ZFReplay.replay (intro_kernel_certificate w r s a b c d n q v)

def rejectCodeSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := (((Formula.mem n w).neg).imp (((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).neg))).close

theorem source_rejectCode {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectCodeSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add ((Formula.mem n w).neg) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ ((Formula.mem n w).neg) := .hyp (Or.inl rfl)
  exact SyntaxRenameJudgmentSyntax.reject_code w r s a b c d n q h0

theorem rejectCode_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectCodeSentence w r s a b c d n q)) := TheoryTransport.sentence (source_rejectCode w r s a b c d n q)

theorem native_rejectCode {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectCodeSentence w r s a b c d n q)) := ZFReplay.replay (rejectCode_kernel_certificate w r s a b c d n q)

def legalSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).imp ((SyntaxRenameStateSyntax.legal w r s a b c d q))).close

theorem source_legal {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (legalSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameJudgment.legal w r s a b c d n q h0

theorem legal_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (legalSentence w r s a b c d n q)) := TheoryTransport.sentence (source_legal w r s a b c d n q)

theorem native_legal {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (legalSentence w r s a b c d n q)) := ZFReplay.replay (legal_kernel_certificate w r s a b c d n q)

def targetTypeSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).imp ((FormulaCodeSyntax.formulaCode w q c d))).close

theorem source_targetType {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetTypeSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameJudgment.target_type w r s a b c d n q h0

theorem targetType_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetTypeSentence w r s a b c d n q)) := TheoryTransport.sentence (source_targetType w r s a b c d n q)

theorem native_targetType {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetTypeSentence w r s a b c d n q)) := ZFReplay.replay (targetType_kernel_certificate w r s a b c d n q)

def containsCriterionSentence {m} (w n h v r s a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOperatorSyntax.value w n h v).imp (((SyntaxRenameQuerySyntax.contains w v r s a b c d q).iff ((SyntaxRenameStateSyntax.legal w r s a b c d q).conj (SyntaxRenameLocalSyntax.content w r s a b c d h n q)))))).close

theorem source_containsCriterion {m} (w n h v r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (containsCriterionSentence w n h v r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOperatorSyntax.value w n h v) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameOperatorSyntax.value w n h v) := .hyp (Or.inl rfl)
  exact SyntaxRenameJudgmentState.contains_iff hZ w n h v r s a b c d q h0 h1

theorem containsCriterion_kernel_certificate {m} (w n h v r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (containsCriterionSentence w n h v r s a b c d q)) := TheoryTransport.sentence (source_containsCriterion w n h v r s a b c d q)

theorem native_containsCriterion {m} (w n h v r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (containsCriterionSentence w n h v r s a b c d q)) := ZFReplay.replay (containsCriterion_kernel_certificate w n h v r s a b c d q)

def atValueSentence {m} (w r s a b c d n q v : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameEvaluationSyntax.evaluation w n v).imp (((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).iff (SyntaxRenameQuerySyntax.contains w v r s a b c d q))))).close

theorem source_atValue {m} (w r s a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atValueSentence w r s a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameEvaluationSyntax.evaluation w n v) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameEvaluationSyntax.evaluation w n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameJudgment.at_value hZ w r s a b c d n q v h0 h1

theorem atValue_kernel_certificate {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atValueSentence w r s a b c d n q v)) := TheoryTransport.sentence (source_atValue w r s a b c d n q v)

theorem native_atValue {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atValueSentence w r s a b c d n q v)) := ZFReplay.replay (atValue_kernel_certificate w r s a b c d n q v)

def readSentence {m} (w h D x r s a b c d q : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal D).imp ((Formula.mem x D).imp ((SyntaxRenameRecursionSyntax.graph w h D).imp (((SyntaxRenameQuerySyntax.read w h x r s a b c d q).iff (SyntaxRenameJudgmentSyntax.renamed w r s a b c d x q)))))).close

theorem source_read {m} (w h D x r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (readSentence w h D x r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w h D) (Context.add (Formula.mem x D) (Context.add (OrdinalSyntax.ordinal D) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal D) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x D) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameRecursionSyntax.graph w h D) := .hyp (Or.inl rfl)
  exact SyntaxRenameJudgment.read_iff hZ w h D x r s a b c d q h0 h1 h2

theorem read_kernel_certificate {m} (w h D x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (readSentence w h D x r s a b c d q)) := TheoryTransport.sentence (source_read w h D x r s a b c d q)

theorem native_read {m} (w h D x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (readSentence w h D x r s a b c d q)) := ZFReplay.replay (read_kernel_certificate w h D x r s a b c d q)

def advancedSentence {m} (w h D x r s a b c d q : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal D).imp ((Formula.mem x D).imp ((SyntaxRenameRecursionSyntax.graph w h D).imp (((SyntaxRenameQuerySyntax.advanced w h x r s a b c d q).iff (SyntaxRenameRecursiveSyntax.advanced w x r s a b c d q)))))).close

theorem source_advanced {m} (w h D x r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedSentence w h D x r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w h D) (Context.add (Formula.mem x D) (Context.add (OrdinalSyntax.ordinal D) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal D) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x D) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameRecursionSyntax.graph w h D) := .hyp (Or.inl rfl)
  exact SyntaxRenameReadTransfer.advanced_iff hZ w h D x r s a b c d q h0 h1 h2

theorem advanced_kernel_certificate {m} (w h D x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedSentence w h D x r s a b c d q)) := TheoryTransport.sentence (source_advanced w h D x r s a b c d q)

theorem native_advanced {m} (w h D x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedSentence w h D x r s a b c d q)) := ZFReplay.replay (advanced_kernel_certificate w h D x r s a b c d q)

def checkSentence {m} (advance : Bool) (w h D x r s a b c d q : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal D).imp ((Formula.mem x D).imp ((SyntaxRenameRecursionSyntax.graph w h D).imp (((SyntaxRenameLogicalSyntax.check advance w h x r s a b c d q).iff (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q)))))).close

theorem source_check {m} (advance : Bool) (w h D x r s a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkSentence advance w h D x r s a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w h D) (Context.add (Formula.mem x D) (Context.add (OrdinalSyntax.ordinal D) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal D) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem x D) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameRecursionSyntax.graph w h D) := .hyp (Or.inl rfl)
  exact SyntaxRenameReadTransfer.check_iff hZ advance w h D x r s a b c d q h0 h1 h2

theorem check_kernel_certificate {m} (advance : Bool) (w h D x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkSentence advance w h D x r s a b c d q)) := TheoryTransport.sentence (source_check advance w h D x r s a b c d q)

theorem native_check {m} (advance : Bool) (w h D x r s a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkSentence advance w h D x r s a b c d q)) := ZFReplay.replay (check_kernel_certificate advance w h D x r s a b c d q)

def singleFieldsSentence {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q x X : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameRecursionSyntax.graph w h n).imp (((SyntaxRenameLogicalSyntax.singleData tag advance w h r s a b c d n q x X).iff (SyntaxRenameRecursiveSyntax.singleData tag advance w r s a b c d n q x X))))).close

theorem source_singleFields {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleFieldsSentence tag advance w h r s a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact SyntaxRenameFieldsTransfer.single_iff hZ tag advance w h r s a b c d n q x X h0 h1

theorem singleFields_kernel_certificate {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleFieldsSentence tag advance w h r s a b c d n q x X)) := TheoryTransport.sentence (source_singleFields tag advance w h r s a b c d n q x X)

theorem native_singleFields {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleFieldsSentence tag advance w h r s a b c d n q x X)) := ZFReplay.replay (singleFields_kernel_certificate tag advance w h r s a b c d n q x X)

def singleCaseSentence {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameRecursionSyntax.graph w h n).imp (((SyntaxRenameLogicalSyntax.single tag advance w h r s a b c d n q).iff (SyntaxRenameRecursiveSyntax.single tag advance w r s a b c d n q))))).close

theorem source_singleCase {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleCaseSentence tag advance w h r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact SyntaxRenameCaseTransfer.single_iff hZ tag advance w h r s a b c d n q h0 h1

theorem singleCase_kernel_certificate {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleCaseSentence tag advance w h r s a b c d n q)) := TheoryTransport.sentence (source_singleCase tag advance w h r s a b c d n q)

theorem native_singleCase {m} (tag : Nat) (advance : Bool) (w h r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleCaseSentence tag advance w h r s a b c d n q)) := ZFReplay.replay (singleCase_kernel_certificate tag advance w h r s a b c d n q)

def binaryFieldsSentence {m} (kind : Fin 4) (w h r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameRecursionSyntax.graph w h n).imp (((SyntaxRenameLogicalSyntax.binaryData kind w h r s a b c d n q x y X Y).iff (SyntaxRenameRecursiveSyntax.binaryData kind w r s a b c d n q x y X Y))))).close

theorem source_binaryFields {m} (kind : Fin 4) (w h r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryFieldsSentence kind w h r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact SyntaxRenameFieldsTransfer.binary_iff hZ kind w h r s a b c d n q x y X Y h0 h1

theorem binaryFields_kernel_certificate {m} (kind : Fin 4) (w h r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryFieldsSentence kind w h r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_binaryFields kind w h r s a b c d n q x y X Y)

theorem native_binaryFields {m} (kind : Fin 4) (w h r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryFieldsSentence kind w h r s a b c d n q x y X Y)) := ZFReplay.replay (binaryFields_kernel_certificate kind w h r s a b c d n q x y X Y)

def binaryCaseSentence {m} (kind : Fin 4) (w h r s a b c d n q : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameRecursionSyntax.graph w h n).imp (((SyntaxRenameLogicalSyntax.binary kind w h r s a b c d n q).iff (SyntaxRenameRecursiveSyntax.binary kind w r s a b c d n q))))).close

theorem source_binaryCase {m} (kind : Fin 4) (w h r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryCaseSentence kind w h r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact SyntaxRenameCaseTransfer.binary_iff hZ kind w h r s a b c d n q h0 h1

theorem binaryCase_kernel_certificate {m} (kind : Fin 4) (w h r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryCaseSentence kind w h r s a b c d n q)) := TheoryTransport.sentence (source_binaryCase kind w h r s a b c d n q)

theorem native_binaryCase {m} (kind : Fin 4) (w h r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryCaseSentence kind w h r s a b c d n q)) := ZFReplay.replay (binaryCase_kernel_certificate kind w h r s a b c d n q)

def allCasesSentence {m} (w R S r s a b c d h n q : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameRecursionSyntax.graph w h n).imp (((SyntaxRenameLocalSyntax.cases w R S r s a b c d h n q).iff (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q))))).close

theorem source_allCases {m} (w R S r s a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allCasesSentence w R S r s a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLocalTransfer.all_iff hZ w R S r s a b c d h n q h0 h1

theorem allCases_kernel_certificate {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allCasesSentence w R S r s a b c d h n q)) := TheoryTransport.sentence (source_allCases w R S r s a b c d h n q)

theorem native_allCases {m} (w R S r s a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allCasesSentence w R S r s a b c d h n q)) := ZFReplay.replay (allCases_kernel_certificate w R S r s a b c d h n q)

def localSentence {m} (w R S a b c d h n q : Fin m) : Source.Sentence := ((OrdinalSyntax.ordinal n).imp ((SyntaxRenameRecursionSyntax.graph w h n).imp (((SyntaxRenameLocalSyntax.localRename w R S a b c d h n q).iff (SyntaxRenameRecursiveSyntax.localRename w R S a b c d n q))))).close

theorem source_local {m} (w R S a b c d h n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (localSentence w R S a b c d h n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursionSyntax.graph w h n) (Context.add (OrdinalSyntax.ordinal n) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (OrdinalSyntax.ordinal n) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameRecursionSyntax.graph w h n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLocalTransfer.local_iff hZ w R S a b c d h n q h0 h1

theorem local_kernel_certificate {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (localSentence w R S a b c d h n q)) := TheoryTransport.sentence (source_local w R S a b c d h n q)

theorem native_local {m} (w R S a b c d h n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (localSentence w R S a b c d h n q)) := ZFReplay.replay (local_kernel_certificate w R S a b c d h n q)

def recursiveAtValueSentence {m} (w r s a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((SyntaxRenameEvaluationSyntax.evaluation w n v).imp (((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).iff (SyntaxRenameRecursiveSyntax.criterion w r s a b c d n q)))))).close

theorem source_recursiveAtValue {m} (w r s a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursiveAtValueSentence w r s a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameEvaluationSyntax.evaluation w n v) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameEvaluationSyntax.evaluation w n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameRecursive.at_value hZ w r s a b c d n q v h0 h1 h2

theorem recursiveAtValue_kernel_certificate {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursiveAtValueSentence w r s a b c d n q v)) := TheoryTransport.sentence (source_recursiveAtValue w r s a b c d n q v)

theorem native_recursiveAtValue {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursiveAtValueSentence w r s a b c d n q v)) := ZFReplay.replay (recursiveAtValue_kernel_certificate w r s a b c d n q v)

def recursiveSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).iff (SyntaxRenameRecursiveSyntax.criterion w r s a b c d n q)))).close

theorem source_recursive {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (recursiveSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxRenameRecursive.recursive_iff hZ w r s a b c d n q h0

theorem recursive_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (recursiveSentence w r s a b c d n q)) := TheoryTransport.sentence (source_recursive w r s a b c d n q)

theorem native_recursive {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (recursiveSentence w r s a b c d n q)) := ZFReplay.replay (recursive_kernel_certificate w r s a b c d n q)

def sourceTypeSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q).imp ((FormulaCodeSyntax.formulaCode w n a b)))).close

theorem source_sourceType {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceTypeSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameRecursive.source_type hZ w r s a b c d n q h0 h1

theorem sourceType_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceTypeSentence w r s a b c d n q)) := TheoryTransport.sentence (source_sourceType w r s a b c d n q)

theorem native_sourceType {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceTypeSentence w r s a b c d n q)) := ZFReplay.replay (sourceType_kernel_certificate w r s a b c d n q)

def universalSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameSystemSyntax.universalLaw w))).close

theorem source_universal {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (universalSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxRenameSystem.all_law hZ w h0

theorem universal_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (universalSentence w)) := TheoryTransport.sentence (source_universal w)

theorem native_universal {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (universalSentence w)) := ZFReplay.replay (universal_kernel_certificate w)

def actualSystemSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameSystemSyntax.system w))).close

theorem source_actualSystem {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualSystemSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxRenameSystem.actual_system hZ w h0

theorem actualSystem_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualSystemSentence w)) := TheoryTransport.sentence (source_actualSystem w)

theorem native_actualSystem {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualSystemSentence w)) := ZFReplay.replay (actualSystem_kernel_certificate w)

def existenceSentence : Source.Sentence := SyntaxRenameSystemSyntax.existsSystem

theorem source_existence : Derives (Source.SetLanguage.ZF.at 0) existenceSentence := by
  have hh := SyntaxRenameSystem.existence (ZFContext.source_ZF 0)
  have hId : (Fin.elim0 : Fin 0 → Fin 0) = id := by funext i; exact Fin.elim0 i
  simpa only [existenceSentence, hId, Reverse.source_rename_id] using hh

theorem existence_kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence existenceSentence) := TheoryTransport.sentence source_existence

theorem native_existence : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence existenceSentence) := ZFReplay.replay existence_kernel_certificate
end PPAC.Migration.Internal.ObjectSyntaxRenameRecursive
