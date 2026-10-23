import PPAC.Migration.Internal.NativeFormulaQuotationValue

/-! 原生全11公式替换的精确quotation对应及实际带类型联合唯一纤维的原YesMetaZFC核证书。 -/
namespace PPAC.Migration.Internal.ObjectNativeFormulaQuotation
open Source SourceAlgebra SourceLogic OmegaSyntax

def environmentExistsSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral sb.length a).imp ((SyntaxNumeralSyntax.numeral sf.length b).imp ((SyntaxNumeralSyntax.numeral tb.length c).imp ((SyntaxNumeralSyntax.numeral tf.length d).imp ((NativeSubstitutionSyntax.existsEnvironment σ τ w a b c d))))))).close

theorem source_environmentExists {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentExistsSentence σ τ w a b c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral tf.length d) (Context.add (SyntaxNumeralSyntax.numeral tb.length c) (Context.add (SyntaxNumeralSyntax.numeral sf.length b) (Context.add (SyntaxNumeralSyntax.numeral sb.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d) := .hyp (Or.inl rfl)
  exact NativeSubstitutionEnvironment.exists_environment hZ σ τ w a b c d h0 h1 h2 h3 h4

theorem environmentExists_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentExistsSentence σ τ w a b c d)) := TheoryTransport.sentence (source_environmentExists σ τ w a b c d)

theorem native_environmentExists {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentExistsSentence σ τ w a b c d)) := ZFReplay.replay (environmentExists_kernel_certificate σ τ w a b c d)

def environmentFiberSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral sb.length a).imp ((SyntaxNumeralSyntax.numeral sf.length b).imp ((SyntaxNumeralSyntax.numeral tb.length c).imp ((SyntaxNumeralSyntax.numeral tf.length d).imp ((NativeSubstitutionSyntax.fiber σ τ w a b c d))))))).close

theorem source_environmentFiber {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentFiberSentence σ τ w a b c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral tf.length d) (Context.add (SyntaxNumeralSyntax.numeral tb.length c) (Context.add (SyntaxNumeralSyntax.numeral sf.length b) (Context.add (SyntaxNumeralSyntax.numeral sb.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d) := .hyp (Or.inl rfl)
  exact NativeSubstitutionEnvironment.actual_fiber hZ σ τ w a b c d h0 h1 h2 h3 h4

theorem environmentFiber_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentFiberSentence σ τ w a b c d)) := TheoryTransport.sentence (source_environmentFiber σ τ w a b c d)

theorem native_environmentFiber {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentFiberSentence σ τ w a b c d)) := ZFReplay.replay (environmentFiber_kernel_certificate σ τ w a b c d)

def environmentAtLiftedSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w R S a b c d A C K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral sb.length a).imp ((SyntaxNumeralSyntax.numeral sf.length b).imp ((SyntaxNumeralSyntax.numeral tb.length c).imp ((SyntaxNumeralSyntax.numeral tf.length d).imp ((NativeSubstitutionSyntax.environment σ τ w a b c d R S).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((NativeSubstitutionSyntax.environment (YesMetaZFC.Logic.FirstOrder.VariableSubstitution.liftBound YesMetaZFC.SetTheory.SetSort.set σ) (YesMetaZFC.Logic.FirstOrder.VariableSubstitution.weakenBound YesMetaZFC.SetTheory.SetSort.set τ) w A b C d K H))))))))).close

theorem source_environmentAtLifted {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w R S a b c d A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (environmentAtLiftedSentence σ τ w R S a b c d A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (NativeSubstitutionSyntax.environment σ τ w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral tf.length d) (Context.add (SyntaxNumeralSyntax.numeral tb.length c) (Context.add (SyntaxNumeralSyntax.numeral sf.length b) (Context.add (SyntaxNumeralSyntax.numeral sb.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (NativeSubstitutionSyntax.environment σ τ w a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inl rfl)
  exact NativeSubstitutionEnvironment.at_lifted hZ σ τ w R S a b c d A C K H h0 h1 h2 h3 h4 h5 h6

theorem environmentAtLifted_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (environmentAtLiftedSentence σ τ w R S a b c d A C K H)) := TheoryTransport.sentence (source_environmentAtLifted σ τ w R S a b c d A C K H)

theorem native_environmentAtLifted {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (w R S a b c d A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (environmentAtLiftedSentence σ τ w R S a b c d A C K H)) := ZFReplay.replay (environmentAtLifted_kernel_certificate σ τ w R S a b c d A C K H)

def termIffSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm sb sf sort) (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral sb.length a).imp ((SyntaxNumeralSyntax.numeral sf.length b).imp ((NativeSubstitutionSyntax.environment σ τ w a b c d R S).imp ((PureQuotationSyntax.term input w n).imp (((SyntaxCodedMixedTermSyntax.substituted w R S a b c d n q).iff (PureQuotationSyntax.term (input.substituteMapped σ τ) w q)))))))).close

theorem source_termIff {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm sb sf sort) (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termIffSentence σ τ input w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.term input w n) (Context.add (NativeSubstitutionSyntax.environment σ τ w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral sf.length b) (Context.add (SyntaxNumeralSyntax.numeral sb.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (NativeSubstitutionSyntax.environment σ τ w a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (PureQuotationSyntax.term input w n) := .hyp (Or.inl rfl)
  exact NativeTermQuotationSubstitution.term_iff hZ σ τ input w R S a b c d n q h0 h1 h2 h3 h4

theorem termIff_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm sb sf sort) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termIffSentence σ τ input w R S a b c d n q)) := TheoryTransport.sentence (source_termIff σ τ input w R S a b c d n q)

theorem native_termIff {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) {sort : YesMetaZFC.SetTheory.SetSort} (input : PureSyntaxQuotation.Tm sb sf sort) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termIffSentence σ τ input w R S a b c d n q)) := ZFReplay.replay (termIff_kernel_certificate σ τ input w R S a b c d n q)

def nullaryStepSentence {m} (truth : Bool) (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (SyntaxAtomSyntax.nullaryTag truth)) w n).imp ((OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (SyntaxAtomSyntax.nullaryTag truth)) w q).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)))))).close

theorem source_nullaryStep {m} (truth : Bool) (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryStepSentence truth w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (SyntaxAtomSyntax.nullaryTag truth)) w q) (Context.add (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (SyntaxAtomSyntax.nullaryTag truth)) w n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (SyntaxAtomSyntax.nullaryTag truth)) w n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf (SyntaxAtomSyntax.nullaryTag truth)) w q) := .hyp (Or.inl rfl)
  exact FormulaQuotationAtomicSteps.nullary hZ truth w R S a b c d n q h0 h1 h2 h3

theorem nullaryStep_kernel_certificate {m} (truth : Bool) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryStepSentence truth w R S a b c d n q)) := TheoryTransport.sentence (source_nullaryStep truth w R S a b c d n q)

theorem native_nullaryStep {m} (truth : Bool) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryStepSentence truth w R S a b c d n q)) := ZFReplay.replay (nullaryStep_kernel_certificate truth w R S a b c d n q)

def equalityStepSentence {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((OriginalTreeQuotationSyntax.tree (.node 3 [left,right]) w n).imp ((OriginalTreeQuotationSyntax.tree (.node 3 [targetLeft,targetRight]) w q).imp ((OriginalTreeQuotationSyntax.tree (left) w x).imp ((OriginalTreeQuotationSyntax.tree (right) w y).imp ((OriginalTreeQuotationSyntax.tree (targetLeft) w X).imp ((OriginalTreeQuotationSyntax.tree (targetRight) w Y).imp ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d x X).imp ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d y Y).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)))))))))))).close

theorem source_equalityStep {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityStepSentence left right targetLeft targetRight w R S a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d y Y) (Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x X) (Context.add (OriginalTreeQuotationSyntax.tree (targetRight) w Y) (Context.add (OriginalTreeQuotationSyntax.tree (targetLeft) w X) (Context.add (OriginalTreeQuotationSyntax.tree (right) w y) (Context.add (OriginalTreeQuotationSyntax.tree (left) w x) (Context.add (OriginalTreeQuotationSyntax.tree (.node 3 [targetLeft,targetRight]) w q) (Context.add (OriginalTreeQuotationSyntax.tree (.node 3 [left,right]) w n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 3 [left,right]) w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 3 [targetLeft,targetRight]) w q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (OriginalTreeQuotationSyntax.tree (left) w x) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (OriginalTreeQuotationSyntax.tree (right) w y) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (OriginalTreeQuotationSyntax.tree (targetLeft) w X) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (OriginalTreeQuotationSyntax.tree (targetRight) w Y) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x X) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d y Y) := .hyp (Or.inl rfl)
  exact FormulaQuotationAtomicSteps.equality hZ left right targetLeft targetRight w R S a b c d n q x y X Y h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem equalityStep_kernel_certificate {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityStepSentence left right targetLeft targetRight w R S a b c d n q x y X Y)) := TheoryTransport.sentence (source_equalityStep left right targetLeft targetRight w R S a b c d n q x y X Y)

theorem native_equalityStep {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityStepSentence left right targetLeft targetRight w R S a b c d n q x y X Y)) := ZFReplay.replay (equalityStep_kernel_certificate left right targetLeft targetRight w R S a b c d n q x y X Y)

def membershipStepSentence {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q s x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((OriginalTreeQuotationSyntax.tree (.node 2 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0,left,right]) w n).imp ((OriginalTreeQuotationSyntax.tree (.node 2 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0,targetLeft,targetRight]) w q).imp ((OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0) w s).imp ((OriginalTreeQuotationSyntax.tree (left) w x).imp ((OriginalTreeQuotationSyntax.tree (right) w y).imp ((OriginalTreeQuotationSyntax.tree (targetLeft) w X).imp ((OriginalTreeQuotationSyntax.tree (targetRight) w Y).imp ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d x X).imp ((SyntaxCodedMixedTermSyntax.substituted w R S a b c d y Y).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q))))))))))))).close

theorem source_membershipStep {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q s x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipStepSentence left right targetLeft targetRight w R S a b c d n q s x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d y Y) (Context.add (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x X) (Context.add (OriginalTreeQuotationSyntax.tree (targetRight) w Y) (Context.add (OriginalTreeQuotationSyntax.tree (targetLeft) w X) (Context.add (OriginalTreeQuotationSyntax.tree (right) w y) (Context.add (OriginalTreeQuotationSyntax.tree (left) w x) (Context.add (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0) w s) (Context.add (OriginalTreeQuotationSyntax.tree (.node 2 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0,targetLeft,targetRight]) w q) (Context.add (OriginalTreeQuotationSyntax.tree (.node 2 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0,left,right]) w n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 2 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0,left,right]) w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 2 [YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0,targetLeft,targetRight]) w q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h4 : Derives Δ (OriginalTreeQuotationSyntax.tree (YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.leaf 0) w s) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h5 : Derives Δ (OriginalTreeQuotationSyntax.tree (left) w x) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h6 : Derives Δ (OriginalTreeQuotationSyntax.tree (right) w y) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h7 : Derives Δ (OriginalTreeQuotationSyntax.tree (targetLeft) w X) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h8 : Derives Δ (OriginalTreeQuotationSyntax.tree (targetRight) w Y) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h9 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d x X) := .hyp (Or.inr (Or.inl rfl))
  have h10 : Derives Δ (SyntaxCodedMixedTermSyntax.substituted w R S a b c d y Y) := .hyp (Or.inl rfl)
  exact FormulaQuotationAtomicSteps.membership hZ left right targetLeft targetRight w R S a b c d n q s x y X Y h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

theorem membershipStep_kernel_certificate {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q s x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipStepSentence left right targetLeft targetRight w R S a b c d n q s x y X Y)) := TheoryTransport.sentence (source_membershipStep left right targetLeft targetRight w R S a b c d n q s x y X Y)

theorem native_membershipStep {m} (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q s x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipStepSentence left right targetLeft targetRight w R S a b c d n q s x y X Y)) := ZFReplay.replay (membershipStep_kernel_certificate left right targetLeft targetRight w R S a b c d n q s x y X Y)

def negationStepSentence {m} (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((OriginalTreeQuotationSyntax.tree (.node 4 [body]) w n).imp ((OriginalTreeQuotationSyntax.tree (.node 4 [targetBody]) w q).imp ((OriginalTreeQuotationSyntax.tree (body) w x).imp ((OriginalTreeQuotationSyntax.tree (targetBody) w X).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q))))))))).close

theorem source_negationStep {m} (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationStepSentence body targetBody w R S a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X) (Context.add (OriginalTreeQuotationSyntax.tree (targetBody) w X) (Context.add (OriginalTreeQuotationSyntax.tree (body) w x) (Context.add (OriginalTreeQuotationSyntax.tree (.node 4 [targetBody]) w q) (Context.add (OriginalTreeQuotationSyntax.tree (.node 4 [body]) w n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 4 [body]) w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node 4 [targetBody]) w q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (OriginalTreeQuotationSyntax.tree (body) w x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (OriginalTreeQuotationSyntax.tree (targetBody) w X) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X) := .hyp (Or.inl rfl)
  exact FormulaQuotationLogicalSteps.negation hZ body targetBody w R S a b c d n q x X h0 h1 h2 h3 h4 h5 h6

theorem negationStep_kernel_certificate {m} (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationStepSentence body targetBody w R S a b c d n q x X)) := TheoryTransport.sentence (source_negationStep body targetBody w R S a b c d n q x X)

theorem native_negationStep {m} (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationStepSentence body targetBody w R S a b c d n q x X)) := ZFReplay.replay (negationStep_kernel_certificate body targetBody w R S a b c d n q x X)

def binaryStepSentence {m} (kind : Fin 4) (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.binaryTag kind) [left,right]) w n).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.binaryTag kind) [targetLeft,targetRight]) w q).imp ((OriginalTreeQuotationSyntax.tree (left) w x).imp ((OriginalTreeQuotationSyntax.tree (right) w y).imp ((OriginalTreeQuotationSyntax.tree (targetLeft) w X).imp ((OriginalTreeQuotationSyntax.tree (targetRight) w Y).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d y Y).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)))))))))))).close

theorem source_binaryStep {m} (kind : Fin 4) (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryStepSentence kind left right targetLeft targetRight w R S a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d y Y) (Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X) (Context.add (OriginalTreeQuotationSyntax.tree (targetRight) w Y) (Context.add (OriginalTreeQuotationSyntax.tree (targetLeft) w X) (Context.add (OriginalTreeQuotationSyntax.tree (right) w y) (Context.add (OriginalTreeQuotationSyntax.tree (left) w x) (Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.binaryTag kind) [targetLeft,targetRight]) w q) (Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.binaryTag kind) [left,right]) w n) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.binaryTag kind) [left,right]) w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.binaryTag kind) [targetLeft,targetRight]) w q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (OriginalTreeQuotationSyntax.tree (left) w x) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (OriginalTreeQuotationSyntax.tree (right) w y) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (OriginalTreeQuotationSyntax.tree (targetLeft) w X) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (OriginalTreeQuotationSyntax.tree (targetRight) w Y) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x X) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d y Y) := .hyp (Or.inl rfl)
  exact FormulaQuotationLogicalSteps.binary hZ kind left right targetLeft targetRight w R S a b c d n q x y X Y h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem binaryStep_kernel_certificate {m} (kind : Fin 4) (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryStepSentence kind left right targetLeft targetRight w R S a b c d n q x y X Y)) := TheoryTransport.sentence (source_binaryStep kind left right targetLeft targetRight w R S a b c d n q x y X Y)

theorem native_binaryStep {m} (kind : Fin 4) (left right targetLeft targetRight : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryStepSentence kind left right targetLeft targetRight w R S a b c d n q x y X Y)) := ZFReplay.replay (binaryStep_kernel_certificate kind left right targetLeft targetRight w R S a b c d n q x y X Y)

def quantifiedStepSentence {m} (universal : Bool) (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X A C K H : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMixedFormulaOutputSyntax.input w R S a b c d n).imp ((SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [body]) w n).imp ((OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [targetBody]) w q).imp ((OriginalTreeQuotationSyntax.tree (body) w x).imp ((OriginalTreeQuotationSyntax.tree (targetBody) w X).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w K H A b C d x X).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)))))))))).close

theorem source_quantifiedStep {m} (universal : Bool) (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X A C K H : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifiedStepSentence universal body targetBody w R S a b c d n q x X A C K H) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A b C d x X) (Context.add (OriginalTreeQuotationSyntax.tree (targetBody) w X) (Context.add (OriginalTreeQuotationSyntax.tree (body) w x) (Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [targetBody]) w q) (Context.add (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [body]) w n) (Context.add (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) (Context.add (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxMixedFormulaOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c d A C K H) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [body]) w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (OriginalTreeQuotationSyntax.tree (.node (SyntaxLogicalSyntax.quantifierTag universal) [targetBody]) w q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (OriginalTreeQuotationSyntax.tree (body) w x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (OriginalTreeQuotationSyntax.tree (targetBody) w X) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w K H A b C d x X) := .hyp (Or.inl rfl)
  exact FormulaQuotationLogicalSteps.quantified hZ universal body targetBody w R S a b c d n q x X A C K H h0 h1 h2 h3 h4 h5 h6 h7

theorem quantifiedStep_kernel_certificate {m} (universal : Bool) (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifiedStepSentence universal body targetBody w R S a b c d n q x X A C K H)) := TheoryTransport.sentence (source_quantifiedStep universal body targetBody w R S a b c d n q x X A C K H)

theorem native_quantifiedStep {m} (universal : Bool) (body targetBody : YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket.Tree) (w R S a b c d n q x X A C K H : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifiedStepSentence universal body targetBody w R S a b c d n q x X A C K H)) := ZFReplay.replay (quantifiedStep_kernel_certificate universal body targetBody w R S a b c d n q x X A C K H)

def formulaConstructSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral sb.length a).imp ((SyntaxNumeralSyntax.numeral sf.length b).imp ((SyntaxNumeralSyntax.numeral tb.length c).imp ((SyntaxNumeralSyntax.numeral tf.length d).imp ((NativeSubstitutionSyntax.environment σ τ w a b c d R S).imp ((PureQuotationSyntax.formula input w n).imp ((PureQuotationSyntax.formula (input.substituteMapped σ τ) w q).imp ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)))))))))).close

theorem source_formulaConstruct {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaConstructSentence σ τ input w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula (input.substituteMapped σ τ) w q) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (NativeSubstitutionSyntax.environment σ τ w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral tf.length d) (Context.add (SyntaxNumeralSyntax.numeral tb.length c) (Context.add (SyntaxNumeralSyntax.numeral sf.length b) (Context.add (SyntaxNumeralSyntax.numeral sb.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (NativeSubstitutionSyntax.environment σ τ w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (PureQuotationSyntax.formula (input.substituteMapped σ τ) w q) := .hyp (Or.inl rfl)
  exact NativeFormulaQuotationConstruct.construct hZ input σ τ w R S a b c d n q h0 h1 h2 h3 h4 h5 h6 h7

theorem formulaConstruct_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaConstructSentence σ τ input w R S a b c d n q)) := TheoryTransport.sentence (source_formulaConstruct σ τ input w R S a b c d n q)

theorem native_formulaConstruct {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaConstructSentence σ τ input w R S a b c d n q)) := ZFReplay.replay (formulaConstruct_kernel_certificate σ τ input w R S a b c d n q)

def formulaIffSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral sb.length a).imp ((SyntaxNumeralSyntax.numeral sf.length b).imp ((SyntaxNumeralSyntax.numeral tb.length c).imp ((SyntaxNumeralSyntax.numeral tf.length d).imp ((NativeSubstitutionSyntax.environment σ τ w a b c d R S).imp ((PureQuotationSyntax.formula input w n).imp (((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q).iff (PureQuotationSyntax.formula (input.substituteMapped σ τ) w q)))))))))).close

theorem source_formulaIff {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaIffSentence σ τ input w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula input w n) (Context.add (NativeSubstitutionSyntax.environment σ τ w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral tf.length d) (Context.add (SyntaxNumeralSyntax.numeral tb.length c) (Context.add (SyntaxNumeralSyntax.numeral sf.length b) (Context.add (SyntaxNumeralSyntax.numeral sb.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (NativeSubstitutionSyntax.environment σ τ w a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inl rfl)
  exact NativeFormulaQuotationCorrespondence.formula_iff hZ input σ τ w R S a b c d n q h0 h1 h2 h3 h4 h5 h6

theorem formulaIff_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaIffSentence σ τ input w R S a b c d n q)) := TheoryTransport.sentence (source_formulaIff σ τ input w R S a b c d n q)

theorem native_formulaIff {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaIffSentence σ τ input w R S a b c d n q)) := ZFReplay.replay (formulaIff_kernel_certificate σ τ input w R S a b c d n q)

def formulaAtCandidateSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral sb.length a).imp ((SyntaxNumeralSyntax.numeral sf.length b).imp ((SyntaxNumeralSyntax.numeral tb.length c).imp ((SyntaxNumeralSyntax.numeral tf.length d).imp ((NativeSubstitutionSyntax.environment σ τ w a b c d R S).imp ((PureQuotationSyntax.formula input w n).imp ((PureQuotationSyntax.formula (input.substituteMapped σ τ) w q).imp ((NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n q)))))))))).close

theorem source_formulaAtCandidate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaAtCandidateSentence σ τ input w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula (input.substituteMapped σ τ) w q) (Context.add (PureQuotationSyntax.formula input w n) (Context.add (NativeSubstitutionSyntax.environment σ τ w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral tf.length d) (Context.add (SyntaxNumeralSyntax.numeral tb.length c) (Context.add (SyntaxNumeralSyntax.numeral sf.length b) (Context.add (SyntaxNumeralSyntax.numeral sb.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (NativeSubstitutionSyntax.environment σ τ w a b c d R S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (PureQuotationSyntax.formula (input.substituteMapped σ τ) w q) := .hyp (Or.inl rfl)
  exact NativeFormulaQuotationValue.at_candidate hZ input σ τ w R S a b c d n q h0 h1 h2 h3 h4 h5 h6 h7

theorem formulaAtCandidate_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaAtCandidateSentence σ τ input w R S a b c d n q)) := TheoryTransport.sentence (source_formulaAtCandidate σ τ input w R S a b c d n q)

theorem native_formulaAtCandidate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaAtCandidateSentence σ τ input w R S a b c d n q)) := ZFReplay.replay (formulaAtCandidate_kernel_certificate σ τ input w R S a b c d n q)

def formulaValueUniqueSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n q).imp ((NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n v).imp ((.equal q v))))).close

theorem source_formulaValueUnique {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaValueUniqueSentence σ τ input w R S a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n v) (Context.add (NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n v) := .hyp (Or.inl rfl)
  exact NativeFormulaQuotationValue.unique hZ input σ τ w R S a b c d n q v h0 h1 h2

theorem formulaValueUnique_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaValueUniqueSentence σ τ input w R S a b c d n q v)) := TheoryTransport.sentence (source_formulaValueUnique σ τ input w R S a b c d n q v)

theorem native_formulaValueUnique {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaValueUniqueSentence σ τ input w R S a b c d n q v)) := ZFReplay.replay (formulaValueUnique_kernel_certificate σ τ input w R S a b c d n q v)

def formulaUniqueOutputSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n q).imp ((SyntaxMixedFormulaOutputSyntax.uniqueOutput w R S a b c d n q)))).close

theorem source_formulaUniqueOutput {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaUniqueOutputSentence σ τ input w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (NativeFormulaQuotationValueSyntax.value input σ τ w R S a b c d n q) := .hyp (Or.inl rfl)
  exact NativeFormulaQuotationValue.unique_output hZ input σ τ w R S a b c d n q h0 h1

theorem formulaUniqueOutput_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaUniqueOutputSentence σ τ input w R S a b c d n q)) := TheoryTransport.sentence (source_formulaUniqueOutput σ τ input w R S a b c d n q)

theorem native_formulaUniqueOutput {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaUniqueOutputSentence σ τ input w R S a b c d n q)) := ZFReplay.replay (formulaUniqueOutput_kernel_certificate σ τ input w R S a b c d n q)

def formulaFiberSentence {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNumeralSyntax.numeral sb.length a).imp ((SyntaxNumeralSyntax.numeral sf.length b).imp ((SyntaxNumeralSyntax.numeral tb.length c).imp ((SyntaxNumeralSyntax.numeral tf.length d).imp ((NativeSubstitutionSyntax.environment σ τ w a b c d R S).imp ((PureQuotationSyntax.formula input w n).imp ((NativeFormulaQuotationValueSyntax.fiber input σ τ w R S a b c d n))))))))).close

theorem source_formulaFiber {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (formulaFiberSentence σ τ input w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (PureQuotationSyntax.formula input w n) (Context.add (NativeSubstitutionSyntax.environment σ τ w a b c d R S) (Context.add (SyntaxNumeralSyntax.numeral tf.length d) (Context.add (SyntaxNumeralSyntax.numeral tb.length c) (Context.add (SyntaxNumeralSyntax.numeral sf.length b) (Context.add (SyntaxNumeralSyntax.numeral sb.length a) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (NativeSubstitutionSyntax.environment σ τ w a b c d R S) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (PureQuotationSyntax.formula input w n) := .hyp (Or.inl rfl)
  exact NativeFormulaQuotationValue.actual_fiber hZ input σ τ w R S a b c d n h0 h1 h2 h3 h4 h5 h6

theorem formulaFiber_kernel_certificate {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (formulaFiberSentence σ τ input w R S a b c d n)) := TheoryTransport.sentence (source_formulaFiber σ τ input w R S a b c d n)

theorem native_formulaFiber {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (σ : NativeSubstitutionSyntax.Mapping sb tb tf) (τ : NativeSubstitutionSyntax.Mapping sf tb tf) (input : PureSyntaxQuotation.Fm sb sf) (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (formulaFiberSentence σ τ input w R S a b c d n)) := ZFReplay.replay (formulaFiber_kernel_certificate σ τ input w R S a b c d n)

end PPAC.Migration.Internal.ObjectNativeFormulaQuotation
