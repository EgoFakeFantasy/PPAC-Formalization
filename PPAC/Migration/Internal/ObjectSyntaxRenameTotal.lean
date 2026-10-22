import PPAC.Migration.Internal.SyntaxRenameOutputClassify

/-! 全内部合法公式的实际唯一重命名输出、七类推进与原对象归纳关闭的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxRenameTotal
open Source SourceAlgebra SourceLogic OmegaSyntax

def tagFilterSentence {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor arity kind.val w xs n).imp ((SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q).imp (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q)))).close

theorem source_tagFilter {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tagFilterSentence kind arity w R S r s a b c d n q xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q) (Context.add (SyntaxNodeSyntax.constructor arity kind.val w xs n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor arity kind.val w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTagCases.filter hZ kind arity w R S r s a b c d n q xs h0 h1 h2

theorem tagFilter_kernel_certificate {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tagFilterSentence kind arity w R S r s a b c d n q xs)) := TheoryTransport.sentence (source_tagFilter kind arity w R S r s a b c d n q xs)

theorem native_tagFilter {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tagFilterSentence kind arity w R S r s a b c d n q xs)) := ZFReplay.replay (tagFilter_kernel_certificate kind arity w R S r s a b c d n q xs)

def tagJudgmentSentence {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxNodeSyntax.constructor arity kind.val w xs n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q)))))).close

theorem source_tagJudgment {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Derives (Source.SetLanguage.ZF.at 0) (tagJudgmentSentence kind arity w R S r s a b c d n q xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxNodeSyntax.constructor arity kind.val w xs n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNodeSyntax.constructor arity kind.val w xs n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTagCases.of_renamed hZ kind arity w R S r s a b c d n q xs h0 h1 h2 h3 h4

theorem tagJudgment_kernel_certificate {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (tagJudgmentSentence kind arity w R S r s a b c d n q xs)) := TheoryTransport.sentence (source_tagJudgment kind arity w R S r s a b c d n q xs)

theorem native_tagJudgment {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (tagJudgmentSentence kind arity w R S r s a b c d n q xs)) := ZFReplay.replay (tagJudgment_kernel_certificate kind arity w R S r s a b c d n q xs)

def fiberUniqueSentence {m} (w R S a b c d n q v : Fin m) : Source.Sentence := ((SyntaxRenameOutputSyntax.fiber w R S a b c d n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v).imp (Formula.equal q v)))).close

theorem source_fiberUnique {m} (w R S a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberUniqueSentence w R S a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxRenameOutputSyntax.fiber w R S a b c d n) ((Source.SetLanguage.ZF.at m))))
  have h0 : Derives Δ (SyntaxRenameOutputSyntax.fiber w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameFiberUnique.fiber_unique w R S a b c d n q v h0 h1 h2

theorem fiberUnique_kernel_certificate {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberUniqueSentence w R S a b c d n q v)) := TheoryTransport.sentence (source_fiberUnique w R S a b c d n q v)

theorem native_fiberUnique {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberUniqueSentence w R S a b c d n q v)) := ZFReplay.replay (fiberUnique_kernel_certificate w R S a b c d n q v)

def propertyUniqueSentence {m} (w R S a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.property w n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v).imp (Formula.equal q v))))).close

theorem source_propertyUnique {m} (w R S a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (propertyUniqueSentence w R S a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxRenameOutputSyntax.property w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.property w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameFiberUnique.property_unique hZ w R S a b c d n q v h0 h1 h2 h3

theorem propertyUnique_kernel_certificate {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (propertyUniqueSentence w R S a b c d n q v)) := TheoryTransport.sentence (source_propertyUnique w R S a b c d n q v)

theorem native_propertyUnique {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (propertyUniqueSentence w R S a b c d n q v)) := ZFReplay.replay (propertyUnique_kernel_certificate w R S a b c d n q v)

def checkTargetSentence {m} (advance : Bool) (w x R S a b c d q : Fin m) : Source.Sentence := ((SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q).imp (FormulaCodeRecursiveSyntax.stepCheck advance w q c d)).close

theorem source_checkTarget {m} (advance : Bool) (w x R S a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkTargetSentence advance w x R S a b c d q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q) := .hyp (Or.inl rfl)
  exact SyntaxRenameCheckUnique.target_type advance w x R S a b c d q h0

theorem checkTarget_kernel_certificate {m} (advance : Bool) (w x R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkTargetSentence advance w x R S a b c d q)) := TheoryTransport.sentence (source_checkTarget advance w x R S a b c d q)

theorem native_checkTarget {m} (advance : Bool) (w x R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkTargetSentence advance w x R S a b c d q)) := ZFReplay.replay (checkTarget_kernel_certificate advance w x R S a b c d q)

def checkNaturalSentence {m} (advance : Bool) (w x R S a b c d q : Fin m) : Source.Sentence := ((SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q).imp (Formula.mem q w)).close

theorem source_checkNatural {m} (advance : Bool) (w x R S a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkNaturalSentence advance w x R S a b c d q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q) := .hyp (Or.inl rfl)
  exact SyntaxRenameCheckUnique.natural advance w x R S a b c d q h0

theorem checkNatural_kernel_certificate {m} (advance : Bool) (w x R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkNaturalSentence advance w x R S a b c d q)) := TheoryTransport.sentence (source_checkNatural advance w x R S a b c d q)

theorem native_checkNatural {m} (advance : Bool) (w x R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkNaturalSentence advance w x R S a b c d q)) := ZFReplay.replay (checkNatural_kernel_certificate advance w x R S a b c d q)

def checkUniqueSentence {m} (advance : Bool) (w x R S a b c d q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.property w x).imp ((SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q).imp ((SyntaxRenameRecursiveSyntax.check advance w x R S a b c d v).imp (Formula.equal q v))))).close

theorem source_checkUnique {m} (advance : Bool) (w x R S a b c d q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkUniqueSentence advance w x R S a b c d q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d v) (Context.add (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q) (Context.add (SyntaxRenameOutputSyntax.property w x) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.property w x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d v) := .hyp (Or.inl rfl)
  exact SyntaxRenameCheckUnique.unique hZ advance w x R S a b c d q v h0 h1 h2 h3

theorem checkUnique_kernel_certificate {m} (advance : Bool) (w x R S a b c d q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkUniqueSentence advance w x R S a b c d q v)) := TheoryTransport.sentence (source_checkUnique advance w x R S a b c d q v)

theorem native_checkUnique {m} (advance : Bool) (w x R S a b c d q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkUniqueSentence advance w x R S a b c d q v)) := ZFReplay.replay (checkUnique_kernel_certificate advance w x R S a b c d q v)

def checkExistsSentence {m} (advance : Bool) (w x R S a b c d : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.property w x).imp ((FormulaCodeRecursiveSyntax.stepCheck advance w x a b).imp ((SyntaxMapCodeSyntax.mapCode w a c R).imp ((SyntaxMapCodeSyntax.mapCode w b d S).imp (SyntaxRenameCheckExistence.existsCheck advance w x R S a b c d)))))).close

theorem source_checkExists {m} (advance : Bool) (w x R S a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkExistsSentence advance w x R S a b c d) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxMapCodeSyntax.mapCode w b d S) (Context.add (SyntaxMapCodeSyntax.mapCode w a c R) (Context.add (FormulaCodeRecursiveSyntax.stepCheck advance w x a b) (Context.add (SyntaxRenameOutputSyntax.property w x) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.property w x) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (FormulaCodeRecursiveSyntax.stepCheck advance w x a b) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c R) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.mapCode w b d S) := .hyp (Or.inl rfl)
  exact SyntaxRenameCheckExistence.exists_at_property hZ advance w x R S a b c d h0 h1 h2 h3 h4

theorem checkExists_kernel_certificate {m} (advance : Bool) (w x R S a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkExistsSentence advance w x R S a b c d)) := TheoryTransport.sentence (source_checkExists advance w x R S a b c d)

theorem native_checkExists {m} (advance : Bool) (w x R S a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkExistsSentence advance w x R S a b c d)) := ZFReplay.replay (checkExists_kernel_certificate advance w x R S a b c d)

def singleDataUniqueSentence {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v x X u U : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameRecursiveSyntax.singleData tag advance w R S a b c d n q x X).imp ((SyntaxRenameRecursiveSyntax.singleData tag advance w R S a b c d n v u U).imp (Formula.equal q v))))).close

theorem source_singleDataUnique {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v x X u U : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleDataUniqueSentence tag advance w R S a b c d n q v x X u U) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.singleData tag advance w R S a b c d n v u U) (Context.add (SyntaxRenameRecursiveSyntax.singleData tag advance w R S a b c d n q x X) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameRecursiveSyntax.singleData tag advance w R S a b c d n q x X) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameRecursiveSyntax.singleData tag advance w R S a b c d n v u U) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalUnique.single_data_unique hZ tag advance w R S a b c d n q v x X u U h0 h1 h2 h3

theorem singleDataUnique_kernel_certificate {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v x X u U : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleDataUniqueSentence tag advance w R S a b c d n q v x X u U)) := TheoryTransport.sentence (source_singleDataUnique tag advance w R S a b c d n q v x X u U)

theorem native_singleDataUnique {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v x X u U : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleDataUniqueSentence tag advance w R S a b c d n q v x X u U)) := ZFReplay.replay (singleDataUnique_kernel_certificate tag advance w R S a b c d n q v x X u U)

def singleRelationUniqueSentence {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameRecursiveSyntax.single tag advance w R S a b c d n q).imp ((SyntaxRenameRecursiveSyntax.single tag advance w R S a b c d n v).imp (Formula.equal q v))))).close

theorem source_singleRelationUnique {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleRelationUniqueSentence tag advance w R S a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.single tag advance w R S a b c d n v) (Context.add (SyntaxRenameRecursiveSyntax.single tag advance w R S a b c d n q) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameRecursiveSyntax.single tag advance w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameRecursiveSyntax.single tag advance w R S a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalUnique.single_unique hZ tag advance w R S a b c d n q v h0 h1 h2 h3

theorem singleRelationUnique_kernel_certificate {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleRelationUniqueSentence tag advance w R S a b c d n q v)) := TheoryTransport.sentence (source_singleRelationUnique tag advance w R S a b c d n q v)

theorem native_singleRelationUnique {m} (tag : Nat) (advance : Bool) (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleRelationUniqueSentence tag advance w R S a b c d n q v)) := ZFReplay.replay (singleRelationUnique_kernel_certificate tag advance w R S a b c d n q v)

def binaryDataUniqueSentence {m} (kind : Fin 4) (w R S a b c d n q v x y X Y u t U V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameRecursiveSyntax.binaryData kind w R S a b c d n q x y X Y).imp ((SyntaxRenameRecursiveSyntax.binaryData kind w R S a b c d n v u t U V).imp (Formula.equal q v))))).close

theorem source_binaryDataUnique {m} (kind : Fin 4) (w R S a b c d n q v x y X Y u t U V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryDataUniqueSentence kind w R S a b c d n q v x y X Y u t U V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.binaryData kind w R S a b c d n v u t U V) (Context.add (SyntaxRenameRecursiveSyntax.binaryData kind w R S a b c d n q x y X Y) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameRecursiveSyntax.binaryData kind w R S a b c d n q x y X Y) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameRecursiveSyntax.binaryData kind w R S a b c d n v u t U V) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalUnique.binary_data_unique hZ kind w R S a b c d n q v x y X Y u t U V h0 h1 h2 h3

theorem binaryDataUnique_kernel_certificate {m} (kind : Fin 4) (w R S a b c d n q v x y X Y u t U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryDataUniqueSentence kind w R S a b c d n q v x y X Y u t U V)) := TheoryTransport.sentence (source_binaryDataUnique kind w R S a b c d n q v x y X Y u t U V)

theorem native_binaryDataUnique {m} (kind : Fin 4) (w R S a b c d n q v x y X Y u t U V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryDataUniqueSentence kind w R S a b c d n q v x y X Y u t U V)) := ZFReplay.replay (binaryDataUnique_kernel_certificate kind w R S a b c d n q v x y X Y u t U V)

def binaryRelationUniqueSentence {m} (kind : Fin 4) (w R S a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameRecursiveSyntax.binary kind w R S a b c d n q).imp ((SyntaxRenameRecursiveSyntax.binary kind w R S a b c d n v).imp (Formula.equal q v))))).close

theorem source_binaryRelationUnique {m} (kind : Fin 4) (w R S a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryRelationUniqueSentence kind w R S a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.binary kind w R S a b c d n v) (Context.add (SyntaxRenameRecursiveSyntax.binary kind w R S a b c d n q) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameRecursiveSyntax.binary kind w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameRecursiveSyntax.binary kind w R S a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalUnique.binary_unique hZ kind w R S a b c d n q v h0 h1 h2 h3

theorem binaryRelationUnique_kernel_certificate {m} (kind : Fin 4) (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryRelationUniqueSentence kind w R S a b c d n q v)) := TheoryTransport.sentence (source_binaryRelationUnique kind w R S a b c d n q v)

theorem native_binaryRelationUnique {m} (kind : Fin 4) (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryRelationUniqueSentence kind w R S a b c d n q v)) := ZFReplay.replay (binaryRelationUnique_kernel_certificate kind w R S a b c d n q v)

def negationAtOutputSentence {m} (w R S r s a b c d n x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxRenameRecursiveSyntax.check false w x R S a b c d X).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n))))))).close

theorem source_negationAtOutput {m} (w R S r s a b c d n x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationAtOutputSentence w R S r s a b c d n x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check false w x R S a b c d X) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxRenameRecursiveSyntax.check false w x R S a b c d X) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalConstruct.single_at_outputs hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S r s a b c d n x X h0 h1 h2 h3 h4 h5

theorem negationAtOutput_kernel_certificate {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationAtOutputSentence w R S r s a b c d n x X)) := TheoryTransport.sentence (source_negationAtOutput w R S r s a b c d n x X)

theorem native_negationAtOutput {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationAtOutputSentence w R S r s a b c d n x X)) := ZFReplay.replay (negationAtOutput_kernel_certificate w R S r s a b c d n x X)

def negationExistsAtGraphsSentence {m} (w R S r s a b c d n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n))))))).close

theorem source_negationExistsAtGraphs {m} (w R S r s a b c d n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationExistsAtGraphsSentence w R S r s a b c d n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalExistence.single_exists_at_graphs hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S r s a b c d n x h0 h1 h2 h3 h4 h5

theorem negationExistsAtGraphs_kernel_certificate {m} (w R S r s a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationExistsAtGraphsSentence w R S r s a b c d n x)) := TheoryTransport.sentence (source_negationExistsAtGraphs w R S r s a b c d n x)

theorem native_negationExistsAtGraphs {m} (w R S r s a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationExistsAtGraphsSentence w R S r s a b c d n x)) := ZFReplay.replay (negationExistsAtGraphs_kernel_certificate w R S r s a b c d n x)

def negationFiberSentence {m} (w R S a b c d n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n))))).close

theorem source_negationFiber {m} (w R S a b c d n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationFiberSentence w R S a b c d n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalOutput.single_fiber hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S a b c d n x h0 h1 h2 h3

theorem negationFiber_kernel_certificate {m} (w R S a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationFiberSentence w R S a b c d n x)) := TheoryTransport.sentence (source_negationFiber w R S a b c d n x)

theorem native_negationFiber {m} (w R S a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationFiberSentence w R S a b c d n x)) := ZFReplay.replay (negationFiber_kernel_certificate w R S a b c d n x)

def negationPropertyStepSentence {m} (w n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp (SyntaxRenameOutputSyntax.property w n)))).close

theorem source_negationPropertyStep {m} (w n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationPropertyStepSentence w n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalOutput.single_property_step hZ 4 false (Or.inl ⟨rfl, rfl⟩) w n x h0 h1 h2

theorem negationPropertyStep_kernel_certificate {m} (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationPropertyStepSentence w n x)) := TheoryTransport.sentence (source_negationPropertyStep w n x)

theorem native_negationPropertyStep {m} (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationPropertyStepSentence w n x)) := ZFReplay.replay (negationPropertyStep_kernel_certificate w n x)

def forallAtOutputSentence {m} (w R S r s a b c d n x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxRenameRecursiveSyntax.check true w x R S a b c d X).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n))))))).close

theorem source_forallAtOutput {m} (w R S r s a b c d n x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallAtOutputSentence w R S r s a b c d n x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalConstruct.single_at_outputs hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w R S r s a b c d n x X h0 h1 h2 h3 h4 h5

theorem forallAtOutput_kernel_certificate {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallAtOutputSentence w R S r s a b c d n x X)) := TheoryTransport.sentence (source_forallAtOutput w R S r s a b c d n x X)

theorem native_forallAtOutput {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallAtOutputSentence w R S r s a b c d n x X)) := ZFReplay.replay (forallAtOutput_kernel_certificate w R S r s a b c d n x X)

def forallExistsAtGraphsSentence {m} (w R S r s a b c d n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n))))))).close

theorem source_forallExistsAtGraphs {m} (w R S r s a b c d n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallExistsAtGraphsSentence w R S r s a b c d n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalExistence.single_exists_at_graphs hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w R S r s a b c d n x h0 h1 h2 h3 h4 h5

theorem forallExistsAtGraphs_kernel_certificate {m} (w R S r s a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallExistsAtGraphsSentence w R S r s a b c d n x)) := TheoryTransport.sentence (source_forallExistsAtGraphs w R S r s a b c d n x)

theorem native_forallExistsAtGraphs {m} (w R S r s a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallExistsAtGraphsSentence w R S r s a b c d n x)) := ZFReplay.replay (forallExistsAtGraphs_kernel_certificate w R S r s a b c d n x)

def forallFiberSentence {m} (w R S a b c d n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n))))).close

theorem source_forallFiber {m} (w R S a b c d n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallFiberSentence w R S a b c d n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalOutput.single_fiber hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w R S a b c d n x h0 h1 h2 h3

theorem forallFiber_kernel_certificate {m} (w R S a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallFiberSentence w R S a b c d n x)) := TheoryTransport.sentence (source_forallFiber w R S a b c d n x)

theorem native_forallFiber {m} (w R S a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallFiberSentence w R S a b c d n x)) := ZFReplay.replay (forallFiber_kernel_certificate w R S a b c d n x)

def forallPropertyStepSentence {m} (w n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp (SyntaxRenameOutputSyntax.property w n)))).close

theorem source_forallPropertyStep {m} (w n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallPropertyStepSentence w n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalOutput.single_property_step hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w n x h0 h1 h2

theorem forallPropertyStep_kernel_certificate {m} (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallPropertyStepSentence w n x)) := TheoryTransport.sentence (source_forallPropertyStep w n x)

theorem native_forallPropertyStep {m} (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallPropertyStepSentence w n x)) := ZFReplay.replay (forallPropertyStep_kernel_certificate w n x)

def existsAtOutputSentence {m} (w R S r s a b c d n x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxRenameRecursiveSyntax.check true w x R S a b c d X).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n))))))).close

theorem source_existsAtOutput {m} (w R S r s a b c d n x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsAtOutputSentence w R S r s a b c d n x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalConstruct.single_at_outputs hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w R S r s a b c d n x X h0 h1 h2 h3 h4 h5

theorem existsAtOutput_kernel_certificate {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsAtOutputSentence w R S r s a b c d n x X)) := TheoryTransport.sentence (source_existsAtOutput w R S r s a b c d n x X)

theorem native_existsAtOutput {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsAtOutputSentence w R S r s a b c d n x X)) := ZFReplay.replay (existsAtOutput_kernel_certificate w R S r s a b c d n x X)

def existsExistsAtGraphsSentence {m} (w R S r s a b c d n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n))))))).close

theorem source_existsExistsAtGraphs {m} (w R S r s a b c d n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsExistsAtGraphsSentence w R S r s a b c d n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalExistence.single_exists_at_graphs hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w R S r s a b c d n x h0 h1 h2 h3 h4 h5

theorem existsExistsAtGraphs_kernel_certificate {m} (w R S r s a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsExistsAtGraphsSentence w R S r s a b c d n x)) := TheoryTransport.sentence (source_existsExistsAtGraphs w R S r s a b c d n x)

theorem native_existsExistsAtGraphs {m} (w R S r s a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsExistsAtGraphsSentence w R S r s a b c d n x)) := ZFReplay.replay (existsExistsAtGraphs_kernel_certificate w R S r s a b c d n x)

def existsFiberSentence {m} (w R S a b c d n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n))))).close

theorem source_existsFiber {m} (w R S a b c d n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsFiberSentence w R S a b c d n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalOutput.single_fiber hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w R S a b c d n x h0 h1 h2 h3

theorem existsFiber_kernel_certificate {m} (w R S a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsFiberSentence w R S a b c d n x)) := TheoryTransport.sentence (source_existsFiber w R S a b c d n x)

theorem native_existsFiber {m} (w R S a b c d n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsFiberSentence w R S a b c d n x)) := ZFReplay.replay (existsFiber_kernel_certificate w R S a b c d n x)

def existsPropertyStepSentence {m} (w n x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp (SyntaxRenameOutputSyntax.property w n)))).close

theorem source_existsPropertyStep {m} (w n x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsPropertyStepSentence w n x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalOutput.single_property_step hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w n x h0 h1 h2

theorem existsPropertyStep_kernel_certificate {m} (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsPropertyStepSentence w n x)) := TheoryTransport.sentence (source_existsPropertyStep w n x)

theorem native_existsPropertyStep {m} (w n x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsPropertyStepSentence w n x)) := ZFReplay.replay (existsPropertyStep_kernel_certificate w n x)

def binaryAtOutputsSentence {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n)))))))).close

theorem source_binaryAtOutputs {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryAtOutputsSentence kind w R S r s a b c d n x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalConstruct.binary_at_outputs hZ kind w R S r s a b c d n x y X Y h0 h1 h2 h3 h4 h5 h6

theorem binaryAtOutputs_kernel_certificate {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryAtOutputsSentence kind w R S r s a b c d n x y X Y)) := TheoryTransport.sentence (source_binaryAtOutputs kind w R S r s a b c d n x y X Y)

theorem native_binaryAtOutputs {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryAtOutputsSentence kind w R S r s a b c d n x y X Y)) := ZFReplay.replay (binaryAtOutputs_kernel_certificate kind w R S r s a b c d n x y X Y)

def binaryExistsAtGraphsSentence {m} (kind : Fin 4) (w R S r s a b c d n x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n))))))).close

theorem source_binaryExistsAtGraphs {m} (kind : Fin 4) (w R S r s a b c d n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryExistsAtGraphsSentence kind w R S r s a b c d n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalExistence.binary_exists_at_graphs hZ kind w R S r s a b c d n x y h0 h1 h2 h3 h4 h5

theorem binaryExistsAtGraphs_kernel_certificate {m} (kind : Fin 4) (w R S r s a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryExistsAtGraphsSentence kind w R S r s a b c d n x y)) := TheoryTransport.sentence (source_binaryExistsAtGraphs kind w R S r s a b c d n x y)

theorem native_binaryExistsAtGraphs {m} (kind : Fin 4) (w R S r s a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryExistsAtGraphsSentence kind w R S r s a b c d n x y)) := ZFReplay.replay (binaryExistsAtGraphs_kernel_certificate kind w R S r s a b c d n x y)

def binaryFiberSentence {m} (kind : Fin 4) (w R S a b c d n x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n))))).close

theorem source_binaryFiber {m} (kind : Fin 4) (w R S a b c d n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryFiberSentence kind w R S a b c d n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalOutput.binary_fiber hZ kind w R S a b c d n x y h0 h1 h2 h3

theorem binaryFiber_kernel_certificate {m} (kind : Fin 4) (w R S a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryFiberSentence kind w R S a b c d n x y)) := TheoryTransport.sentence (source_binaryFiber kind w R S a b c d n x y)

theorem native_binaryFiber {m} (kind : Fin 4) (w R S a b c d n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryFiberSentence kind w R S a b c d n x y)) := ZFReplay.replay (binaryFiber_kernel_certificate kind w R S a b c d n x y)

def binaryPropertyStepSentence {m} (kind : Fin 4) (w n x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp (SyntaxRenameOutputSyntax.property w n)))).close

theorem source_binaryPropertyStep {m} (kind : Fin 4) (w n x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryPropertyStepSentence kind w n x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact SyntaxRenameLogicalOutput.binary_property_step hZ kind w n x y h0 h1 h2

theorem binaryPropertyStep_kernel_certificate {m} (kind : Fin 4) (w n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryPropertyStepSentence kind w n x y)) := TheoryTransport.sentence (source_binaryPropertyStep kind w n x y)

theorem native_binaryPropertyStep {m} (kind : Fin 4) (w n x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryPropertyStepSentence kind w n x y)) := ZFReplay.replay (binaryPropertyStep_kernel_certificate kind w n x y)

def codePropertyStepSentence {m} (w n b f : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp ((FormulaCodeSyntax.formulaCode w n b f).imp (SyntaxRenameOutputSyntax.property w n)))).close

theorem source_codePropertyStep {m} (w n b f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codePropertyStepSentence w n b f) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n b f) (Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (FormulaCodeSyntax.formulaCode w n b f) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputPoint.property_of_code hZ w n b f h0 h1 h2

theorem codePropertyStep_kernel_certificate {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codePropertyStepSentence w n b f)) := TheoryTransport.sentence (source_codePropertyStep w n b f)

theorem native_codePropertyStep {m} (w n b f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codePropertyStepSentence w n b f)) := ZFReplay.replay (codePropertyStep_kernel_certificate w n b f)

def propertyStepSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.earlier w n).imp (SyntaxRenameOutputSyntax.property w n))).close

theorem source_propertyStep {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (propertyStepSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOutputSyntax.earlier w n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.earlier w n) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputPoint.property_from_earlier hZ w n h0 h1

theorem propertyStep_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (propertyStepSentence w n)) := TheoryTransport.sentence (source_propertyStep w n)

theorem native_propertyStep {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (propertyStepSentence w n)) := ZFReplay.replay (propertyStep_kernel_certificate w n)

def progressiveSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp (BoundedInduction.progressive SyntaxRenameOutputInduction.matrix (fun _ : Fin 1 => w) w)).close

theorem source_progressive {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (progressiveSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputInduction.progressive hZ w h0

theorem progressive_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (progressiveSentence w)) := TheoryTransport.sentence (source_progressive w)

theorem native_progressive {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (progressiveSentence w)) := ZFReplay.replay (progressive_kernel_certificate w)

def allPropertiesSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp (Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (SyntaxRenameOutputSyntax.property w.castSucc (Fin.last m))))).close

theorem source_allProperties {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allPropertiesSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputInduction.all_properties hZ w h0

theorem allProperties_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allPropertiesSentence w)) := TheoryTransport.sentence (source_allProperties w)

theorem native_allProperties {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allPropertiesSentence w)) := ZFReplay.replay (allProperties_kernel_certificate w)

def naturalPropertySentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp (SyntaxRenameOutputSyntax.property w n))).close

theorem source_naturalProperty {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalPropertySentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputInduction.at_natural hZ w n h0 h1

theorem naturalProperty_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalPropertySentence w n)) := TheoryTransport.sentence (source_naturalProperty w n)

theorem native_naturalProperty {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalPropertySentence w n)) := ZFReplay.replay (naturalProperty_kernel_certificate w n)

def actualFiberSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp (SyntaxRenameOutputSyntax.fiber w R S a b c d n))).close

theorem source_actualFiber {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualFiberSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputInduction.actual_fiber hZ w R S a b c d n h0 h1

theorem actualFiber_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualFiberSentence w R S a b c d n)) := TheoryTransport.sentence (source_actualFiber w R S a b c d n)

theorem native_actualFiber {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualFiberSentence w R S a b c d n)) := ZFReplay.replay (actualFiber_kernel_certificate w R S a b c d n)

def actualExistsSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp (SyntaxRenameOutputSyntax.existsOutput w R S a b c d n))).close

theorem source_actualExists {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (actualExistsSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputInduction.actual_exists hZ w R S a b c d n h0 h1

theorem actualExists_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (actualExistsSentence w R S a b c d n)) := TheoryTransport.sentence (source_actualExists w R S a b c d n)

theorem native_actualExists {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (actualExistsSentence w R S a b c d n)) := ZFReplay.replay (actualExists_kernel_certificate w R S a b c d n)

def fiberIffInputSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.fiber w R S a b c d n).iff (SyntaxRenameOutputSyntax.input w R S a b c d n))).close

theorem source_fiberIffInput {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberIffInputSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputClassify.fiber_iff_input hZ w R S a b c d n h0

theorem fiberIffInput_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberIffInputSentence w R S a b c d n)) := TheoryTransport.sentence (source_fiberIffInput w R S a b c d n)

theorem native_fiberIffInput {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberIffInputSentence w R S a b c d n)) := ZFReplay.replay (fiberIffInput_kernel_certificate w R S a b c d n)

def existsIffInputSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.existsOutput w R S a b c d n).iff (SyntaxRenameOutputSyntax.input w R S a b c d n))).close

theorem source_existsIffInput {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsIffInputSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) ((Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputClassify.exists_iff_input hZ w R S a b c d n h0

theorem existsIffInput_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsIffInputSentence w R S a b c d n)) := TheoryTransport.sentence (source_existsIffInput w R S a b c d n)

theorem native_existsIffInput {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsIffInputSentence w R S a b c d n)) := ZFReplay.replay (existsIffInput_kernel_certificate w R S a b c d n)

def rejectInputSentence {m} (w R S a b c d n : Fin m) : Source.Sentence := ((omega w).imp (((SyntaxRenameOutputSyntax.input w R S a b c d n).neg).imp ((SyntaxRenameOutputSyntax.existsOutput w R S a b c d n).neg))).close

theorem source_rejectInput {m} (w R S a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectInputSentence w R S a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxRenameOutputSyntax.input w R S a b c d n).neg) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ ((SyntaxRenameOutputSyntax.input w R S a b c d n).neg) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputClassify.reject_input hZ w R S a b c d n h0 h1

theorem rejectInput_kernel_certificate {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectInputSentence w R S a b c d n)) := TheoryTransport.sentence (source_rejectInput w R S a b c d n)

theorem native_rejectInput {m} (w R S a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectInputSentence w R S a b c d n)) := ZFReplay.replay (rejectInput_kernel_certificate w R S a b c d n)

def uniqueSentence {m} (w R S a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v).imp (Formula.equal q v)))).close

theorem source_unique {m} (w R S a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueSentence w R S a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputInduction.unique hZ w R S a b c d n q v h0 h1 h2

theorem unique_kernel_certificate {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueSentence w R S a b c d n q v)) := TheoryTransport.sentence (source_unique w R S a b c d n q v)

theorem native_unique {m} (w R S a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueSentence w R S a b c d n q v)) := ZFReplay.replay (unique_kernel_certificate w R S a b c d n q v)

def uniqueOutputSentence {m} (w R S a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameOutputSyntax.uniqueOutput w R S a b c d n q))).close

theorem source_uniqueOutput {m} (w R S a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueOutputSentence w R S a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameOutputClassify.unique_output_of_renamed hZ w R S a b c d n q h0 h1

theorem uniqueOutput_kernel_certificate {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueOutputSentence w R S a b c d n q)) := TheoryTransport.sentence (source_uniqueOutput w R S a b c d n q)

theorem native_uniqueOutput {m} (w R S a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueOutputSentence w R S a b c d n q)) := ZFReplay.replay (uniqueOutput_kernel_certificate w R S a b c d n q)

end PPAC.Migration.Internal.ObjectSyntaxRenameTotal
