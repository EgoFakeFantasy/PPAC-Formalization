import PPAC.Migration.Internal.SyntaxRenameCodeFields

/-! 原11构造精确字段律及真实提升下量词体判断的源/原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxRenameFields
open Source SourceAlgebra SourceLogic OmegaSyntax

def introBranchSentence {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : Source.Sentence := ((SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q).imp (SyntaxRenameRecursiveSyntax.cases w R S r s a b c d n q)).close

theorem source_introBranch {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (introBranchSentence kind w R S r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameBranchIntro.intro_cases kind w R S r s a b c d n q h0

theorem introBranch_kernel_certificate {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (introBranchSentence kind w R S r s a b c d n q)) := TheoryTransport.sentence (source_introBranch kind w R S r s a b c d n q)

theorem native_introBranch {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (introBranchSentence kind w R S r s a b c d n q)) := ZFReplay.replay (introBranch_kernel_certificate kind w R S r s a b c d n q)

def branchTargetSentence {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q).imp (FormulaCodeSyntax.formulaCode w q c d)))).close

theorem source_branchTarget {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (branchTargetSentence kind w R S r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameCaseTyping.selected hZ kind w R S r s a b c d n q h0 h1 h2

theorem branchTarget_kernel_certificate {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (branchTargetSentence kind w R S r s a b c d n q)) := TheoryTransport.sentence (source_branchTarget kind w R S r s a b c d n q)

theorem native_branchTarget {m} (kind : Fin 11) (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (branchTargetSentence kind w R S r s a b c d n q)) := ZFReplay.replay (branchTarget_kernel_certificate kind w R S r s a b c d n q)

def sourceCaseIffSentence {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameOutputSyntax.input w R S a b c d n).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxNodeSyntax.constructor arity kind.val w xs n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameTagCases.tagBranch kind w R S r s a b c d n q))))))).close

theorem source_sourceCaseIff {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceCaseIffSentence kind arity w R S r s a b c d n q xs) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor arity kind.val w xs n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (SyntaxRenameOutputSyntax.input w R S a b c d n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxRenameOutputSyntax.input w R S a b c d n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxNodeSyntax.constructor arity kind.val w xs n) := .hyp (Or.inl rfl)
  exact SyntaxRenameSelectedIff.source_case hZ kind arity w R S r s a b c d n q xs h0 h1 h2 h3 h4

theorem sourceCaseIff_kernel_certificate {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceCaseIffSentence kind arity w R S r s a b c d n q xs)) := TheoryTransport.sentence (source_sourceCaseIff kind arity w R S r s a b c d n q xs)

theorem native_sourceCaseIff {m} (kind : Fin 11) (arity : Nat) (w R S r s a b c d n q : Fin m) (xs : Fin arity → Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceCaseIffSentence kind arity w R S r s a b c d n q xs)) := ZFReplay.replay (sourceCaseIff_kernel_certificate kind arity w R S r s a b c d n q xs)

def checkSourceSentence {m} (advance : Bool) (w x R S a b c d q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q).imp (FormulaCodeRecursiveSyntax.stepCheck advance w x a b))).close

theorem source_checkSource {m} (advance : Bool) (w x R S a b c d q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkSourceSentence advance w x R S a b c d q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d q) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownSource.check_source_type hZ advance w x R S a b c d q h0 h1

theorem checkSource_kernel_certificate {m} (advance : Bool) (w x R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkSourceSentence advance w x R S a b c d q)) := TheoryTransport.sentence (source_checkSource advance w x R S a b c d q)

theorem native_checkSource {m} (advance : Bool) (w x R S a b c d q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkSourceSentence advance w x R S a b c d q)) := ZFReplay.replay (checkSource_kernel_certificate advance w x R S a b c d q)

def equalityRawIffSentence {m} (w r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxAtomSyntax.equalCode w X Y q).imp ((SyntaxRenameAtomSyntax.equality w r s a b c d n q).iff (SyntaxRenameKnownFieldsSyntax.equalOperands w r s a b c d x y X Y))))).close

theorem source_equalityRawIff {m} (w r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityRawIffSentence w r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w X Y q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.equalCode w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxRenameRawFields.equality_iff hZ w r s a b c d n q x y X Y h0 h1 h2

theorem equalityRawIff_kernel_certificate {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityRawIffSentence w r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_equalityRawIff w r s a b c d n q x y X Y)

theorem native_equalityRawIff {m} (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityRawIffSentence w r s a b c d n q x y X Y)) := ZFReplay.replay (equalityRawIff_kernel_certificate w r s a b c d n q x y X Y)

def membershipRawIffSentence {m} (w r s a b c d n q z Z x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxAtomSyntax.memberCode w Z X Y q).imp ((SyntaxRenameAtomSyntax.membership w r s a b c d n q).iff (SyntaxRenameKnownFieldsSyntax.memberOperands w r s a b c d z Z x y X Y))))).close

theorem source_membershipRawIff {m} (w r s a b c d n q z Z x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipRawIffSentence w r s a b c d n q z Z x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w Z X Y q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxAtomSyntax.memberCode w Z X Y q) := .hyp (Or.inl rfl)
  exact SyntaxRenameRawFields.membership_iff hZ w r s a b c d n q z Z x y X Y h0 h1 h2

theorem membershipRawIff_kernel_certificate {m} (w r s a b c d n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipRawIffSentence w r s a b c d n q z Z x y X Y)) := TheoryTransport.sentence (source_membershipRawIff w r s a b c d n q z Z x y X Y)

theorem native_membershipRawIff {m} (w r s a b c d n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipRawIffSentence w r s a b c d n q z Z x y X Y)) := ZFReplay.replay (membershipRawIff_kernel_certificate w r s a b c d n q z Z x y X Y)

def singleRawIffSentence {m} (tag : Nat) (advance : Bool) (w r s a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxLogicalSyntax.singleCode tag w x n).imp ((SyntaxLogicalSyntax.singleCode tag w X q).imp ((SyntaxRenameRecursiveSyntax.single tag advance w r s a b c d n q).iff (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d X))))).close

theorem source_singleRawIff {m} (tag : Nat) (advance : Bool) (w r s a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (singleRawIffSentence tag advance w r s a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode tag w X q) (Context.add (SyntaxLogicalSyntax.singleCode tag w x n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxLogicalSyntax.singleCode tag w x n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxLogicalSyntax.singleCode tag w X q) := .hyp (Or.inl rfl)
  exact SyntaxRenameRawFields.single_iff hZ tag advance w r s a b c d n q x X h0 h1 h2

theorem singleRawIff_kernel_certificate {m} (tag : Nat) (advance : Bool) (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (singleRawIffSentence tag advance w r s a b c d n q x X)) := TheoryTransport.sentence (source_singleRawIff tag advance w r s a b c d n q x X)

theorem native_singleRawIff {m} (tag : Nat) (advance : Bool) (w r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (singleRawIffSentence tag advance w r s a b c d n q x X)) := ZFReplay.replay (singleRawIff_kernel_certificate tag advance w r s a b c d n q x X)

def binaryRawIffSentence {m} (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp ((SyntaxRenameRecursiveSyntax.binary kind w r s a b c d n q).iff ((SyntaxRenameJudgmentSyntax.renamed w r s a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w r s a b c d y Y)))))).close

theorem source_binaryRawIff {m} (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryRawIffSentence kind w r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxRenameRawFields.binary_iff hZ kind w r s a b c d n q x y X Y h0 h1 h2

theorem binaryRawIff_kernel_certificate {m} (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryRawIffSentence kind w r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_binaryRawIff kind w r s a b c d n q x y X Y)

theorem native_binaryRawIff {m} (kind : Fin 4) (w r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryRawIffSentence kind w r s a b c d n q x y X Y)) := ZFReplay.replay (binaryRawIff_kernel_certificate kind w r s a b c d n q x y X Y)

def equalityIffSentence {m} (w R S r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxAtomSyntax.equalCode w X Y q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameKnownFieldsSyntax.equalOperands w r s a b c d x y X Y))))))).close

theorem source_equalityIff {m} (w R S r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityIffSentence w R S r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w X Y q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.equalCode w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownFields.equality_iff hZ w R S r s a b c d n q x y X Y h0 h1 h2 h3 h4

theorem equalityIff_kernel_certificate {m} (w R S r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityIffSentence w R S r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_equalityIff w R S r s a b c d n q x y X Y)

theorem native_equalityIff {m} (w R S r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityIffSentence w R S r s a b c d n q x y X Y)) := ZFReplay.replay (equalityIff_kernel_certificate w R S r s a b c d n q x y X Y)

def equalityInputSentence {m} (w R S r s a b c d n x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxRenameKnownFieldsSyntax.equalOperands w r s a b c d x y X Y).imp (SyntaxRenameOutputSyntax.input w R S a b c d n)))))).close

theorem source_equalityInput {m} (w R S r s a b c d n x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityInputSentence w R S r s a b c d n x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameKnownFieldsSyntax.equalOperands w r s a b c d x y X Y) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameKnownFieldsSyntax.equalOperands w r s a b c d x y X Y) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownSource.equality_input hZ w R S r s a b c d n x y X Y h0 h1 h2 h3 h4

theorem equalityInput_kernel_certificate {m} (w R S r s a b c d n x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityInputSentence w R S r s a b c d n x y X Y)) := TheoryTransport.sentence (source_equalityInput w R S r s a b c d n x y X Y)

theorem native_equalityInput {m} (w R S r s a b c d n x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityInputSentence w R S r s a b c d n x y X Y)) := ZFReplay.replay (equalityInput_kernel_certificate w R S r s a b c d n x y X Y)

def membershipIffSentence {m} (w R S r s a b c d n q z Z x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxAtomSyntax.memberCode w Z X Y q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameKnownFieldsSyntax.memberOperands w r s a b c d z Z x y X Y))))))).close

theorem source_membershipIff {m} (w R S r s a b c d n q z Z x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipIffSentence w R S r s a b c d n q z Z x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w Z X Y q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.memberCode w Z X Y q) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownFields.membership_iff hZ w R S r s a b c d n q z Z x y X Y h0 h1 h2 h3 h4

theorem membershipIff_kernel_certificate {m} (w R S r s a b c d n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipIffSentence w R S r s a b c d n q z Z x y X Y)) := TheoryTransport.sentence (source_membershipIff w R S r s a b c d n q z Z x y X Y)

theorem native_membershipIff {m} (w R S r s a b c d n q z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipIffSentence w R S r s a b c d n q z Z x y X Y)) := ZFReplay.replay (membershipIff_kernel_certificate w R S r s a b c d n q z Z x y X Y)

def membershipInputSentence {m} (w R S r s a b c d n z Z x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxRenameKnownFieldsSyntax.memberOperands w r s a b c d z Z x y X Y).imp (SyntaxRenameOutputSyntax.input w R S a b c d n)))))).close

theorem source_membershipInput {m} (w R S r s a b c d n z Z x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipInputSentence w R S r s a b c d n z Z x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameKnownFieldsSyntax.memberOperands w r s a b c d z Z x y X Y) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameKnownFieldsSyntax.memberOperands w r s a b c d z Z x y X Y) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownSource.membership_input hZ w R S r s a b c d n z Z x y X Y h0 h1 h2 h3 h4

theorem membershipInput_kernel_certificate {m} (w R S r s a b c d n z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipInputSentence w R S r s a b c d n z Z x y X Y)) := TheoryTransport.sentence (source_membershipInput w R S r s a b c d n z Z x y X Y)

theorem native_membershipInput {m} (w R S r s a b c d n z Z x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipInputSentence w R S r s a b c d n z Z x y X Y)) := ZFReplay.replay (membershipInput_kernel_certificate w R S r s a b c d n z Z x y X Y)

def negationIffSentence {m} (w R S r s a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.check false w x R S a b c d X))))))).close

theorem source_negationIff {m} (w R S r s a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationIffSentence w R S r s a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownFields.single_iff hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S r s a b c d n q x X h0 h1 h2 h3 h4

theorem negationIff_kernel_certificate {m} (w R S r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationIffSentence w R S r s a b c d n q x X)) := TheoryTransport.sentence (source_negationIff w R S r s a b c d n q x X)

theorem native_negationIff {m} (w R S r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationIffSentence w R S r s a b c d n q x X)) := ZFReplay.replay (negationIff_kernel_certificate w R S r s a b c d n q x X)

def negationCodeIffSentence {m} (w R S a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w a c R).imp ((SyntaxMapCodeSyntax.mapCode w b d S).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.check false w x R S a b c d X))))))).close

theorem source_negationCodeIff {m} (w R S a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationCodeIffSentence w R S a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxMapCodeSyntax.mapCode w b d S) (Context.add (SyntaxMapCodeSyntax.mapCode w a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.mapCode w b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inl rfl)
  exact SyntaxRenameCodeFields.single_iff hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S a b c d n q x X h0 h1 h2 h3 h4

theorem negationCodeIff_kernel_certificate {m} (w R S a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationCodeIffSentence w R S a b c d n q x X)) := TheoryTransport.sentence (source_negationCodeIff w R S a b c d n q x X)

theorem native_negationCodeIff {m} (w R S a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationCodeIffSentence w R S a b c d n q x X)) := ZFReplay.replay (negationCodeIff_kernel_certificate w R S a b c d n q x X)

def negationInputSentence {m} (w R S r s a b c d n x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxRenameRecursiveSyntax.check false w x R S a b c d X).imp (SyntaxRenameOutputSyntax.input w R S a b c d n)))))).close

theorem source_negationInput {m} (w R S r s a b c d n x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationInputSentence w R S r s a b c d n x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check false w x R S a b c d X) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameRecursiveSyntax.check false w x R S a b c d X) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownSource.single_input hZ 4 false (Or.inl ⟨rfl, rfl⟩) w R S r s a b c d n x X h0 h1 h2 h3 h4

theorem negationInput_kernel_certificate {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationInputSentence w R S r s a b c d n x X)) := TheoryTransport.sentence (source_negationInput w R S r s a b c d n x X)

theorem native_negationInput {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationInputSentence w R S r s a b c d n x X)) := ZFReplay.replay (negationInput_kernel_certificate w R S r s a b c d n x X)

def forallIffSentence {m} (w R S r s a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxLogicalSyntax.singleCode 9 w X q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X))))))).close

theorem source_forallIff {m} (w R S r s a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallIffSentence w R S r s a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w X q) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownFields.single_iff hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w R S r s a b c d n q x X h0 h1 h2 h3 h4

theorem forallIff_kernel_certificate {m} (w R S r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallIffSentence w R S r s a b c d n q x X)) := TheoryTransport.sentence (source_forallIff w R S r s a b c d n q x X)

theorem native_forallIff {m} (w R S r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallIffSentence w R S r s a b c d n q x X)) := ZFReplay.replay (forallIff_kernel_certificate w R S r s a b c d n q x X)

def forallCodeIffSentence {m} (w R S a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w a c R).imp ((SyntaxMapCodeSyntax.mapCode w b d S).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxLogicalSyntax.singleCode 9 w X q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X))))))).close

theorem source_forallCodeIff {m} (w R S a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallCodeIffSentence w R S a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxMapCodeSyntax.mapCode w b d S) (Context.add (SyntaxMapCodeSyntax.mapCode w a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.mapCode w b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w X q) := .hyp (Or.inl rfl)
  exact SyntaxRenameCodeFields.single_iff hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w R S a b c d n q x X h0 h1 h2 h3 h4

theorem forallCodeIff_kernel_certificate {m} (w R S a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallCodeIffSentence w R S a b c d n q x X)) := TheoryTransport.sentence (source_forallCodeIff w R S a b c d n q x X)

theorem native_forallCodeIff {m} (w R S a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallCodeIffSentence w R S a b c d n q x X)) := ZFReplay.replay (forallCodeIff_kernel_certificate w R S a b c d n q x X)

def forallInputSentence {m} (w R S r s a b c d n x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxRenameRecursiveSyntax.check true w x R S a b c d X).imp (SyntaxRenameOutputSyntax.input w R S a b c d n)))))).close

theorem source_forallInput {m} (w R S r s a b c d n x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallInputSentence w R S r s a b c d n x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownSource.single_input hZ 9 true (Or.inr (Or.inl ⟨rfl, rfl⟩)) w R S r s a b c d n x X h0 h1 h2 h3 h4

theorem forallInput_kernel_certificate {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallInputSentence w R S r s a b c d n x X)) := TheoryTransport.sentence (source_forallInput w R S r s a b c d n x X)

theorem native_forallInput {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallInputSentence w R S r s a b c d n x X)) := ZFReplay.replay (forallInput_kernel_certificate w R S r s a b c d n x X)

def existsIffSentence {m} (w R S r s a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxLogicalSyntax.singleCode 10 w X q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X))))))).close

theorem source_existsIff {m} (w R S r s a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsIffSentence w R S r s a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w X q) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownFields.single_iff hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w R S r s a b c d n q x X h0 h1 h2 h3 h4

theorem existsIff_kernel_certificate {m} (w R S r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsIffSentence w R S r s a b c d n q x X)) := TheoryTransport.sentence (source_existsIff w R S r s a b c d n q x X)

theorem native_existsIff {m} (w R S r s a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsIffSentence w R S r s a b c d n q x X)) := ZFReplay.replay (existsIff_kernel_certificate w R S r s a b c d n q x X)

def existsCodeIffSentence {m} (w R S a b c d n q x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w a c R).imp ((SyntaxMapCodeSyntax.mapCode w b d S).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxLogicalSyntax.singleCode 10 w X q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X))))))).close

theorem source_existsCodeIff {m} (w R S a b c d n q x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsCodeIffSentence w R S a b c d n q x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxMapCodeSyntax.mapCode w b d S) (Context.add (SyntaxMapCodeSyntax.mapCode w a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.mapCode w b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w X q) := .hyp (Or.inl rfl)
  exact SyntaxRenameCodeFields.single_iff hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w R S a b c d n q x X h0 h1 h2 h3 h4

theorem existsCodeIff_kernel_certificate {m} (w R S a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsCodeIffSentence w R S a b c d n q x X)) := TheoryTransport.sentence (source_existsCodeIff w R S a b c d n q x X)

theorem native_existsCodeIff {m} (w R S a b c d n q x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsCodeIffSentence w R S a b c d n q x X)) := ZFReplay.replay (existsCodeIff_kernel_certificate w R S a b c d n q x X)

def existsInputSentence {m} (w R S r s a b c d n x X : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxRenameRecursiveSyntax.check true w x R S a b c d X).imp (SyntaxRenameOutputSyntax.input w R S a b c d n)))))).close

theorem source_existsInput {m} (w R S r s a b c d n x X : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsInputSentence w R S r s a b c d n x X) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameRecursiveSyntax.check true w x R S a b c d X) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownSource.single_input hZ 10 true (Or.inr (Or.inr ⟨rfl, rfl⟩)) w R S r s a b c d n x X h0 h1 h2 h3 h4

theorem existsInput_kernel_certificate {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsInputSentence w R S r s a b c d n x X)) := TheoryTransport.sentence (source_existsInput w R S r s a b c d n x X)

theorem native_existsInput {m} (w R S r s a b c d n x X : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsInputSentence w R S r s a b c d n x X)) := ZFReplay.replay (existsInput_kernel_certificate w R S r s a b c d n x X)

def binaryIffSentence {m} (kind : Fin 4) (w R S r s a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y)))))))).close

theorem source_binaryIff {m} (kind : Fin 4) (w R S r s a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryIffSentence kind w R S r s a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownFields.binary_iff hZ kind w R S r s a b c d n q x y X Y h0 h1 h2 h3 h4

theorem binaryIff_kernel_certificate {m} (kind : Fin 4) (w R S r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryIffSentence kind w R S r s a b c d n q x y X Y)) := TheoryTransport.sentence (source_binaryIff kind w R S r s a b c d n q x y X Y)

theorem native_binaryIff {m} (kind : Fin 4) (w R S r s a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryIffSentence kind w R S r s a b c d n q x y X Y)) := ZFReplay.replay (binaryIff_kernel_certificate kind w R S r s a b c d n q x y X Y)

def binaryCodeIffSentence {m} (kind : Fin 4) (w R S a b c d n q x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w a c R).imp ((SyntaxMapCodeSyntax.mapCode w b d S).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y)))))))).close

theorem source_binaryCodeIff {m} (kind : Fin 4) (w R S a b c d n q x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryCodeIffSentence kind w R S a b c d n q x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxMapCodeSyntax.mapCode w b d S) (Context.add (SyntaxMapCodeSyntax.mapCode w a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w a c R) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.mapCode w b d S) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inl rfl)
  exact SyntaxRenameCodeFields.binary_iff hZ kind w R S a b c d n q x y X Y h0 h1 h2 h3 h4

theorem binaryCodeIff_kernel_certificate {m} (kind : Fin 4) (w R S a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryCodeIffSentence kind w R S a b c d n q x y X Y)) := TheoryTransport.sentence (source_binaryCodeIff kind w R S a b c d n q x y X Y)

theorem native_binaryCodeIff {m} (kind : Fin 4) (w R S a b c d n q x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryCodeIffSentence kind w R S a b c d n q x y X Y)) := ZFReplay.replay (binaryCodeIff_kernel_certificate kind w R S a b c d n q x y X Y)

def binaryInputSentence {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp (((SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y)).imp (SyntaxRenameOutputSyntax.input w R S a b c d n)))))).close

theorem source_binaryInput {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryInputSentence kind w R S r s a b c d n x y X Y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y)) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
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
  have h3 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d x X).conj (SyntaxRenameJudgmentSyntax.renamed w R S a b c d y Y)) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownSource.binary_input hZ kind w R S r s a b c d n x y X Y h0 h1 h2 h3 h4

theorem binaryInput_kernel_certificate {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryInputSentence kind w R S r s a b c d n x y X Y)) := TheoryTransport.sentence (source_binaryInput kind w R S r s a b c d n x y X Y)

theorem native_binaryInput {m} (kind : Fin 4) (w R S r s a b c d n x y X Y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryInputSentence kind w R S r s a b c d n x y X Y)) := ZFReplay.replay (binaryInput_kernel_certificate kind w R S r s a b c d n x y X Y)

def nullaryIffSentence {m} (truth : Bool) (w R S r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (.equal n q)))))).close

theorem source_nullaryIff {m} (truth : Bool) (w R S r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullaryIffSentence truth w R S r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.encoded w r a c R) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxMapCodeSyntax.encoded w s b d S) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxRenameKnownFields.nullary_iff hZ truth w R S r s a b c d n q h0 h1 h2 h3

theorem nullaryIff_kernel_certificate {m} (truth : Bool) (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullaryIffSentence truth w R S r s a b c d n q)) := TheoryTransport.sentence (source_nullaryIff truth w R S r s a b c d n q)

theorem native_nullaryIff {m} (truth : Bool) (w R S r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullaryIffSentence truth w R S r s a b c d n q)) := ZFReplay.replay (nullaryIff_kernel_certificate truth w R S r s a b c d n q)

def quantifiedAtLiftSentence {m} (universal : Bool) (w R S a b c d n q x X u v l : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.mapCode w b d S).imp ((SyntaxMapLiftSyntax.codedLift w a c R u v l).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n).imp ((SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).iff (SyntaxRenameJudgmentSyntax.renamed w l S u b v d x X))))))).close

theorem source_quantifiedAtLift {m} (universal : Bool) (w R S a b c d n q x X u v l : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (quantifiedAtLiftSentence universal w R S a b c d n q x X u v l) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) (Context.add (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) (Context.add (SyntaxMapLiftSyntax.codedLift w a c R u v l) (Context.add (SyntaxMapCodeSyntax.mapCode w b d S) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxMapCodeSyntax.mapCode w b d S) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxMapLiftSyntax.codedLift w a c R u v l) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w X q) := .hyp (Or.inl rfl)
  exact SyntaxRenameCodeFields.quantified_at_lift hZ universal w R S a b c d n q x X u v l h0 h1 h2 h3 h4

theorem quantifiedAtLift_kernel_certificate {m} (universal : Bool) (w R S a b c d n q x X u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (quantifiedAtLiftSentence universal w R S a b c d n q x X u v l)) := TheoryTransport.sentence (source_quantifiedAtLift universal w R S a b c d n q x X u v l)

theorem native_quantifiedAtLift {m} (universal : Bool) (w R S a b c d n q x X u v l : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (quantifiedAtLiftSentence universal w R S a b c d n q x X u v l)) := ZFReplay.replay (quantifiedAtLift_kernel_certificate universal w R S a b c d n q x X u v l)

end PPAC.Migration.Internal.ObjectSyntaxRenameFields
