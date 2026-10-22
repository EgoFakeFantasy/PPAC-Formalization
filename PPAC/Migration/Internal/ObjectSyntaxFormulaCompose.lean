import PPAC.Migration.Internal.SyntaxFormulaComposeFactor

/-! 全11构造与14内部参数公式复合、原归纳关闭及实际中间码双条件的源/YesMetaZFC原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxFormulaCompose
open Source SourceAlgebra SourceLogic OmegaSyntax

def targetNegationSentence {m} (w R S r s a b c d n q x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameTargetFields.singleTarget 4 w q)))))).close

theorem source_targetNegation {m} (w R S r s a b c d n q x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetNegationSentence w R S r s a b c d n q x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTargetFields.single hZ 4 false (Or.inl ⟨rfl,rfl⟩) w R S r s a b c d n q x h0 h1 h2 h3 h4

theorem targetNegation_kernel_certificate {m} (w R S r s a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetNegationSentence w R S r s a b c d n q x)) := TheoryTransport.sentence (source_targetNegation w R S r s a b c d n q x)

theorem native_targetNegation {m} (w R S r s a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetNegationSentence w R S r s a b c d n q x)) := ZFReplay.replay (targetNegation_kernel_certificate w R S r s a b c d n q x)

def targetForallSentence {m} (w R S r s a b c d n q x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameTargetFields.singleTarget 9 w q)))))).close

theorem source_targetForall {m} (w R S r s a b c d n q x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetForallSentence w R S r s a b c d n q x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTargetFields.single hZ 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩)) w R S r s a b c d n q x h0 h1 h2 h3 h4

theorem targetForall_kernel_certificate {m} (w R S r s a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetForallSentence w R S r s a b c d n q x)) := TheoryTransport.sentence (source_targetForall w R S r s a b c d n q x)

theorem native_targetForall {m} (w R S r s a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetForallSentence w R S r s a b c d n q x)) := ZFReplay.replay (targetForall_kernel_certificate w R S r s a b c d n q x)

def targetExistsSentence {m} (w R S r s a b c d n q x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameTargetFields.singleTarget 10 w q)))))).close

theorem source_targetExists {m} (w R S r s a b c d n q x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetExistsSentence w R S r s a b c d n q x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTargetFields.single hZ 10 true (Or.inr (Or.inr ⟨rfl,rfl⟩)) w R S r s a b c d n q x h0 h1 h2 h3 h4

theorem targetExists_kernel_certificate {m} (w R S r s a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetExistsSentence w R S r s a b c d n q x)) := TheoryTransport.sentence (source_targetExists w R S r s a b c d n q x)

theorem native_targetExists {m} (w R S r s a b c d n q x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetExistsSentence w R S r s a b c d n q x)) := ZFReplay.replay (targetExists_kernel_certificate w R S r s a b c d n q x)

def targetBinarySentence {m} (kind : Fin 4) (w R S r s a b c d n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameTargetFields.binaryTarget kind w q)))))).close

theorem source_targetBinary {m} (kind : Fin 4) (w R S r s a b c d n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetBinarySentence kind w R S r s a b c d n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTargetFields.binary hZ kind w R S r s a b c d n q x y h0 h1 h2 h3 h4

theorem targetBinary_kernel_certificate {m} (kind : Fin 4) (w R S r s a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetBinarySentence kind w R S r s a b c d n q x y)) := TheoryTransport.sentence (source_targetBinary kind w R S r s a b c d n q x y)

theorem native_targetBinary {m} (kind : Fin 4) (w R S r s a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetBinarySentence kind w R S r s a b c d n q x y)) := ZFReplay.replay (targetBinary_kernel_certificate kind w R S r s a b c d n q x y)

def targetEqualitySentence {m} (w R S r s a b c d n q x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameTargetFields.equalTarget w q)))))).close

theorem source_targetEquality {m} (w R S r s a b c d n q x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetEqualitySentence w R S r s a b c d n q x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTargetFields.equality hZ w R S r s a b c d n q x y h0 h1 h2 h3 h4

theorem targetEquality_kernel_certificate {m} (w R S r s a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetEqualitySentence w R S r s a b c d n q x y)) := TheoryTransport.sentence (source_targetEquality w R S r s a b c d n q x y)

theorem native_targetEquality {m} (w R S r s a b c d n q x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetEqualitySentence w R S r s a b c d n q x y)) := ZFReplay.replay (targetEquality_kernel_certificate w R S r s a b c d n q x y)

def targetMembershipSentence {m} (w R S r s a b c d n q z x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxMapCodeSyntax.encoded w r a c R).imp ((SyntaxMapCodeSyntax.encoded w s b d S).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp (SyntaxRenameTargetFields.memberTarget w q)))))).close

theorem source_targetMembership {m} (w R S r s a b c d n q z x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetMembershipSentence w R S r s a b c d n q z x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxMapCodeSyntax.encoded w s b d S) (Context.add (SyntaxMapCodeSyntax.encoded w r a c R) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
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
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTargetFields.membership hZ w R S r s a b c d n q z x y h0 h1 h2 h3 h4

theorem targetMembership_kernel_certificate {m} (w R S r s a b c d n q z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetMembershipSentence w R S r s a b c d n q z x y)) := TheoryTransport.sentence (source_targetMembership w R S r s a b c d n q z x y)

theorem native_targetMembership {m} (w R S r s a b c d n q z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetMembershipSentence w R S r s a b c d n q z x y)) := ZFReplay.replay (targetMembership_kernel_certificate w R S r s a b c d n q z x y)

def boundDiagramCodeSentence {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : Source.Sentence := ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp (SyntaxComposeCodeSyntax.coded w a c e R T K)).close

theorem source_boundDiagramCode {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (boundDiagramCodeSentence w R S T U K L r s t u g h a b c d e f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeDiagrams.bound_code w R S T U K L r s t u g h a b c d e f h0

theorem boundDiagramCode_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (boundDiagramCodeSentence w R S T U K L r s t u g h a b c d e f)) := TheoryTransport.sentence (source_boundDiagramCode w R S T U K L r s t u g h a b c d e f)

theorem native_boundDiagramCode {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (boundDiagramCodeSentence w R S T U K L r s t u g h a b c d e f)) := ZFReplay.replay (boundDiagramCode_kernel_certificate w R S T U K L r s t u g h a b c d e f)

def freeDiagramCodeSentence {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : Source.Sentence := ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp (SyntaxComposeCodeSyntax.coded w b d f S U L)).close

theorem source_freeDiagramCode {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (freeDiagramCodeSentence w R S T U K L r s t u g h a b c d e f) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeDiagrams.free_code w R S T U K L r s t u g h a b c d e f h0

theorem freeDiagramCode_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (freeDiagramCodeSentence w R S T U K L r s t u g h a b c d e f)) := TheoryTransport.sentence (source_freeDiagramCode w R S T U K L r s t u g h a b c d e f)

theorem native_freeDiagramCode {m} (w R S T U K L r s t u g h a b c d e f : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (freeDiagramCodeSentence w R S T U K L r s t u g h a b c d e f)) := ZFReplay.replay (freeDiagramCode_kernel_certificate w R S T U K L r s t u g h a b c d e f)

def nullarySentence {m} (truth : Bool) (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))).close

theorem source_nullary {m} (truth : Bool) (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (nullarySentence truth w R S T U K L r s t u g h a b c d e f n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeAtomFields.nullary hZ truth w R S T U K L r s t u g h a b c d e f n q v h0 h1 h2 h3 h4

theorem nullary_kernel_certificate {m} (truth : Bool) (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (nullarySentence truth w R S T U K L r s t u g h a b c d e f n q v)) := TheoryTransport.sentence (source_nullary truth w R S T U K L r s t u g h a b c d e f n q v)

theorem native_nullary {m} (truth : Bool) (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (nullarySentence truth w R S T U K L r s t u g h a b c d e f n q v)) := ZFReplay.replay (nullary_kernel_certificate truth w R S T U K L r s t u g h a b c d e f n q v)

def equalityFieldsSentence {m} (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxAtomSyntax.equalCode w x y n).imp ((SyntaxAtomSyntax.equalCode w X Y q).imp ((SyntaxAtomSyntax.equalCode w Z W v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))))).close

theorem source_equalityFields {m} (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalityFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w Z W v) (Context.add (SyntaxAtomSyntax.equalCode w X Y q) (Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxAtomSyntax.equalCode w X Y q) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxAtomSyntax.equalCode w Z W v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeAtomFields.equality hZ w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W h0 h1 h2 h3 h4 h5 h6

theorem equalityFields_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalityFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)) := TheoryTransport.sentence (source_equalityFields w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)

theorem native_equalityFields {m} (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalityFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)) := ZFReplay.replay (equalityFields_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)

def membershipFieldsSentence {m} (w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp ((SyntaxAtomSyntax.memberCode w z1 X Y q).imp ((SyntaxAtomSyntax.memberCode w z2 Z W v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))))).close

theorem source_membershipFields {m} (w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipFieldsSentence w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w z2 Z W v) (Context.add (SyntaxAtomSyntax.memberCode w z1 X Y q) (Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxAtomSyntax.memberCode w z1 X Y q) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxAtomSyntax.memberCode w z2 Z W v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeAtomFields.membership hZ w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W h0 h1 h2 h3 h4 h5 h6

theorem membershipFields_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipFieldsSentence w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W)) := TheoryTransport.sentence (source_membershipFields w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W)

theorem native_membershipFields {m} (w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipFieldsSentence w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W)) := ZFReplay.replay (membershipFields_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W)

def equalitySentence {m} (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxAtomSyntax.equalCode w x y n).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))).close

theorem source_equality {m} (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (equalitySentence w R S T U K L r s t u g h a b c d e f n q v x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.equalCode w x y n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.equalCode w x y n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeAtoms.equality hZ w R S T U K L r s t u g h a b c d e f n q v x y h0 h1 h2 h3 h4

theorem equality_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (equalitySentence w R S T U K L r s t u g h a b c d e f n q v x y)) := TheoryTransport.sentence (source_equality w R S T U K L r s t u g h a b c d e f n q v x y)

theorem native_equality {m} (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (equalitySentence w R S T U K L r s t u g h a b c d e f n q v x y)) := ZFReplay.replay (equality_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v x y)

def membershipSentence {m} (w R S T U K L r s t u g h a b c d e f n q v z x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxAtomSyntax.memberCode w z x y n).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))).close

theorem source_membership {m} (w R S T U K L r s t u g h a b c d e f n q v z x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (membershipSentence w R S T U K L r s t u g h a b c d e f n q v z x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.memberCode w z x y n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.memberCode w z x y n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeAtoms.membership hZ w R S T U K L r s t u g h a b c d e f n q v z x y h0 h1 h2 h3 h4

theorem membership_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (membershipSentence w R S T U K L r s t u g h a b c d e f n q v z x y)) := TheoryTransport.sentence (source_membership w R S T U K L r s t u g h a b c d e f n q v z x y)

theorem native_membership {m} (w R S T U K L r s t u g h a b c d e f n q v z x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (membershipSentence w R S T U K L r s t u g h a b c d e f n q v z x y)) := ZFReplay.replay (membership_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v z x y)

def atomicSentence {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxAtomSyntax.atomic w a b n).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))).close

theorem source_atomic {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (atomicSentence w R S T U K L r s t u g h a b c d e f n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxAtomSyntax.atomic w a b n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxAtomSyntax.atomic w a b n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeAtoms.from_atomic hZ w R S T U K L r s t u g h a b c d e f n q v h0 h1 h2 h3 h4

theorem atomic_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (atomicSentence w R S T U K L r s t u g h a b c d e f n q v)) := TheoryTransport.sentence (source_atomic w R S T U K L r s t u g h a b c d e f n q v)

theorem native_atomic {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (atomicSentence w R S T U K L r s t u g h a b c d e f n q v)) := ZFReplay.replay (atomic_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v)

def advancedComposeSentence {m} (w n x R S T U K L a b c d e f X Z : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxComposeCodeSyntax.coded w b d f S U L).imp ((SyntaxRenameRecursiveSyntax.advanced w x R S a b c d X).imp ((SyntaxRenameRecursiveSyntax.advanced w X T U c d e f Z).imp (SyntaxRenameRecursiveSyntax.advanced w x K L a b e f Z)))))))).close

theorem source_advancedCompose {m} (w n x R S T U K L a b c d e f X Z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (advancedComposeSentence w n x R S T U K L a b c d e f X Z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.advanced w X T U c d e f Z) (Context.add (SyntaxRenameRecursiveSyntax.advanced w x R S a b c d X) (Context.add (SyntaxComposeCodeSyntax.coded w b d f S U L) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxComposeCodeSyntax.coded w b d f S U L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxRenameRecursiveSyntax.advanced w x R S a b c d X) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxRenameRecursiveSyntax.advanced w X T U c d e f Z) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeAdvanced.compose hZ w n x R S T U K L a b c d e f X Z h0 h1 h2 h3 h4 h5 h6

theorem advancedCompose_kernel_certificate {m} (w n x R S T U K L a b c d e f X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (advancedComposeSentence w n x R S T U K L a b c d e f X Z)) := TheoryTransport.sentence (source_advancedCompose w n x R S T U K L a b c d e f X Z)

theorem native_advancedCompose {m} (w n x R S T U K L a b c d e f X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (advancedComposeSentence w n x R S T U K L a b c d e f X Z)) := ZFReplay.replay (advancedCompose_kernel_certificate w n x R S T U K L a b c d e f X Z)

def checkComposeSentence {m} (advance : Bool) (w n x R S T U K L a b c d e f X Z : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxComposeCodeSyntax.coded w b d f S U L).imp ((SyntaxRenameRecursiveSyntax.check advance w x R S a b c d X).imp ((SyntaxRenameRecursiveSyntax.check advance w X T U c d e f Z).imp (SyntaxRenameRecursiveSyntax.check advance w x K L a b e f Z)))))))).close

theorem source_checkCompose {m} (advance : Bool) (w n x R S T U K L a b c d e f X Z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (checkComposeSentence advance w n x R S T U K L a b c d e f X Z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameRecursiveSyntax.check advance w X T U c d e f Z) (Context.add (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d X) (Context.add (SyntaxComposeCodeSyntax.coded w b d f S U L) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxComposeCodeSyntax.coded w b d f S U L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxRenameRecursiveSyntax.check advance w x R S a b c d X) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxRenameRecursiveSyntax.check advance w X T U c d e f Z) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeAdvanced.check hZ advance w n x R S T U K L a b c d e f X Z h0 h1 h2 h3 h4 h5 h6

theorem checkCompose_kernel_certificate {m} (advance : Bool) (w n x R S T U K L a b c d e f X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (checkComposeSentence advance w n x R S T U K L a b c d e f X Z)) := TheoryTransport.sentence (source_checkCompose advance w n x R S T U K L a b c d e f X Z)

theorem native_checkCompose {m} (advance : Bool) (w n x R S T U K L a b c d e f X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (checkComposeSentence advance w n x R S T U K L a b c d e f X Z)) := ZFReplay.replay (checkCompose_kernel_certificate advance w n x R S T U K L a b c d e f X Z)

def negationFieldsSentence {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp ((SyntaxLogicalSyntax.singleCode 4 w X q).imp ((SyntaxLogicalSyntax.singleCode 4 w Z v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))))))).close

theorem source_negationFields {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z) := by
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
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w Z v) (Context.add (SyntaxLogicalSyntax.singleCode 4 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w X q) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w Z v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeLogicalFields.single hZ 4 false (Or.inl ⟨rfl,rfl⟩) w R S T U K L r s t u g h a b c d e f n q v x X Z h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem negationFields_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z)) := TheoryTransport.sentence (source_negationFields w R S T U K L r s t u g h a b c d e f n q v x X Z)

theorem native_negationFields {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z)) := ZFReplay.replay (negationFields_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v x X Z)

def forallFieldsSentence {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp ((SyntaxLogicalSyntax.singleCode 9 w X q).imp ((SyntaxLogicalSyntax.singleCode 9 w Z v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))))))).close

theorem source_forallFields {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z) := by
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
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w Z v) (Context.add (SyntaxLogicalSyntax.singleCode 9 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w X q) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w Z v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeLogicalFields.single hZ 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩)) w R S T U K L r s t u g h a b c d e f n q v x X Z h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem forallFields_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z)) := TheoryTransport.sentence (source_forallFields w R S T U K L r s t u g h a b c d e f n q v x X Z)

theorem native_forallFields {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z)) := ZFReplay.replay (forallFields_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v x X Z)

def existsFieldsSentence {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp ((SyntaxLogicalSyntax.singleCode 10 w X q).imp ((SyntaxLogicalSyntax.singleCode 10 w Z v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))))))).close

theorem source_existsFields {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z) := by
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
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w Z v) (Context.add (SyntaxLogicalSyntax.singleCode 10 w X q) (Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))))
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
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h3 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h7 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w X q) := .hyp (Or.inr (Or.inl rfl))
  have h8 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w Z v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeLogicalFields.single hZ 10 true (Or.inr (Or.inr ⟨rfl,rfl⟩)) w R S T U K L r s t u g h a b c d e f n q v x X Z h0 h1 h2 h3 h4 h5 h6 h7 h8

theorem existsFields_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z)) := TheoryTransport.sentence (source_existsFields w R S T U K L r s t u g h a b c d e f n q v x X Z)

theorem native_existsFields {m} (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsFieldsSentence w R S T U K L r s t u g h a b c d e f n q v x X Z)) := ZFReplay.replay (existsFields_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v x X Z)

def binaryFieldsSentence {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((Formula.mem y n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp ((SyntaxLogicalSyntax.binaryCode kind w X Y q).imp ((SyntaxLogicalSyntax.binaryCode kind w Z W v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v))))))))))).close

theorem source_binaryFields {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binaryFieldsSentence kind w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W) := by
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
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w Z W v) (Context.add (SyntaxLogicalSyntax.binaryCode kind w X Y q) (Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (Formula.mem y n) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))))
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
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  have h3 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h4 : Derives Δ (Formula.mem y n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h6 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h7 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h8 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w X Y q) := .hyp (Or.inr (Or.inl rfl))
  have h9 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w Z W v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeLogicalFields.binary hZ kind w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W h0 h1 h2 h3 h4 h5 h6 h7 h8 h9

theorem binaryFields_kernel_certificate {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binaryFieldsSentence kind w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)) := TheoryTransport.sentence (source_binaryFields kind w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)

theorem native_binaryFields {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binaryFieldsSentence kind w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)) := ZFReplay.replay (binaryFields_kernel_certificate kind w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W)

def negationSentence {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxLogicalSyntax.singleCode 4 w x n).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))))).close

theorem source_negation {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (negationSentence w R S T U K L r s t u g h a b c d e f n q v x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 4 w x n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 4 w x n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeLogical.single hZ 4 false (Or.inl ⟨rfl,rfl⟩) w R S T U K L r s t u g h a b c d e f n q v x h0 h1 h2 h3 h4 h5 h6

theorem negation_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (negationSentence w R S T U K L r s t u g h a b c d e f n q v x)) := TheoryTransport.sentence (source_negation w R S T U K L r s t u g h a b c d e f n q v x)

theorem native_negation {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (negationSentence w R S T U K L r s t u g h a b c d e f n q v x)) := ZFReplay.replay (negation_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v x)

def forallSentence {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxLogicalSyntax.singleCode 9 w x n).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))))).close

theorem source_forall {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forallSentence w R S T U K L r s t u g h a b c d e f n q v x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 9 w x n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 9 w x n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeLogical.single hZ 9 true (Or.inr (Or.inl ⟨rfl,rfl⟩)) w R S T U K L r s t u g h a b c d e f n q v x h0 h1 h2 h3 h4 h5 h6

theorem forall_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forallSentence w R S T U K L r s t u g h a b c d e f n q v x)) := TheoryTransport.sentence (source_forall w R S T U K L r s t u g h a b c d e f n q v x)

theorem native_forall {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forallSentence w R S T U K L r s t u g h a b c d e f n q v x)) := ZFReplay.replay (forall_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v x)

def existsSentence {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxLogicalSyntax.singleCode 10 w x n).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))))).close

theorem source_exists {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsSentence w R S T U K L r s t u g h a b c d e f n q v x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.singleCode 10 w x n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (SyntaxLogicalSyntax.singleCode 10 w x n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeLogical.single hZ 10 true (Or.inr (Or.inr ⟨rfl,rfl⟩)) w R S T U K L r s t u g h a b c d e f n q v x h0 h1 h2 h3 h4 h5 h6

theorem exists_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsSentence w R S T U K L r s t u g h a b c d e f n q v x)) := TheoryTransport.sentence (source_exists w R S T U K L r s t u g h a b c d e f n q v x)

theorem native_exists {m} (w R S T U K L r s t u g h a b c d e f n q v x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsSentence w R S T U K L r s t u g h a b c d e f n q v x)) := ZFReplay.replay (exists_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v x)

def binarySentence {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((Formula.mem x n).imp ((Formula.mem y n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((SyntaxLogicalSyntax.binaryCode kind w x y n).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v))))))))).close

theorem source_binary {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (binarySentence kind w R S T U K L r s t u g h a b c d e f n q v x y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxLogicalSyntax.binaryCode kind w x y n) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (Formula.mem y n) (Context.add (Formula.mem x n) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (Formula.mem x n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (Formula.mem y n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w x y n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeLogical.binary hZ kind w R S T U K L r s t u g h a b c d e f n q v x y h0 h1 h2 h3 h4 h5 h6 h7

theorem binary_kernel_certificate {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (binarySentence kind w R S T U K L r s t u g h a b c d e f n q v x y)) := TheoryTransport.sentence (source_binary kind w R S T U K L r s t u g h a b c d e f n q v x y)

theorem native_binary {m} (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (binarySentence kind w R S T U K L r s t u g h a b c d e f n q v x y)) := ZFReplay.replay (binary_kernel_certificate kind w R S T U K L r s t u g h a b c d e f n q v x y)

def codeStepSentence {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp ((FormulaCodeSyntax.formulaCode w n a b).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v))))))).close

theorem source_codeStep {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (codeStepSentence w R S T U K L r s t u g h a b c d e f n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (FormulaCodeSyntax.formulaCode w n a b) (Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (FormulaCodeSyntax.formulaCode w n a b) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposePoint.from_code hZ w R S T U K L r s t u g h a b c d e f n q v h0 h1 h2 h3 h4 h5

theorem codeStep_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (codeStepSentence w R S T U K L r s t u g h a b c d e f n q v)) := TheoryTransport.sentence (source_codeStep w R S T U K L r s t u g h a b c d e f n q v)

theorem native_codeStep {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (codeStepSentence w R S T U K L r s t u g h a b c d e f n q v)) := ZFReplay.replay (codeStep_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v)

def diagramStepSentence {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))).close

theorem source_diagramStep {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (diagramStepSentence w R S T U K L r s t u g h a b c d e f n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposePoint.at_diagrams hZ w R S T U K L r s t u g h a b c d e f n q v h0 h1 h2 h3 h4

theorem diagramStep_kernel_certificate {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (diagramStepSentence w R S T U K L r s t u g h a b c d e f n q v)) := TheoryTransport.sentence (source_diagramStep w R S T U K L r s t u g h a b c d e f n q v)

theorem native_diagramStep {m} (w R S T U K L r s t u g h a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (diagramStepSentence w R S T U K L r s t u g h a b c d e f n q v)) := ZFReplay.replay (diagramStep_kernel_certificate w R S T U K L r s t u g h a b c d e f n q v)

def mapCodeStepSentence {m} (w n R S T U K L a b c d e f q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxComposeCodeSyntax.coded w b d f S U L).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v))))))).close

theorem source_mapCodeStep {m} (w n R S T U K L a b c d e f q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mapCodeStepSentence w n R S T U K L a b c d e f q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxComposeCodeSyntax.coded w b d f S U L) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h1 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h2 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h3 : Derives Δ (SyntaxComposeCodeSyntax.coded w b d f S U L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h5 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposePoint.from_codes hZ w n R S T U K L a b c d e f q v h0 h1 h2 h3 h4 h5

theorem mapCodeStep_kernel_certificate {m} (w n R S T U K L a b c d e f q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mapCodeStepSentence w n R S T U K L a b c d e f q v)) := TheoryTransport.sentence (source_mapCodeStep w n R S T U K L a b c d e f q v)

theorem native_mapCodeStep {m} (w n R S T U K L a b c d e f q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mapCodeStepSentence w n R S T U K L a b c d e f q v)) := ZFReplay.replay (mapCodeStep_kernel_certificate w n R S T U K L a b c d e f q v)

def propertyStepSentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxFormulaComposeSyntax.earlier w n).imp (SyntaxFormulaComposeSyntax.property w n))).close

theorem source_propertyStep {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (propertyStepSentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaComposeSyntax.earlier w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxFormulaComposeSyntax.earlier w n) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposePoint.property_from_earlier hZ w n h0 h1

theorem propertyStep_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (propertyStepSentence w n)) := TheoryTransport.sentence (source_propertyStep w n)

theorem native_propertyStep {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (propertyStepSentence w n)) := ZFReplay.replay (propertyStep_kernel_certificate w n)

def progressiveSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp (BoundedInduction.progressive SyntaxFormulaComposeInduction.matrix (fun _ : Fin 1 => w) w)).close

theorem source_progressive {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (progressiveSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeInduction.progressive hZ w h0

theorem progressive_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (progressiveSentence w)) := TheoryTransport.sentence (source_progressive w)

theorem native_progressive {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (progressiveSentence w)) := ZFReplay.replay (progressive_kernel_certificate w)

def allPropertiesSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp (Formula.all ((Formula.mem (Fin.last m) w.castSucc).imp (SyntaxFormulaComposeSyntax.property w.castSucc (Fin.last m))))).close

theorem source_allProperties {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (allPropertiesSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeInduction.all_properties hZ w h0

theorem allProperties_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (allPropertiesSentence w)) := TheoryTransport.sentence (source_allProperties w)

theorem native_allProperties {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (allPropertiesSentence w)) := ZFReplay.replay (allProperties_kernel_certificate w)

def naturalPropertySentence {m} (w n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp (SyntaxFormulaComposeSyntax.property w n))).close

theorem source_naturalProperty {m} (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (naturalPropertySentence w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeInduction.at_natural hZ w n h0 h1

theorem naturalProperty_kernel_certificate {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (naturalPropertySentence w n)) := TheoryTransport.sentence (source_naturalProperty w n)

theorem native_naturalProperty {m} (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (naturalPropertySentence w n)) := ZFReplay.replay (naturalProperty_kernel_certificate w n)

def forwardSentence {m} (w R S T U K L a b c d e f n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxComposeCodeSyntax.coded w b d f S U L).imp ((SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q).imp ((SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v)))))).close

theorem source_forward {m} (w R S T U K L a b c d e f n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (forwardSentence w R S T U K L a b c d e f n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) (Context.add (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) (Context.add (SyntaxComposeCodeSyntax.coded w b d f S U L) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (SyntaxComposeCodeSyntax.coded w b d f S U L) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeInduction.forward hZ w R S T U K L a b c d e f n q v h0 h1 h2 h3 h4

theorem forward_kernel_certificate {m} (w R S T U K L a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (forwardSentence w R S T U K L a b c d e f n q v)) := TheoryTransport.sentence (source_forward w R S T U K L a b c d e f n q v)

theorem native_forward {m} (w R S T U K L a b c d e f n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (forwardSentence w R S T U K L a b c d e f n q v)) := ZFReplay.replay (forward_kernel_certificate w R S T U K L a b c d e f n q v)

def factorSentence {m} (w R S T U K L a b c d e f n v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxComposeCodeSyntax.coded w b d f S U L).imp ((SyntaxFormulaComposeSyntax.result w K L a b e f n v).imp (SyntaxFormulaComposeFactor.sequential w R S T U a b c d e f n v))))).close

theorem source_factor {m} (w R S T U K L a b c d e f n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (factorSentence w R S T U K L a b c d e f n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaComposeSyntax.result w K L a b e f n v) (Context.add (SyntaxComposeCodeSyntax.coded w b d f S U L) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxComposeCodeSyntax.coded w b d f S U L) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxFormulaComposeSyntax.result w K L a b e f n v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeFactor.factor hZ w R S T U K L a b c d e f n v h0 h1 h2 h3

theorem factor_kernel_certificate {m} (w R S T U K L a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (factorSentence w R S T U K L a b c d e f n v)) := TheoryTransport.sentence (source_factor w R S T U K L a b c d e f n v)

theorem native_factor {m} (w R S T U K L a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (factorSentence w R S T U K L a b c d e f n v)) := ZFReplay.replay (factor_kernel_certificate w R S T U K L a b c d e f n v)

def collapseSentence {m} (w R S T U K L a b c d e f n v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxComposeCodeSyntax.coded w b d f S U L).imp ((SyntaxFormulaComposeFactor.sequential w R S T U a b c d e f n v).imp (SyntaxFormulaComposeSyntax.result w K L a b e f n v))))).close

theorem source_collapse {m} (w R S T U K L a b c d e f n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (collapseSentence w R S T U K L a b c d e f n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxFormulaComposeFactor.sequential w R S T U a b c d e f n v) (Context.add (SyntaxComposeCodeSyntax.coded w b d f S U L) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxComposeCodeSyntax.coded w b d f S U L) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxFormulaComposeFactor.sequential w R S T U a b c d e f n v) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeFactor.collapse hZ w R S T U K L a b c d e f n v h0 h1 h2 h3

theorem collapse_kernel_certificate {m} (w R S T U K L a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (collapseSentence w R S T U K L a b c d e f n v)) := TheoryTransport.sentence (source_collapse w R S T U K L a b c d e f n v)

theorem native_collapse {m} (w R S T U K L a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (collapseSentence w R S T U K L a b c d e f n v)) := ZFReplay.replay (collapse_kernel_certificate w R S T U K L a b c d e f n v)

def composeIffSentence {m} (w R S T U K L a b c d e f n v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxComposeCodeSyntax.coded w a c e R T K).imp ((SyntaxComposeCodeSyntax.coded w b d f S U L).imp ((SyntaxFormulaComposeSyntax.result w K L a b e f n v).iff (SyntaxFormulaComposeFactor.sequential w R S T U a b c d e f n v))))).close

theorem source_composeIff {m} (w R S T U K L a b c d e f n v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (composeIffSentence w R S T U K L a b c d e f n v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxComposeCodeSyntax.coded w b d f S U L) (Context.add (SyntaxComposeCodeSyntax.coded w a c e R T K) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxComposeCodeSyntax.coded w a c e R T K) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxComposeCodeSyntax.coded w b d f S U L) := .hyp (Or.inl rfl)
  exact SyntaxFormulaComposeFactor.compose_iff hZ w R S T U K L a b c d e f n v h0 h1 h2

theorem composeIff_kernel_certificate {m} (w R S T U K L a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (composeIffSentence w R S T U K L a b c d e f n v)) := TheoryTransport.sentence (source_composeIff w R S T U K L a b c d e f n v)

theorem native_composeIff {m} (w R S T U K L a b c d e f n v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (composeIffSentence w R S T U K L a b c d e f n v)) := ZFReplay.replay (composeIff_kernel_certificate w R S T U K L a b c d e f n v)

end PPAC.Migration.Internal.ObjectSyntaxFormulaCompose
