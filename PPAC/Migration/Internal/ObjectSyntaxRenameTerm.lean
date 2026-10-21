import PPAC.Migration.Internal.SyntaxRenameTermIdentity

/-! 任意内部完整索引映射下的纯项重命名实际存在唯一、作用域与精确图边原nativeZF闭句。 -/
namespace PPAC.Migration.Internal.ObjectSyntaxRenameTerm
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxVariableSyntax SyntaxIndexMapSyntax
open SyntaxTermSyntax (contexts term limit)
open SyntaxRenameTermSyntax (renamed existsBranch existsRenamed)
open SyntaxRenameTermIdentity (diagonal)

def sourceContextsSentence {m} (w r s a b c d : Fin m) : Source.Sentence := ((maps w r s a b c d).imp ((contexts w a b))).close

theorem source_sourceContexts {m} (w r s a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceContextsSentence w r s a b c d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (maps w r s a b c d) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (maps w r s a b c d) := .hyp (Or.inl rfl)
  exact SyntaxIndexMapSyntax.source_contexts w r s a b c d h0

theorem sourceContexts_kernel_certificate {m} (w r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceContextsSentence w r s a b c d)) := TheoryTransport.sentence (source_sourceContexts w r s a b c d)

theorem native_sourceContexts {m} (w r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceContextsSentence w r s a b c d)) := ZFReplay.replay (sourceContexts_kernel_certificate w r s a b c d)

def targetContextsSentence {m} (w r s a b c d : Fin m) : Source.Sentence := ((maps w r s a b c d).imp ((contexts w c d))).close

theorem source_targetContexts {m} (w r s a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetContextsSentence w r s a b c d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (maps w r s a b c d) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (maps w r s a b c d) := .hyp (Or.inl rfl)
  exact SyntaxIndexMapSyntax.target_contexts w r s a b c d h0

theorem targetContexts_kernel_certificate {m} (w r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetContextsSentence w r s a b c d)) := TheoryTransport.sentence (source_targetContexts w r s a b c d)

theorem native_targetContexts {m} (w r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetContextsSentence w r s a b c d)) := ZFReplay.replay (targetContexts_kernel_certificate w r s a b c d)

def selectedMapSentence {m} (bound : Bool) (w r s a b c d : Fin m) : Source.Sentence := ((maps w r s a b c d).imp ((indexMap w (selectMap bound r s) (limit bound a b) (limit bound c d)))).close

theorem source_selectedMap {m} (bound : Bool) (w r s a b c d : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (selectedMapSentence bound w r s a b c d) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (maps w r s a b c d) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (maps w r s a b c d) := .hyp (Or.inl rfl)
  exact SyntaxIndexMapSyntax.selected bound w r s a b c d h0

theorem selectedMap_kernel_certificate {m} (bound : Bool) (w r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (selectedMapSentence bound w r s a b c d)) := TheoryTransport.sentence (source_selectedMap bound w r s a b c d)

theorem native_selectedMap {m} (bound : Bool) (w r s a b c d : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (selectedMapSentence bound w r s a b c d)) := ZFReplay.replay (selectedMap_kernel_certificate bound w r s a b c d)

def edgeSourceSentence {m} (w r a c i j : Fin m) : Source.Sentence := ((indexMap w r a c).imp ((edge r i j).imp ((Formula.mem i a)))).close

theorem source_edgeSource {m} (w r a c i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (edgeSourceSentence w r a c i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (edge r i j) (Context.add (indexMap w r a c) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (edge r i j) := .hyp (Or.inl rfl)
  exact SyntaxIndexMapSyntax.edge_source hZ w r a c i j h0 h1

theorem edgeSource_kernel_certificate {m} (w r a c i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (edgeSourceSentence w r a c i j)) := TheoryTransport.sentence (source_edgeSource w r a c i j)

theorem native_edgeSource {m} (w r a c i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (edgeSourceSentence w r a c i j)) := ZFReplay.replay (edgeSource_kernel_certificate w r a c i j)

def edgeTargetSentence {m} (w r a c i j : Fin m) : Source.Sentence := ((indexMap w r a c).imp ((edge r i j).imp ((Formula.mem j c)))).close

theorem source_edgeTarget {m} (w r a c i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (edgeTargetSentence w r a c i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (edge r i j) (Context.add (indexMap w r a c) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (edge r i j) := .hyp (Or.inl rfl)
  exact SyntaxIndexMapSyntax.edge_target w r a c i j h0 h1

theorem edgeTarget_kernel_certificate {m} (w r a c i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (edgeTargetSentence w r a c i j)) := TheoryTransport.sentence (source_edgeTarget w r a c i j)

theorem native_edgeTarget {m} (w r a c i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (edgeTargetSentence w r a c i j)) := ZFReplay.replay (edgeTarget_kernel_certificate w r a c i j)

def valueExistsSentence {m} (w r a c i : Fin m) : Source.Sentence := ((indexMap w r a c).imp ((Formula.mem i a).imp ((SequenceSyntax.value r i c)))).close

theorem source_valueExists {m} (w r a c i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (valueExistsSentence w r a c i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i a) (Context.add (indexMap w r a c) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i a) := .hyp (Or.inl rfl)
  exact SyntaxIndexMapSyntax.value_exists w r a c i h0 h1

theorem valueExists_kernel_certificate {m} (w r a c i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (valueExistsSentence w r a c i)) := TheoryTransport.sentence (source_valueExists w r a c i)

theorem native_valueExists {m} (w r a c i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (valueExistsSentence w r a c i)) := ZFReplay.replay (valueExists_kernel_certificate w r a c i)

def introBranchSentence {m} (bound : Bool) (w r a n q i j : Fin m) : Source.Sentence := ((Formula.mem i a).imp ((edge r i j).imp ((code bound w i n).imp ((code bound w j q).imp ((SyntaxRenameTermSyntax.branch bound w r a n q)))))).close

theorem source_introBranch {m} (bound : Bool) (w r a n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (introBranchSentence bound w r a n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code bound w j q) (Context.add (code bound w i n) (Context.add (edge r i j) (Context.add (Formula.mem i a) ((Source.SetLanguage.ZF.at m)))))
  have h0 : Derives Δ (Formula.mem i a) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (edge r i j) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (code bound w i n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (code bound w j q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermSyntax.intro_branch bound w r a n q i j h0 h1 h2 h3

theorem introBranch_kernel_certificate {m} (bound : Bool) (w r a n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (introBranchSentence bound w r a n q i j)) := TheoryTransport.sentence (source_introBranch bound w r a n q i j)

theorem native_introBranch {m} (bound : Bool) (w r a n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (introBranchSentence bound w r a n q i j)) := ZFReplay.replay (introBranch_kernel_certificate bound w r a n q i j)

def sourceBranchSentence {m} (bound : Bool) (w r a n q : Fin m) : Source.Sentence := ((SyntaxRenameTermSyntax.branch bound w r a n q).imp ((SyntaxTermSyntax.branch bound w a n))).close

theorem source_sourceBranch {m} (bound : Bool) (w r a n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceBranchSentence bound w r a n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.branch bound w r a n q) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameTermSyntax.branch bound w r a n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermTyping.source_branch bound w r a n q h0

theorem sourceBranch_kernel_certificate {m} (bound : Bool) (w r a n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceBranchSentence bound w r a n q)) := TheoryTransport.sentence (source_sourceBranch bound w r a n q)

theorem native_sourceBranch {m} (bound : Bool) (w r a n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceBranchSentence bound w r a n q)) := ZFReplay.replay (sourceBranch_kernel_certificate bound w r a n q)

def targetBranchSentence {m} (bound : Bool) (w r a c n q : Fin m) : Source.Sentence := ((indexMap w r a c).imp ((SyntaxRenameTermSyntax.branch bound w r a n q).imp ((SyntaxTermSyntax.branch bound w c q)))).close

theorem source_targetBranch {m} (bound : Bool) (w r a c n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetBranchSentence bound w r a c n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.branch bound w r a n q) (Context.add (indexMap w r a c) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxRenameTermSyntax.branch bound w r a n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermTyping.target_branch bound w r a c n q h0 h1

theorem targetBranch_kernel_certificate {m} (bound : Bool) (w r a c n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetBranchSentence bound w r a c n q)) := TheoryTransport.sentence (source_targetBranch bound w r a c n q)

theorem native_targetBranch {m} (bound : Bool) (w r a c n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetBranchSentence bound w r a c n q)) := ZFReplay.replay (targetBranch_kernel_certificate bound w r a c n q)

def sourceTermSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((renamed w r s a b c d n q).imp ((term w a b n))).close

theorem source_sourceTerm {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (sourceTermSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (renamed w r s a b c d n q) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermTyping.source_term w r s a b c d n q h0

theorem sourceTerm_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (sourceTermSentence w r s a b c d n q)) := TheoryTransport.sentence (source_sourceTerm w r s a b c d n q)

theorem native_sourceTerm {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (sourceTermSentence w r s a b c d n q)) := ZFReplay.replay (sourceTerm_kernel_certificate w r s a b c d n q)

def targetTermSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((renamed w r s a b c d n q).imp ((term w c d q))).close

theorem source_targetTerm {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (targetTermSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (renamed w r s a b c d n q) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermTyping.target_term w r s a b c d n q h0

theorem targetTerm_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (targetTermSentence w r s a b c d n q)) := TheoryTransport.sentence (source_targetTerm w r s a b c d n q)

theorem native_targetTerm {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (targetTermSentence w r s a b c d n q)) := ZFReplay.replay (targetTerm_kernel_certificate w r s a b c d n q)

def outputNaturalSentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((renamed w r s a b c d n q).imp ((Formula.mem q w)))).close

theorem source_outputNatural {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputNaturalSentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (renamed w r s a b c d n q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermTyping.output_natural hZ w r s a b c d n q h0 h1

theorem outputNatural_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputNaturalSentence w r s a b c d n q)) := TheoryTransport.sentence (source_outputNatural w r s a b c d n q)

theorem native_outputNatural {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputNaturalSentence w r s a b c d n q)) := ZFReplay.replay (outputNatural_kernel_certificate w r s a b c d n q)

def oppositeBranchesSentence {m} (w r s a b n q v : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxRenameTermSyntax.branch true w r a n q).imp ((SyntaxRenameTermSyntax.branch false w s b n v).imp ((Formula.bot))))).close

theorem source_oppositeBranches {m} (w r s a b n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (oppositeBranchesSentence w r s a b n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.branch false w s b n v) (Context.add (SyntaxRenameTermSyntax.branch true w r a n q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxRenameTermSyntax.branch true w r a n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameTermSyntax.branch false w s b n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermTyping.opposite_branches hZ w r s a b n q v h0 h1 h2

theorem oppositeBranches_kernel_certificate {m} (w r s a b n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (oppositeBranchesSentence w r s a b n q v)) := TheoryTransport.sentence (source_oppositeBranches w r s a b n q v)

theorem native_oppositeBranches {m} (w r s a b n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (oppositeBranchesSentence w r s a b n q v)) := ZFReplay.replay (oppositeBranches_kernel_certificate w r s a b n q v)

def branchUniqueSentence {m} (bound : Bool) (w r a n q v : Fin m) : Source.Sentence := ((omega w).imp ((functionOn r a).imp ((SyntaxRenameTermSyntax.branch bound w r a n q).imp ((SyntaxRenameTermSyntax.branch bound w r a n v).imp ((Formula.equal q v)))))).close

theorem source_branchUnique {m} (bound : Bool) (w r a n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (branchUniqueSentence bound w r a n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.branch bound w r a n v) (Context.add (SyntaxRenameTermSyntax.branch bound w r a n q) (Context.add (functionOn r a) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (functionOn r a) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (SyntaxRenameTermSyntax.branch bound w r a n q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxRenameTermSyntax.branch bound w r a n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermUnique.branch_unique hZ bound w r a n q v h0 h1 h2 h3

theorem branchUnique_kernel_certificate {m} (bound : Bool) (w r a n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (branchUniqueSentence bound w r a n q v)) := TheoryTransport.sentence (source_branchUnique bound w r a n q v)

theorem native_branchUnique {m} (bound : Bool) (w r a n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (branchUniqueSentence bound w r a n q v)) := ZFReplay.replay (branchUnique_kernel_certificate bound w r a n q v)

def uniqueSentence {m} (w r s a b c d n q v : Fin m) : Source.Sentence := ((omega w).imp ((renamed w r s a b c d n q).imp ((renamed w r s a b c d n v).imp ((Formula.equal q v))))).close

theorem source_unique {m} (w r s a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (uniqueSentence w r s a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (renamed w r s a b c d n v) (Context.add (renamed w r s a b c d n q) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (renamed w r s a b c d n q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (renamed w r s a b c d n v) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermUnique.unique hZ w r s a b c d n q v h0 h1 h2

theorem unique_kernel_certificate {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (uniqueSentence w r s a b c d n q v)) := TheoryTransport.sentence (source_unique w r s a b c d n q v)

theorem native_unique {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (uniqueSentence w r s a b c d n q v)) := ZFReplay.replay (unique_kernel_certificate w r s a b c d n q v)

def existsAtIndexSentence {m} (bound : Bool) (w r a c n i : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w r a c).imp ((Formula.mem i a).imp ((code bound w i n).imp ((existsBranch bound w r a n)))))).close

theorem source_existsAtIndex {m} (bound : Bool) (w r a c n i : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsAtIndexSentence bound w r a c n i) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code bound w i n) (Context.add (Formula.mem i a) (Context.add (indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i a) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (code bound w i n) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermExistence.at_index hZ bound w r a c n i h0 h1 h2 h3

theorem existsAtIndex_kernel_certificate {m} (bound : Bool) (w r a c n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsAtIndexSentence bound w r a c n i)) := TheoryTransport.sentence (source_existsAtIndex bound w r a c n i)

theorem native_existsAtIndex {m} (bound : Bool) (w r a c n i : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsAtIndexSentence bound w r a c n i)) := ZFReplay.replay (existsAtIndex_kernel_certificate bound w r a c n i)

def existsBranchSentence {m} (bound : Bool) (w r a c n : Fin m) : Source.Sentence := ((omega w).imp ((indexMap w r a c).imp ((SyntaxTermSyntax.branch bound w a n).imp ((existsBranch bound w r a n))))).close

theorem source_existsBranch {m} (bound : Bool) (w r a c n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsBranchSentence bound w r a c n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxTermSyntax.branch bound w a n) (Context.add (indexMap w r a c) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (indexMap w r a c) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxTermSyntax.branch bound w a n) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermExistence.for_branch hZ bound w r a c n h0 h1 h2

theorem existsBranch_kernel_certificate {m} (bound : Bool) (w r a c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsBranchSentence bound w r a c n)) := TheoryTransport.sentence (source_existsBranch bound w r a c n)

theorem native_existsBranch {m} (bound : Bool) (w r a c n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsBranchSentence bound w r a c n)) := ZFReplay.replay (existsBranch_kernel_certificate bound w r a c n)

def existsTermSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((maps w r s a b c d).imp ((term w a b n).imp ((existsRenamed w r s a b c d n))))).close

theorem source_existsTerm {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsTermSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (term w a b n) (Context.add (maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (maps w r s a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (term w a b n) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermExistence.for_term hZ w r s a b c d n h0 h1 h2

theorem existsTerm_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsTermSentence w r s a b c d n)) := TheoryTransport.sentence (source_existsTerm w r s a b c d n)

theorem native_existsTerm {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsTermSentence w r s a b c d n)) := ZFReplay.replay (existsTerm_kernel_certificate w r s a b c d n)

def fiberSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((maps w r s a b c d).imp ((term w a b n).imp ((SyntaxRenameTermSyntax.fiber w r s a b c d n))))).close

theorem source_fiber {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (term w a b n) (Context.add (maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (maps w r s a b c d) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (term w a b n) := .hyp (Or.inl rfl)
  exact SyntaxRenameTerm.actual_fiber hZ w r s a b c d n h0 h1 h2

theorem fiber_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberSentence w r s a b c d n)) := TheoryTransport.sentence (source_fiber w r s a b c d n)

theorem native_fiber {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberSentence w r s a b c d n)) := ZFReplay.replay (fiber_kernel_certificate w r s a b c d n)

def termOfExistsSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((existsRenamed w r s a b c d n).imp ((term w a b n))).close

theorem source_termOfExists {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termOfExistsSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (existsRenamed w r s a b c d n) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (existsRenamed w r s a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxRenameTerm.term_of_exists w r s a b c d n h0

theorem termOfExists_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termOfExistsSentence w r s a b c d n)) := TheoryTransport.sentence (source_termOfExists w r s a b c d n)

theorem native_termOfExists {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termOfExistsSentence w r s a b c d n)) := ZFReplay.replay (termOfExists_kernel_certificate w r s a b c d n)

def termOfFiberSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((SyntaxRenameTermSyntax.fiber w r s a b c d n).imp ((term w a b n))).close

theorem source_termOfFiber {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (termOfFiberSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.fiber w r s a b c d n) ((Source.SetLanguage.ZF.at m))
  have h0 : Derives Δ (SyntaxRenameTermSyntax.fiber w r s a b c d n) := .hyp (Or.inl rfl)
  exact SyntaxRenameTerm.term_of_fiber w r s a b c d n h0

theorem termOfFiber_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (termOfFiberSentence w r s a b c d n)) := TheoryTransport.sentence (source_termOfFiber w r s a b c d n)

theorem native_termOfFiber {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (termOfFiberSentence w r s a b c d n)) := ZFReplay.replay (termOfFiber_kernel_certificate w r s a b c d n)

def existsIffSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((maps w r s a b c d).imp (((term w a b n).iff (existsRenamed w r s a b c d n))))).close

theorem source_existsIff {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (existsIffSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (maps w r s a b c d) := .hyp (Or.inl rfl)
  exact SyntaxRenameTerm.exists_iff hZ w r s a b c d n h0 h1

theorem existsIff_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (existsIffSentence w r s a b c d n)) := TheoryTransport.sentence (source_existsIff w r s a b c d n)

theorem native_existsIff {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (existsIffSentence w r s a b c d n)) := ZFReplay.replay (existsIff_kernel_certificate w r s a b c d n)

def fiberIffSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((maps w r s a b c d).imp (((term w a b n).iff (SyntaxRenameTermSyntax.fiber w r s a b c d n))))).close

theorem source_fiberIff {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (fiberIffSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (maps w r s a b c d) := .hyp (Or.inl rfl)
  exact SyntaxRenameTerm.fiber_iff hZ w r s a b c d n h0 h1

theorem fiberIff_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (fiberIffSentence w r s a b c d n)) := TheoryTransport.sentence (source_fiberIff w r s a b c d n)

theorem native_fiberIff {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (fiberIffSentence w r s a b c d n)) := ZFReplay.replay (fiberIff_kernel_certificate w r s a b c d n)

def knownBranchSentence {m} (bound : Bool) (w r a n q i j : Fin m) : Source.Sentence := ((omega w).imp ((code bound w i n).imp ((code bound w j q).imp (((SyntaxRenameTermSyntax.branch bound w r a n q).iff ((Formula.mem i a).conj (edge r i j))))))).close

theorem source_knownBranch {m} (bound : Bool) (w r a n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (knownBranchSentence bound w r a n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code bound w j q) (Context.add (code bound w i n) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (code bound w i n) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (code bound w j q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermKnown.branch_iff hZ bound w r a n q i j h0 h1 h2

theorem knownBranch_kernel_certificate {m} (bound : Bool) (w r a n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (knownBranchSentence bound w r a n q i j)) := TheoryTransport.sentence (source_knownBranch bound w r a n q i j)

theorem native_knownBranch {m} (bound : Bool) (w r a n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (knownBranchSentence bound w r a n q i j)) := ZFReplay.replay (knownBranch_kernel_certificate bound w r a n q i j)

def knownTermSentence {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : Source.Sentence := ((omega w).imp ((maps w r s a b c d).imp ((code bound w i n).imp ((code bound w j q).imp (((renamed w r s a b c d n q).iff ((Formula.mem i (limit bound a b)).conj (edge (selectMap bound r s) i j)))))))).close

theorem source_knownTerm {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (knownTermSentence bound w r s a b c d n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (code bound w j q) (Context.add (code bound w i n) (Context.add (maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (maps w r s a b c d) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (code bound w i n) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (code bound w j q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermKnown.known_iff hZ bound w r s a b c d n q i j h0 h1 h2 h3

theorem knownTerm_kernel_certificate {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (knownTermSentence bound w r s a b c d n q i j)) := TheoryTransport.sentence (source_knownTerm bound w r s a b c d n q i j)

theorem native_knownTerm {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (knownTermSentence bound w r s a b c d n q i j)) := ZFReplay.replay (knownTerm_kernel_certificate bound w r s a b c d n q i j)

def rejectEdgeSentence {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : Source.Sentence := ((omega w).imp ((maps w r s a b c d).imp ((code bound w i n).imp ((code bound w j q).imp (((edge (selectMap bound r s) i j).neg).imp (((renamed w r s a b c d n q).neg))))))).close

theorem source_rejectEdge {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (rejectEdgeSentence bound w r s a b c d n q i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add ((edge (selectMap bound r s) i j).neg) (Context.add (code bound w j q) (Context.add (code bound w i n) (Context.add (maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (maps w r s a b c d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (code bound w i n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (code bound w j q) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ ((edge (selectMap bound r s) i j).neg) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermKnown.reject_edge hZ bound w r s a b c d n q i j h0 h1 h2 h3 h4

theorem rejectEdge_kernel_certificate {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (rejectEdgeSentence bound w r s a b c d n q i j)) := TheoryTransport.sentence (source_rejectEdge bound w r s a b c d n q i j)

theorem native_rejectEdge {m} (bound : Bool) (w r s a b c d n q i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (rejectEdgeSentence bound w r s a b c d n q i j)) := ZFReplay.replay (rejectEdge_kernel_certificate bound w r s a b c d n q i j)

def diagonalAtSentence {m} (r i j : Fin m) : Source.Sentence := ((diagonal r).imp ((edge r i j).imp ((Formula.equal i j)))).close

theorem source_diagonalAt {m} (r i j : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (diagonalAtSentence r i j) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (edge r i j) (Context.add (diagonal r) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (diagonal r) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (edge r i j) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermIdentity.diagonal_at r i j h0 h1

theorem diagonalAt_kernel_certificate {m} (r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (diagonalAtSentence r i j)) := TheoryTransport.sentence (source_diagonalAt r i j)

theorem native_diagonalAt {m} (r i j : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (diagonalAtSentence r i j)) := ZFReplay.replay (diagonalAt_kernel_certificate r i j)

def branchIdentitySentence {m} (bound : Bool) (w r a n q : Fin m) : Source.Sentence := ((omega w).imp ((diagonal r).imp ((SyntaxRenameTermSyntax.branch bound w r a n q).imp ((Formula.equal n q))))).close

theorem source_branchIdentity {m} (bound : Bool) (w r a n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (branchIdentitySentence bound w r a n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxRenameTermSyntax.branch bound w r a n q) (Context.add (diagonal r) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (diagonal r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxRenameTermSyntax.branch bound w r a n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermIdentity.branch_identity hZ bound w r a n q h0 h1 h2

theorem branchIdentity_kernel_certificate {m} (bound : Bool) (w r a n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (branchIdentitySentence bound w r a n q)) := TheoryTransport.sentence (source_branchIdentity bound w r a n q)

theorem native_branchIdentity {m} (bound : Bool) (w r a n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (branchIdentitySentence bound w r a n q)) := ZFReplay.replay (branchIdentity_kernel_certificate bound w r a n q)

def identitySentence {m} (w r s a b c d n q : Fin m) : Source.Sentence := ((omega w).imp ((diagonal r).imp ((diagonal s).imp ((renamed w r s a b c d n q).imp ((Formula.equal n q)))))).close

theorem source_identity {m} (w r s a b c d n q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (identitySentence w r s a b c d n q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (renamed w r s a b c d n q) (Context.add (diagonal s) (Context.add (diagonal r) (Context.add (omega w) ((Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (diagonal r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (diagonal s) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermIdentity.identity hZ w r s a b c d n q h0 h1 h2 h3

theorem identity_kernel_certificate {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (identitySentence w r s a b c d n q)) := TheoryTransport.sentence (source_identity w r s a b c d n q)

theorem native_identity {m} (w r s a b c d n q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (identitySentence w r s a b c d n q)) := ZFReplay.replay (identity_kernel_certificate w r s a b c d n q)

def outputSubstSentence {m} (w r s a b c d n q v : Fin m) : Source.Sentence := ((Formula.equal q v).imp ((renamed w r s a b c d n q).imp ((renamed w r s a b c d n v)))).close

theorem source_outputSubst {m} (w r s a b c d n q v : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (outputSubstSentence w r s a b c d n q v) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (renamed w r s a b c d n q) (Context.add (Formula.equal q v) ((Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (Formula.equal q v) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (renamed w r s a b c d n q) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermIdentity.output_subst w r s a b c d n q v h0 h1

theorem outputSubst_kernel_certificate {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (outputSubstSentence w r s a b c d n q v)) := TheoryTransport.sentence (source_outputSubst w r s a b c d n q v)

theorem native_outputSubst {m} (w r s a b c d n q v : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (outputSubstSentence w r s a b c d n q v)) := ZFReplay.replay (outputSubst_kernel_certificate w r s a b c d n q v)

def reflexiveSentence {m} (w r s a b c d n : Fin m) : Source.Sentence := ((omega w).imp ((maps w r s a b c d).imp ((diagonal r).imp ((diagonal s).imp ((term w a b n).imp ((renamed w r s a b c d n n))))))).close

theorem source_reflexive {m} (w r s a b c d n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (reflexiveSentence w r s a b c d n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (term w a b n) (Context.add (diagonal s) (Context.add (diagonal r) (Context.add (maps w r s a b c d) (Context.add (omega w) ((Source.SetLanguage.ZF.at m))))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (maps w r s a b c d) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (diagonal r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (diagonal s) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (term w a b n) := .hyp (Or.inl rfl)
  exact SyntaxRenameTermIdentity.reflexive hZ w r s a b c d n h0 h1 h2 h3 h4

theorem reflexive_kernel_certificate {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (reflexiveSentence w r s a b c d n)) := TheoryTransport.sentence (source_reflexive w r s a b c d n)

theorem native_reflexive {m} (w r s a b c d n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (reflexiveSentence w r s a b c d n)) := ZFReplay.replay (reflexive_kernel_certificate w r s a b c d n)

end PPAC.Migration.Internal.ObjectSyntaxRenameTerm
