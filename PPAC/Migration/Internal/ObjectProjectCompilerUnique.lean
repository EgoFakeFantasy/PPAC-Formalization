import PPAC.Migration.Internal.ProjectCompilerUniqueFiber

/-! Actual compiler scalar uniqueness and legal-source typed unique fibers; source validity converse and original code bridge remain unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectProjectCompilerUnique
open Source SourceAlgebra SourceLogic OmegaSyntax

def compilerGuardedChildScalarUniqueSentence {m} (w n x b q r : Fin m) : Source.Sentence := ((ProjectCompilerUniqueSyntax.allIH w n).imp ((ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q).imp ((ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b r).imp ((Formula.equal q r))))).close

theorem source_compilerGuardedChildScalarUnique {m} (w n x b q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerGuardedChildScalarUniqueSentence w n x b q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b r) (Context.add (ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q) (Context.add (ProjectCompilerUniqueSyntax.allIH w n) (Source.SetLanguage.ZF.at m)))
  have h0 : Derives Δ (ProjectCompilerUniqueSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b r) := .hyp (Or.inl rfl)
  exact ProjectCompilerUniqueQueries.query_unique w n x b q r h0 h1 h2

theorem compilerGuardedChildScalarUnique_kernel_certificate {m} (w n x b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerGuardedChildScalarUniqueSentence w n x b q r)) := TheoryTransport.sentence (source_compilerGuardedChildScalarUnique w n x b q r)

theorem native_compilerGuardedChildScalarUnique {m} (w n x b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerGuardedChildScalarUniqueSentence w n x b q r)) := ZFReplay.replay (compilerGuardedChildScalarUnique_kernel_certificate w n x b q r)

def compilerSuccessorChildScalarUniqueSentence {m} (w n x b q r : Fin m) : Source.Sentence := ((ProjectCompilerUniqueSyntax.allIH w n).imp ((ProjectCompilerCaseSyntax.advanced ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q).imp ((ProjectCompilerCaseSyntax.advanced ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b r).imp ((Formula.equal q r))))).close

theorem source_compilerSuccessorChildScalarUnique {m} (w n x b q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSuccessorChildScalarUniqueSentence w n x b q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCaseSyntax.advanced ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b r) (Context.add (ProjectCompilerCaseSyntax.advanced ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q) (Context.add (ProjectCompilerUniqueSyntax.allIH w n) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (ProjectCompilerUniqueSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectCompilerCaseSyntax.advanced ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectCompilerCaseSyntax.advanced ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b r) := .hyp (Or.inl rfl)
  exact ProjectCompilerUniqueQueries.advanced_unique hZ w n x b q r h0 h1 h2

theorem compilerSuccessorChildScalarUnique_kernel_certificate {m} (w n x b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSuccessorChildScalarUniqueSentence w n x b q r)) := TheoryTransport.sentence (source_compilerSuccessorChildScalarUnique w n x b q r)

theorem native_compilerSuccessorChildScalarUnique {m} (w n x b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSuccessorChildScalarUniqueSentence w n x b q r)) := ZFReplay.replay (compilerSuccessorChildScalarUnique_kernel_certificate w n x b q r)

def compilerAllCasesScalarUniqueSentence {m} (w b z n q r : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerUniqueSyntax.allIH w n).imp ((ProjectCompilerRecursiveSyntax.casesAt w b z n q).imp ((ProjectCompilerRecursiveSyntax.casesAt w b z n r).imp ((Formula.equal q r)))))).close

theorem source_compilerAllCasesScalarUnique {m} (w b z n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllCasesScalarUniqueSentence w b z n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerRecursiveSyntax.casesAt w b z n r) (Context.add (ProjectCompilerRecursiveSyntax.casesAt w b z n q) (Context.add (ProjectCompilerUniqueSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (ProjectCompilerUniqueSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerRecursiveSyntax.casesAt w b z n q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerRecursiveSyntax.casesAt w b z n r) := .hyp (Or.inl rfl)
  exact ProjectCompilerUniquePairs.actual_cases_unique hZ w b z n q r h0 h1 h2 h3

theorem compilerAllCasesScalarUnique_kernel_certificate {m} (w b z n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllCasesScalarUniqueSentence w b z n q r)) := TheoryTransport.sentence (source_compilerAllCasesScalarUnique w b z n q r)

theorem native_compilerAllCasesScalarUnique {m} (w b z n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllCasesScalarUniqueSentence w b z n q r)) := ZFReplay.replay (compilerAllCasesScalarUnique_kernel_certificate w b z n q r)

def compilerOutputsUniqueFromMemberIHSentence {m} (w n b q r : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerUniqueSyntax.allIH w n).imp ((ProjectCompilerCodeSyntax.compiled w n b q).imp ((ProjectCompilerCodeSyntax.compiled w n b r).imp ((Formula.equal q r)))))).close

theorem source_compilerOutputsUniqueFromMemberIH {m} (w n b q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerOutputsUniqueFromMemberIHSentence w n b q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.compiled w n b r) (Context.add (ProjectCompilerCodeSyntax.compiled w n b q) (Context.add (ProjectCompilerUniqueSyntax.allIH w n) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (ProjectCompilerUniqueSyntax.allIH w n) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b q) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b r) := .hyp (Or.inl rfl)
  exact ProjectCompilerUniqueStep.outputs_from_induction hZ w n b q r h0 h1 h2 h3

theorem compilerOutputsUniqueFromMemberIH_kernel_certificate {m} (w n b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerOutputsUniqueFromMemberIHSentence w n b q r)) := TheoryTransport.sentence (source_compilerOutputsUniqueFromMemberIH w n b q r)

theorem native_compilerOutputsUniqueFromMemberIH {m} (w n b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerOutputsUniqueFromMemberIHSentence w n b q r)) := ZFReplay.replay (compilerOutputsUniqueFromMemberIH_kernel_certificate w n b q r)

def compilerScalarFunctionalityProgressiveSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((SetInductionSyntax.progressive ProjectCompilerUnique.inductionMatrix (fun _ : Fin 1 => w)))).close

theorem source_compilerScalarFunctionalityProgressive {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerScalarFunctionalityProgressiveSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerUnique.progressive hZ w h0

theorem compilerScalarFunctionalityProgressive_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerScalarFunctionalityProgressiveSentence w)) := TheoryTransport.sentence (source_compilerScalarFunctionalityProgressive w)

theorem native_compilerScalarFunctionalityProgressive {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerScalarFunctionalityProgressiveSentence w)) := ZFReplay.replay (compilerScalarFunctionalityProgressive_kernel_certificate w)

def compilerAllInternalOutputsScalarUniqueSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.all (ProjectCompilerUniqueSyntax.functional w.castSucc (Fin.last m))))).close

theorem source_compilerAllInternalOutputsScalarUnique {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalOutputsScalarUniqueSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerUnique.all_functional hZ w h0

theorem compilerAllInternalOutputsScalarUnique_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalOutputsScalarUniqueSentence w)) := TheoryTransport.sentence (source_compilerAllInternalOutputsScalarUnique w)

theorem native_compilerAllInternalOutputsScalarUnique {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalOutputsScalarUniqueSentence w)) := ZFReplay.replay (compilerAllInternalOutputsScalarUnique_kernel_certificate w)

def compilerActualOutputsScalarUniqueSentence {m} (w n b q r : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerCodeSyntax.compiled w n b q).imp ((ProjectCompilerCodeSyntax.compiled w n b r).imp ((Formula.equal q r))))).close

theorem source_compilerActualOutputsScalarUnique {m} (w n b q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualOutputsScalarUniqueSentence w n b q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.compiled w n b r) (Context.add (ProjectCompilerCodeSyntax.compiled w n b q) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b q) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b r) := .hyp (Or.inl rfl)
  exact ProjectCompilerUnique.unique_outputs hZ w n b q r h0 h1 h2

theorem compilerActualOutputsScalarUnique_kernel_certificate {m} (w n b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualOutputsScalarUniqueSentence w n b q r)) := TheoryTransport.sentence (source_compilerActualOutputsScalarUnique w n b q r)

theorem native_compilerActualOutputsScalarUnique {m} (w n b q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualOutputsScalarUniqueSentence w n b q r)) := ZFReplay.replay (compilerActualOutputsScalarUnique_kernel_certificate w n b q r)

def compilerActualUniqueOutputFiberSentence {m} (w n b q : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerCodeSyntax.compiled w n b q).imp ((ProjectCompilerUniqueFiberSyntax.uniqueOutput w n b q)))).close

theorem source_compilerActualUniqueOutputFiber {m} (w n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualUniqueOutputFiberSentence w n b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.compiled w n b q) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectCompilerCodeSyntax.compiled w n b q) := .hyp (Or.inl rfl)
  exact ProjectCompilerUniqueFiber.unique_output hZ w n b q h0 h1

theorem compilerActualUniqueOutputFiber_kernel_certificate {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualUniqueOutputFiberSentence w n b q)) := TheoryTransport.sentence (source_compilerActualUniqueOutputFiber w n b q)

theorem native_compilerActualUniqueOutputFiber {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualUniqueOutputFiberSentence w n b q)) := ZFReplay.replay (compilerActualUniqueOutputFiber_kernel_certificate w n b q)

def compilerSourceActualTypedUniqueOutputExistsSentence {m} (w n b f z : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp ((ProjectSourceCodeSyntax.sourceCode w n b f).imp ((ProjectCompilerUniqueFiberSyntax.typedFiber w n b z))))).close

theorem source_compilerSourceActualTypedUniqueOutputExists {m} (w n b f z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSourceActualTypedUniqueOutputExistsSentence w n b f z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectSourceCodeSyntax.sourceCode w n b f) (Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectSourceCodeSyntax.sourceCode w n b f) := .hyp (Or.inl rfl)
  exact ProjectCompilerUniqueFiber.typed_unique_exists hZ w n b f z h0 h1 h2

theorem compilerSourceActualTypedUniqueOutputExists_kernel_certificate {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSourceActualTypedUniqueOutputExistsSentence w n b f z)) := TheoryTransport.sentence (source_compilerSourceActualTypedUniqueOutputExists w n b f z)

theorem native_compilerSourceActualTypedUniqueOutputExists {m} (w n b f z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSourceActualTypedUniqueOutputExistsSentence w n b f z)) := ZFReplay.replay (compilerSourceActualTypedUniqueOutputExists_kernel_certificate w n b f z)

def compilerAllInternalSourceTypedUniqueOutputExistsSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerUniqueFiberSyntax.allSourceTypedUniqueLaw w))).close

theorem source_compilerAllInternalSourceTypedUniqueOutputExists {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalSourceTypedUniqueOutputExistsSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerUniqueFiber.all_source_typed_unique hZ w h0

theorem compilerAllInternalSourceTypedUniqueOutputExists_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalSourceTypedUniqueOutputExistsSentence w)) := TheoryTransport.sentence (source_compilerAllInternalSourceTypedUniqueOutputExists w)

theorem native_compilerAllInternalSourceTypedUniqueOutputExists {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalSourceTypedUniqueOutputExistsSentence w)) := ZFReplay.replay (compilerAllInternalSourceTypedUniqueOutputExists_kernel_certificate w)

end PPAC.Migration.Internal.ObjectProjectCompilerUnique
