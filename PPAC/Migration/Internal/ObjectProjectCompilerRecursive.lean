import PPAC.Migration.Internal.ProjectCompilerRecursive

/-! All internal actual Project compiler recursive equations; full source correctness remains unproved in the original nativeZF kernel; complete schema tests and Con remain unproved. -/
namespace PPAC.Migration.Internal.ObjectProjectCompilerRecursive
open Source SourceAlgebra SourceLogic OmegaSyntax

def compilerActualChildReadIffSentence {m} (w a c h n x b q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp ((ProjectCompilerRecursionSyntax.graph w c h n).imp ((Formula.mem x n).imp (((SyntaxContextReadSyntax.read h x b q).iff (ProjectCompilerCodeSyntax.compiled w x b q)))))))).close

theorem source_compilerActualChildReadIff {m} (w a c h n x b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualChildReadIffSentence w a c h n x b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem x n) (Context.add (ProjectCompilerRecursionSyntax.graph w c h n) (Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (ProjectCompilerRecursionSyntax.graph w c h n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (Formula.mem x n) := .hyp (Or.inl rfl)
  exact ProjectCompilerQueryBridge.at_member hZ w a c h n x b q h0 h1 h2 h3 h4

theorem compilerActualChildReadIff_kernel_certificate {m} (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualChildReadIffSentence w a c h n x b q)) := TheoryTransport.sentence (source_compilerActualChildReadIff w a c h n x b q)

theorem native_compilerActualChildReadIff {m} (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualChildReadIffSentence w a c h n x b q)) := ZFReplay.replay (compilerActualChildReadIff_kernel_certificate w a c h n x b q)

def compilerGuardedChildQueryIffSentence {m} (w a c h n x b q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp ((ProjectCompilerRecursionSyntax.graph w c h n).imp (((ProjectCompilerCaseSyntax.queried ProjectCompilerLocalSyntax.readMatrix (ProjectCompilerLocalSyntax.one h) n x b q).iff (ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q))))))).close

theorem source_compilerGuardedChildQueryIff {m} (w a c h n x b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerGuardedChildQueryIffSentence w a c h n x b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerRecursionSyntax.graph w c h n) (Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerRecursionSyntax.graph w c h n) := .hyp (Or.inl rfl)
  exact ProjectCompilerQueryBridge.guarded hZ w a c h n x b q h0 h1 h2 h3

theorem compilerGuardedChildQueryIff_kernel_certificate {m} (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerGuardedChildQueryIffSentence w a c h n x b q)) := TheoryTransport.sentence (source_compilerGuardedChildQueryIff w a c h n x b q)

theorem native_compilerGuardedChildQueryIff {m} (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerGuardedChildQueryIffSentence w a c h n x b q)) := ZFReplay.replay (compilerGuardedChildQueryIff_kernel_certificate w a c h n x b q)

def compilerAllInternalChildQueriesSentence {m} (w a c h n : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp ((ProjectCompilerRecursionSyntax.graph w c h n).imp ((ProjectCompilerQuerySyntax.equivalent ProjectCompilerLocalSyntax.readMatrix (ProjectCompilerLocalSyntax.one h) ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n)))))).close

theorem source_compilerAllInternalChildQueries {m} (w a c h n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalChildQueriesSentence w a c h n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerRecursionSyntax.graph w c h n) (Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerRecursionSyntax.graph w c h n) := .hyp (Or.inl rfl)
  exact ProjectCompilerQueryBridge.all_queries hZ w a c h n h0 h1 h2 h3

theorem compilerAllInternalChildQueries_kernel_certificate {m} (w a c h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalChildQueriesSentence w a c h n)) := TheoryTransport.sentence (source_compilerAllInternalChildQueries w a c h n)

theorem native_compilerAllInternalChildQueries {m} (w a c h n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalChildQueriesSentence w a c h n)) := ZFReplay.replay (compilerAllInternalChildQueries_kernel_certificate w a c h n)

def compilerSuccessorQueryIffSentence {m} (w a c h n x b q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp ((ProjectCompilerRecursionSyntax.graph w c h n).imp (((ProjectCompilerCaseSyntax.advanced ProjectCompilerLocalSyntax.readMatrix (ProjectCompilerLocalSyntax.one h) n x b q).iff (ProjectCompilerCaseSyntax.advanced ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q))))))).close

theorem source_compilerSuccessorQueryIff {m} (w a c h n x b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerSuccessorQueryIffSentence w a c h n x b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerRecursionSyntax.graph w c h n) (Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerRecursionSyntax.graph w c h n) := .hyp (Or.inl rfl)
  exact ProjectCompilerQueryTransport.advanced_iff ProjectCompilerLocalSyntax.readMatrix (ProjectCompilerLocalSyntax.one h) ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q (ProjectCompilerQueryBridge.all_queries hZ w a c h n h0 h1 h2 h3)

theorem compilerSuccessorQueryIff_kernel_certificate {m} (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerSuccessorQueryIffSentence w a c h n x b q)) := TheoryTransport.sentence (source_compilerSuccessorQueryIff w a c h n x b q)

theorem native_compilerSuccessorQueryIff {m} (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerSuccessorQueryIffSentence w a c h n x b q)) := ZFReplay.replay (compilerSuccessorQueryIff_kernel_certificate w a c h n x b q)

def compilerScopedChildQueryIffSentence {m} (advance : Bool) (w a c h n x b q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp ((ProjectCompilerRecursionSyntax.graph w c h n).imp (((ProjectCompilerCaseSyntax.check advance ProjectCompilerLocalSyntax.readMatrix (ProjectCompilerLocalSyntax.one h) n x b q).iff (ProjectCompilerCaseSyntax.check advance ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q))))))).close

theorem source_compilerScopedChildQueryIff {m} (advance : Bool) (w a c h n x b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerScopedChildQueryIffSentence advance w a c h n x b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerRecursionSyntax.graph w c h n) (Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerRecursionSyntax.graph w c h n) := .hyp (Or.inl rfl)
  exact ProjectCompilerQueryTransport.check_iff advance ProjectCompilerLocalSyntax.readMatrix (ProjectCompilerLocalSyntax.one h) ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) n x b q (ProjectCompilerQueryBridge.all_queries hZ w a c h n h0 h1 h2 h3)

theorem compilerScopedChildQueryIff_kernel_certificate {m} (advance : Bool) (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerScopedChildQueryIffSentence advance w a c h n x b q)) := TheoryTransport.sentence (source_compilerScopedChildQueryIff advance w a c h n x b q)

theorem native_compilerScopedChildQueryIff {m} (advance : Bool) (w a c h n x b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerScopedChildQueryIffSentence advance w a c h n x b q)) := ZFReplay.replay (compilerScopedChildQueryIff_kernel_certificate advance w a c h n x b q)

def compilerAllTwelveCasesIffSentence {m} (w a c h n b z q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp ((ProjectCompilerRecursionSyntax.graph w c h n).imp (((ProjectCompilerLocalSyntax.casesAt w b q h n z).iff (ProjectCompilerRecursiveSyntax.casesAt w b z n q))))))).close

theorem source_compilerAllTwelveCasesIff {m} (w a c h n b z q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllTwelveCasesIffSentence w a c h n b z q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerRecursionSyntax.graph w c h n) (Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerRecursionSyntax.graph w c h n) := .hyp (Or.inl rfl)
  exact ProjectCompilerCaseTransport.all_cases ProjectCompilerLocalSyntax.readMatrix (ProjectCompilerLocalSyntax.one h) ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w) w b z n q (ProjectCompilerQueryBridge.all_queries hZ w a c h n h0 h1 h2 h3)

theorem compilerAllTwelveCasesIff_kernel_certificate {m} (w a c h n b z q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllTwelveCasesIffSentence w a c h n b z q)) := TheoryTransport.sentence (source_compilerAllTwelveCasesIff w a c h n b z q)

theorem native_compilerAllTwelveCasesIff {m} (w a c h n b z q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllTwelveCasesIffSentence w a c h n b z q)) := ZFReplay.replay (compilerAllTwelveCasesIff_kernel_certificate w a c h n b z q)

def compilerActualLocalRecursiveIffSentence {m} (w a c h n b q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp ((ProjectCompilerRecursionSyntax.graph w c h n).imp (((ProjectCompilerLocalSyntax.localStep w b q h n).iff (ProjectCompilerRecursiveSyntax.criterion w n b q))))))).close

theorem source_compilerActualLocalRecursiveIff {m} (w a c h n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualLocalRecursiveIffSentence w a c h n b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerRecursionSyntax.graph w c h n) (Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerRecursionSyntax.graph w c h n) := .hyp (Or.inl rfl)
  exact ProjectCompilerLocalBridge.local_iff hZ w a c h n b q h0 h1 h2 h3

theorem compilerActualLocalRecursiveIff_kernel_certificate {m} (w a c h n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualLocalRecursiveIffSentence w a c h n b q)) := TheoryTransport.sentence (source_compilerActualLocalRecursiveIff w a c h n b q)

theorem native_compilerActualLocalRecursiveIff {m} (w a c h n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualLocalRecursiveIffSentence w a c h n b q)) := ZFReplay.replay (compilerActualLocalRecursiveIff_kernel_certificate w a c h n b q)

def compilerActualStateRecursiveIffSentence {m} (w a c n h v b q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp ((ProjectCompilerRecursionSyntax.graph w c h n).imp ((ProjectCompilerStateSyntax.state w c n h v).imp (((GraphSyntax.edge v b q).iff (ProjectCompilerRecursiveSyntax.criterion w n b q)))))))).close

theorem source_compilerActualStateRecursiveIff {m} (w a c n h v b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerActualStateRecursiveIffSentence w a c n h v b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerStateSyntax.state w c n h v) (Context.add (ProjectCompilerRecursionSyntax.graph w c h n) (Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (ProjectCompilerRecursionSyntax.graph w c h n) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (ProjectCompilerStateSyntax.state w c n h v) := .hyp (Or.inl rfl)
  exact ProjectCompilerRecursivePoint.at_state hZ w a c n h v b q h0 h1 h2 h3 h4

theorem compilerActualStateRecursiveIff_kernel_certificate {m} (w a c n h v b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerActualStateRecursiveIffSentence w a c n h v b q)) := TheoryTransport.sentence (source_compilerActualStateRecursiveIff w a c n h v b q)

theorem native_compilerActualStateRecursiveIff {m} (w a c n h v b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerActualStateRecursiveIffSentence w a c n h v b q)) := ZFReplay.replay (compilerActualStateRecursiveIff_kernel_certificate w a c n h v b q)

def compilerAtEvaluationRecursiveIffSentence {m} (w a c n v b q : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem n w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp ((ProjectCompilerEvaluationSyntax.evaluation w c n v).imp (((ProjectCompilerCodeSyntax.compiled w n b q).iff (ProjectCompilerRecursiveSyntax.criterion w n b q))))))).close

theorem source_compilerAtEvaluationRecursiveIff {m} (w a c n v b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAtEvaluationRecursiveIffSentence w a c n v b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerEvaluationSyntax.evaluation w c n v) (Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (Formula.mem n w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem n w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectCompilerEvaluationSyntax.evaluation w c n v) := .hyp (Or.inl rfl)
  exact ProjectCompilerRecursivePoint.at_value hZ w a c n v b q h0 h1 h2 h3

theorem compilerAtEvaluationRecursiveIff_kernel_certificate {m} (w a c n v b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAtEvaluationRecursiveIffSentence w a c n v b q)) := TheoryTransport.sentence (source_compilerAtEvaluationRecursiveIff w a c n v b q)

theorem native_compilerAtEvaluationRecursiveIff {m} (w a c n v b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAtEvaluationRecursiveIffSentence w a c n v b q)) := ZFReplay.replay (compilerAtEvaluationRecursiveIff_kernel_certificate w a c n v b q)

def compilerAtCarrierRecursiveIffSentence {m} (w a c n b q : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerCodeSyntax.carrier w a c).imp (((ProjectCompilerCodeSyntax.compiled w n b q).iff (ProjectCompilerRecursiveSyntax.criterion w n b q))))).close

theorem source_compilerAtCarrierRecursiveIff {m} (w a c n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAtCarrierRecursiveIffSentence w a c n b q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectCompilerCodeSyntax.carrier w a c) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectCompilerCodeSyntax.carrier w a c) := .hyp (Or.inl rfl)
  exact ProjectCompilerRecursive.at_carrier hZ w a c n b q h0 h1

theorem compilerAtCarrierRecursiveIff_kernel_certificate {m} (w a c n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAtCarrierRecursiveIffSentence w a c n b q)) := TheoryTransport.sentence (source_compilerAtCarrierRecursiveIff w a c n b q)

theorem native_compilerAtCarrierRecursiveIff {m} (w a c n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAtCarrierRecursiveIffSentence w a c n b q)) := ZFReplay.replay (compilerAtCarrierRecursiveIff_kernel_certificate w a c n b q)

def compilerAllCandidatesRecursiveIffSentence {m} (w n b q : Fin m) : Source.Sentence := ((omega w).imp (((ProjectCompilerCodeSyntax.compiled w n b q).iff (ProjectCompilerRecursiveSyntax.criterion w n b q)))).close

theorem source_compilerAllCandidatesRecursiveIff {m} (w n b q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllCandidatesRecursiveIffSentence w n b q) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerRecursive.recursive_iff hZ w n b q h0

theorem compilerAllCandidatesRecursiveIff_kernel_certificate {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllCandidatesRecursiveIffSentence w n b q)) := TheoryTransport.sentence (source_compilerAllCandidatesRecursiveIff w n b q)

theorem native_compilerAllCandidatesRecursiveIff {m} (w n b q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllCandidatesRecursiveIffSentence w n b q)) := ZFReplay.replay (compilerAllCandidatesRecursiveIff_kernel_certificate w n b q)

def compilerAllInternalRecursiveLawSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((ProjectCompilerRecursive.universalLaw w))).close

theorem source_compilerAllInternalRecursiveLaw {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (compilerAllInternalRecursiveLawSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectCompilerRecursive.all_law hZ w h0

theorem compilerAllInternalRecursiveLaw_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (compilerAllInternalRecursiveLawSentence w)) := TheoryTransport.sentence (source_compilerAllInternalRecursiveLaw w)

theorem native_compilerAllInternalRecursiveLaw {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (compilerAllInternalRecursiveLawSentence w)) := ZFReplay.replay (compilerAllInternalRecursiveLaw_kernel_certificate w)

end PPAC.Migration.Internal.ObjectProjectCompilerRecursive
