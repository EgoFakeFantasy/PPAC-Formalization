import PPAC.Migration.Internal.ProofMPNode

/-! 原MP六项查询、复合蕴含码见证、全部赋值界与完整纯关系式节点的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectProofMPNode
open Source SourceAlgebra SourceLogic OmegaSyntax

def mpConclusionQueryIffSentence {m} (env : Fin 5 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp (((PureSyntaxExprQuery.query ProofMPSyntax.conclusionQuery w env).iff (FormulaCodeSyntax.formulaCode w (env 1) z (env 0))))))).close

theorem source_mpConclusionQueryIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpConclusionQueryIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofMPQueries.conclusion_iff hZ w z env h0 h1 h2

theorem mpConclusionQueryIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpConclusionQueryIffSentence env w z)) := TheoryTransport.sentence (source_mpConclusionQueryIff env w z)

theorem native_mpConclusionQueryIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpConclusionQueryIffSentence env w z)) := ZFReplay.replay (mpConclusionQueryIff_kernel_certificate env w z)

def mpAntecedentQueryIffSentence {m} (env : Fin 5 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp (((PureSyntaxExprQuery.query ProofMPSyntax.antecedentQuery w env).iff (FormulaCodeSyntax.formulaCode w (env 4) z (env 0))))))).close

theorem source_mpAntecedentQueryIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpAntecedentQueryIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofMPQueries.antecedent_iff hZ w z env h0 h1 h2

theorem mpAntecedentQueryIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpAntecedentQueryIffSentence env w z)) := TheoryTransport.sentence (source_mpAntecedentQueryIff env w z)

theorem native_mpAntecedentQueryIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpAntecedentQueryIffSentence env w z)) := ZFReplay.replay (mpAntecedentQueryIff_kernel_certificate env w z)

def mpLeftFreeProjectionIffSentence {m} (env : Fin 5 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp (((ProjectionExprQuery.query ProofMPSyntax.leftFreeQuery w env).iff (RawCodeFieldSyntax.field w (env 2) z (env 0))))))).close

theorem source_mpLeftFreeProjectionIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpLeftFreeProjectionIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofMPQueries.leftFree_iff hZ w z env h0 h1 h2

theorem mpLeftFreeProjectionIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpLeftFreeProjectionIffSentence env w z)) := TheoryTransport.sentence (source_mpLeftFreeProjectionIff env w z)

theorem native_mpLeftFreeProjectionIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpLeftFreeProjectionIffSentence env w z)) := ZFReplay.replay (mpLeftFreeProjectionIff_kernel_certificate env w z)

def mpLeftFormulaProjectionIffSentence {m} (env : Fin 5 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp (((ProjectionExprQuery.query ProofMPSyntax.leftFormulaQuery w env).iff (ProofSubstitutionProjectionSyntax.atOne w (env 2) (env 4)))))).close

theorem source_mpLeftFormulaProjectionIff {m} (env : Fin 5 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpLeftFormulaProjectionIffSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inl rfl)
  exact ProofMPQueries.leftFormula_iff hZ w env h0 h1

theorem mpLeftFormulaProjectionIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpLeftFormulaProjectionIffSentence env w)) := TheoryTransport.sentence (source_mpLeftFormulaProjectionIff env w)

theorem native_mpLeftFormulaProjectionIff {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpLeftFormulaProjectionIffSentence env w)) := ZFReplay.replay (mpLeftFormulaProjectionIff_kernel_certificate env w)

def mpRightFreeProjectionIffSentence {m} (env : Fin 5 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp (((ProjectionExprQuery.query ProofMPSyntax.rightFreeQuery w env).iff (RawCodeFieldSyntax.field w (env 3) z (env 0))))))).close

theorem source_mpRightFreeProjectionIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpRightFreeProjectionIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofMPQueries.rightFree_iff hZ w z env h0 h1 h2

theorem mpRightFreeProjectionIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpRightFreeProjectionIffSentence env w z)) := TheoryTransport.sentence (source_mpRightFreeProjectionIff env w z)

theorem native_mpRightFreeProjectionIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpRightFreeProjectionIffSentence env w z)) := ZFReplay.replay (mpRightFreeProjectionIff_kernel_certificate env w z)

def mpRightImplicationProjectionIffSentence {m} (env : Fin 5 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp (((ProjectionExprQuery.query ProofMPSyntax.rightImplicationQuery w env).iff (ProofMPSyntax.implicationRead w (env 3) (env 4) (env 1)))))).close

theorem source_mpRightImplicationProjectionIff {m} (env : Fin 5 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpRightImplicationProjectionIffSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inl rfl)
  exact ProofMPQueries.rightImplication_iff hZ w env h0 h1

theorem mpRightImplicationProjectionIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpRightImplicationProjectionIffSentence env w)) := TheoryTransport.sentence (source_mpRightImplicationProjectionIff env w)

theorem native_mpRightImplicationProjectionIff {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpRightImplicationProjectionIffSentence env w)) := ZFReplay.replay (mpRightImplicationProjectionIff_kernel_certificate env w)

def mpImplicationGraphIffSentence {m} (env : Fin 5 → Fin m) (w q : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp (((HornExprSyntax.graph ProofMPSyntax.implicationExpr w env q).iff (SyntaxNodeSyntax.constructor 2 7 w (SetLanguage.args2 (env 4) (env 1)) q))))).close

theorem source_mpImplicationGraphIff {m} (env : Fin 5 → Fin m) (w q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpImplicationGraphIffSentence env w q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inl rfl)
  exact ProofMPQueries.implication_graph_iff hZ w q env h0 h1

theorem mpImplicationGraphIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpImplicationGraphIffSentence env w q)) := TheoryTransport.sentence (source_mpImplicationGraphIff env w q)

theorem native_mpImplicationGraphIff {m} (env : Fin 5 → Fin m) (w q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpImplicationGraphIffSentence env w q)) := ZFReplay.replay (mpImplicationGraphIff_kernel_certificate env w q)

def mpRightImplicationAtConstructorIffSentence {m} (env : Fin 5 → Fin m) (w q : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((SyntaxNodeSyntax.constructor 2 7 w (SetLanguage.args2 (env 4) (env 1)) q).imp (((ProjectionExprQuery.query ProofMPSyntax.rightImplicationQuery w env).iff (ProofSubstitutionProjectionSyntax.atOne w (env 3) q)))))).close

theorem source_mpRightImplicationAtConstructorIff {m} (env : Fin 5 → Fin m) (w q : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpRightImplicationAtConstructorIffSentence env w q) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 2 7 w (SetLanguage.args2 (env 4) (env 1)) q) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (SyntaxNodeSyntax.constructor 2 7 w (SetLanguage.args2 (env 4) (env 1)) q) := .hyp (Or.inl rfl)
  exact ProofMPQueries.rightImplication_at hZ w q env h0 h1 h2

theorem mpRightImplicationAtConstructorIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpRightImplicationAtConstructorIffSentence env w q)) := TheoryTransport.sentence (source_mpRightImplicationAtConstructorIff env w q)

theorem native_mpRightImplicationAtConstructorIff {m} (env : Fin 5 → Fin m) (w q : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpRightImplicationAtConstructorIffSentence env w q)) := ZFReplay.replay (mpRightImplicationAtConstructorIff_kernel_certificate env w q)

def mpAllFourProjectionsIffSentence {m} (env : Fin 5 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp (((ProofMPSyntax.projections w env).iff (ProofMPSyntax.metadata w z env)))))).close

theorem source_mpAllFourProjectionsIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpAllFourProjectionsIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofMPQueries.projections_iff hZ w z env h0 h1 h2

theorem mpAllFourProjectionsIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpAllFourProjectionsIffSentence env w z)) := TheoryTransport.sentence (source_mpAllFourProjectionsIff env w z)

theorem native_mpAllFourProjectionsIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpAllFourProjectionsIffSentence env w z)) := ZFReplay.replay (mpAllFourProjectionsIff_kernel_certificate env w z)

def mpBothFormulaQueriesIffSentence {m} (env : Fin 5 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp (((ProofMPAllQueries.formulaQueries w env).iff (ProofMPAllQueries.formulas w z env)))))).close

theorem source_mpBothFormulaQueriesIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpBothFormulaQueriesIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofMPAllQueries.formulas_iff hZ w z env h0 h1 h2

theorem mpBothFormulaQueriesIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpBothFormulaQueriesIffSentence env w z)) := TheoryTransport.sentence (source_mpBothFormulaQueriesIff env w z)

theorem native_mpBothFormulaQueriesIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpBothFormulaQueriesIffSentence env w z)) := ZFReplay.replay (mpBothFormulaQueriesIff_kernel_certificate env w z)

def mpAllSixQueriesIffSentence {m} (env : Fin 5 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp (((ProofMPAllQueries.bundle w env).iff (ProofMPAllQueries.specification w z env)))))).close

theorem source_mpAllSixQueriesIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpAllSixQueriesIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofMPAllQueries.bundle_iff hZ w z env h0 h1 h2

theorem mpAllSixQueriesIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpAllSixQueriesIffSentence env w z)) := TheoryTransport.sentence (source_mpAllSixQueriesIff env w z)

theorem native_mpAllSixQueriesIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpAllSixQueriesIffSentence env w z)) := ZFReplay.replay (mpAllSixQueriesIff_kernel_certificate env w z)

def mpAntecedentProjectionBoundSentence {m} (env : Fin 5 → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((ProjectionExprQuery.query ProofMPSyntax.leftFormulaQuery w env).imp ((NaturalAdditionBounds.below (env 4) (env 2)))))).close

theorem source_mpAntecedentProjectionBound {m} (env : Fin 5 → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpAntecedentProjectionBoundSentence env w) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.query ProofMPSyntax.leftFormulaQuery w env) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectionExprQuery.query ProofMPSyntax.leftFormulaQuery w env) := .hyp (Or.inl rfl)
  exact ProofMPBounds.leftFormula_bound hZ w env h0 h1 h2

theorem mpAntecedentProjectionBound_kernel_certificate {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpAntecedentProjectionBoundSentence env w)) := TheoryTransport.sentence (source_mpAntecedentProjectionBound env w)

theorem native_mpAntecedentProjectionBound {m} (env : Fin 5 → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpAntecedentProjectionBoundSentence env w)) := ZFReplay.replay (mpAntecedentProjectionBound_kernel_certificate env w)

def mpAllAssignmentBoundsSentence {m} (env : Fin 5 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.mpShape.head w env row).imp ((ProjectionExprQuery.query ProofMPSyntax.leftFormulaQuery w env).imp ((HornExprBounds.environmentBound 5 row env)))))).close

theorem source_mpAllAssignmentBounds {m} (env : Fin 5 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpAllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionExprQuery.query ProofMPSyntax.leftFormulaQuery w env) (Context.add (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.mpShape.head w env row) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.mpShape.head w env row) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectionExprQuery.query ProofMPSyntax.leftFormulaQuery w env) := .hyp (Or.inl rfl)
  exact ProofMPBounds.environment_bound hZ w row env h0 h1 h2 h3

theorem mpAllAssignmentBounds_kernel_certificate {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpAllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_mpAllAssignmentBounds env w row)

theorem native_mpAllAssignmentBounds {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpAllAssignmentBoundsSentence env w row)) := ZFReplay.replay (mpAllAssignmentBounds_kernel_certificate env w row)

def mpActualFourFieldHeadIffSentence {m} (env : Fin 5 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectProofNode.mpShape.head w env row).iff (SyntaxNodeSyntax.constructor 4 2 w (fun j : Fin 4 => env j.castSucc) row))))).close

theorem source_mpActualFourFieldHeadIff {m} (env : Fin 5 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpActualFourFieldHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inl rfl)
  exact ProofMPBounds.head_constructor_iff hZ w row env h0 h1

theorem mpActualFourFieldHeadIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpActualFourFieldHeadIffSentence env w row)) := TheoryTransport.sentence (source_mpActualFourFieldHeadIff env w row)

theorem native_mpActualFourFieldHeadIff {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpActualFourFieldHeadIffSentence env w row)) := ZFReplay.replay (mpActualFourFieldHeadIff_kernel_certificate env w row)

def mpBoundedMatrixIffSentence {m} (env : Fin 5 → Fin m) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofMPNodeSyntax.boundedMatrix w row env).iff (ProofMPNodeSyntax.specificationMatrix w z row env))))).close

theorem source_mpBoundedMatrixIff {m} (env : Fin 5 → Fin m) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpBoundedMatrixIffSentence env w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofMPNode.matrix_iff hZ w z row env h0 h1

theorem mpBoundedMatrixIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpBoundedMatrixIffSentence env w z row)) := TheoryTransport.sentence (source_mpBoundedMatrixIff env w z row)

theorem native_mpBoundedMatrixIff {m} (env : Fin 5 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpBoundedMatrixIffSentence env w z row)) := ZFReplay.replay (mpBoundedMatrixIff_kernel_certificate env w z row)

def mpFullPureRelationalNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((ProofMPNodeSyntax.node w row).iff (ProofMPNodeSyntax.specification w z row))))).close

theorem source_mpFullPureRelationalNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (mpFullPureRelationalNodeIffSentence w z row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProofMPNode.node_iff hZ w z row h0 h1

theorem mpFullPureRelationalNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (mpFullPureRelationalNodeIffSentence w z row)) := TheoryTransport.sentence (source_mpFullPureRelationalNodeIff w z row)

theorem native_mpFullPureRelationalNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (mpFullPureRelationalNodeIffSentence w z row)) := ZFReplay.replay (mpFullPureRelationalNodeIff_kernel_certificate w z row)

end PPAC.Migration.Internal.ObjectProofMPNode
