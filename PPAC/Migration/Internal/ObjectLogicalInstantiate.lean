import PPAC.Migration.Internal.LogicalInstantiateNode

/-! 原逻辑20／23／25完整纯关系节点、查询、搜索界与数值头的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectLogicalInstantiate
open Source SourceAlgebra SourceLogic OmegaSyntax

def logicalTwentyTwentyThreeAtBoundQueriesIffSentence {m} (env : Fin 4 → Fin m) (w z A : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((successor A z).imp (((LogicalInstantiateSyntax.bundle4 w env).iff (LogicalInstantiateSyntax.atBound4 w z A env))))))).close

theorem source_logicalTwentyTwentyThreeAtBoundQueriesIff {m} (env : Fin 4 → Fin m) (w z A : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyTwentyThreeAtBoundQueriesIffSentence env w z A) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor A z) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor A z) := .hyp (Or.inl rfl)
  exact LogicalInstantiateAllQueries.at_bound4_iff hZ w z A env h0 h1 h2 h3

theorem logicalTwentyTwentyThreeAtBoundQueriesIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyTwentyThreeAtBoundQueriesIffSentence env w z A)) := TheoryTransport.sentence (source_logicalTwentyTwentyThreeAtBoundQueriesIff env w z A)

theorem native_logicalTwentyTwentyThreeAtBoundQueriesIff {m} (env : Fin 4 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyTwentyThreeAtBoundQueriesIffSentence env w z A)) := ZFReplay.replay (logicalTwentyTwentyThreeAtBoundQueriesIff_kernel_certificate env w z A)

def logicalTwentyTwentyThreeAllQueriesIffSentence {m} (env : Fin 4 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp (((LogicalInstantiateSyntax.bundle4 w env).iff (LogicalInstantiateSyntax.specification4 w z env)))))).close

theorem source_logicalTwentyTwentyThreeAllQueriesIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyTwentyThreeAllQueriesIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact LogicalInstantiateAllQueries.bundle4_iff hZ w z env h0 h1 h2

theorem logicalTwentyTwentyThreeAllQueriesIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyTwentyThreeAllQueriesIffSentence env w z)) := TheoryTransport.sentence (source_logicalTwentyTwentyThreeAllQueriesIff env w z)

theorem native_logicalTwentyTwentyThreeAllQueriesIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyTwentyThreeAllQueriesIffSentence env w z)) := ZFReplay.replay (logicalTwentyTwentyThreeAllQueriesIff_kernel_certificate env w z)

def logicalTwentyTwentyThreeAllAssignmentBoundsSentence {m} (universal : Bool) (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornExprSyntax.graph (LogicalInstantiateNodeSyntax.head4 universal) w env row).imp ((HornExprBounds.environmentBound 4 row env))))).close

theorem source_logicalTwentyTwentyThreeAllAssignmentBounds {m} (universal : Bool) (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyTwentyThreeAllAssignmentBoundsSentence universal env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (LogicalInstantiateNodeSyntax.head4 universal) w env row) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (LogicalInstantiateNodeSyntax.head4 universal) w env row) := .hyp (Or.inl rfl)
  exact LogicalInstantiateNodeSyntax.head4_bounds hZ universal w row env h0 h1 h2

theorem logicalTwentyTwentyThreeAllAssignmentBounds_kernel_certificate {m} (universal : Bool) (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyTwentyThreeAllAssignmentBoundsSentence universal env w row)) := TheoryTransport.sentence (source_logicalTwentyTwentyThreeAllAssignmentBounds universal env w row)

theorem native_logicalTwentyTwentyThreeAllAssignmentBounds {m} (universal : Bool) (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyTwentyThreeAllAssignmentBoundsSentence universal env w row)) := ZFReplay.replay (logicalTwentyTwentyThreeAllAssignmentBounds_kernel_certificate universal env w row)

def logicalTwentyTwentyThreeBoundedMatrixIffSentence {m} (universal : Bool) (env : Fin 4 → Fin m) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalInstantiateNodeSyntax.boundedMatrix4 universal w row env).iff (LogicalInstantiateNodeSyntax.specificationMatrix4 universal w z row env))))).close

theorem source_logicalTwentyTwentyThreeBoundedMatrixIff {m} (universal : Bool) (env : Fin 4 → Fin m) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyTwentyThreeBoundedMatrixIffSentence universal env w z row) := by
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
  exact LogicalInstantiateNode.matrix4_iff hZ universal w z row env h0 h1

theorem logicalTwentyTwentyThreeBoundedMatrixIff_kernel_certificate {m} (universal : Bool) (env : Fin 4 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyTwentyThreeBoundedMatrixIffSentence universal env w z row)) := TheoryTransport.sentence (source_logicalTwentyTwentyThreeBoundedMatrixIff universal env w z row)

theorem native_logicalTwentyTwentyThreeBoundedMatrixIff {m} (universal : Bool) (env : Fin 4 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyTwentyThreeBoundedMatrixIffSentence universal env w z row)) := ZFReplay.replay (logicalTwentyTwentyThreeBoundedMatrixIff_kernel_certificate universal env w z row)

def logicalTwentyTwentyThreeWholeNodeIffSentence {m} (universal : Bool) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalInstantiateNodeSyntax.node4 universal w row).iff (LogicalInstantiateNodeSyntax.specification4 universal w z row))))).close

theorem source_logicalTwentyTwentyThreeWholeNodeIff {m} (universal : Bool) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyTwentyThreeWholeNodeIffSentence universal w z row) := by
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
  exact LogicalInstantiateNode.node4_iff hZ universal w z row h0 h1

theorem logicalTwentyTwentyThreeWholeNodeIff_kernel_certificate {m} (universal : Bool) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyTwentyThreeWholeNodeIffSentence universal w z row)) := TheoryTransport.sentence (source_logicalTwentyTwentyThreeWholeNodeIff universal w z row)

theorem native_logicalTwentyTwentyThreeWholeNodeIff {m} (universal : Bool) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyTwentyThreeWholeNodeIffSentence universal w z row)) := ZFReplay.replay (logicalTwentyTwentyThreeWholeNodeIff_kernel_certificate universal w z row)

def logicalTwentyTwentyThreeWholeNormalizedNodeIffSentence {m} (universal : Bool) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalInstantiateNodeSyntax.node4 universal w row).iff (LogicalInstantiateNodeSyntax.normalized4 universal w z row))))).close

theorem source_logicalTwentyTwentyThreeWholeNormalizedNodeIff {m} (universal : Bool) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyTwentyThreeWholeNormalizedNodeIffSentence universal w z row) := by
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
  exact LogicalInstantiateNode.normalized_node4_iff hZ universal w z row h0 h1

theorem logicalTwentyTwentyThreeWholeNormalizedNodeIff_kernel_certificate {m} (universal : Bool) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyTwentyThreeWholeNormalizedNodeIffSentence universal w z row)) := TheoryTransport.sentence (source_logicalTwentyTwentyThreeWholeNormalizedNodeIff universal w z row)

theorem native_logicalTwentyTwentyThreeWholeNormalizedNodeIff {m} (universal : Bool) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyTwentyThreeWholeNormalizedNodeIffSentence universal w z row)) := ZFReplay.replay (logicalTwentyTwentyThreeWholeNormalizedNodeIff_kernel_certificate universal w z row)

def logicalTwentyFiveAtBoundQueriesIffSentence {m} (env : Fin 6 → Fin m) (w z A : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp ((successor A z).imp (((LogicalInstantiateSyntax.bundle6 w env).iff (LogicalInstantiateSyntax.atBound6 w z A env))))))).close

theorem source_logicalTwentyFiveAtBoundQueriesIff {m} (env : Fin 6 → Fin m) (w z A : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyFiveAtBoundQueriesIffSentence env w z A) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor A z) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor A z) := .hyp (Or.inl rfl)
  exact LogicalInstantiateAllQueries.at_bound6_iff hZ w z A env h0 h1 h2 h3

theorem logicalTwentyFiveAtBoundQueriesIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyFiveAtBoundQueriesIffSentence env w z A)) := TheoryTransport.sentence (source_logicalTwentyFiveAtBoundQueriesIff env w z A)

theorem native_logicalTwentyFiveAtBoundQueriesIff {m} (env : Fin 6 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyFiveAtBoundQueriesIffSentence env w z A)) := ZFReplay.replay (logicalTwentyFiveAtBoundQueriesIff_kernel_certificate env w z A)

def logicalTwentyFiveAllQueriesIffSentence {m} (env : Fin 6 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((empty z).imp (((LogicalInstantiateSyntax.bundle6 w env).iff (LogicalInstantiateSyntax.specification6 w z env)))))).close

theorem source_logicalTwentyFiveAllQueriesIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyFiveAllQueriesIffSentence env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact LogicalInstantiateAllQueries.bundle6_iff hZ w z env h0 h1 h2

theorem logicalTwentyFiveAllQueriesIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyFiveAllQueriesIffSentence env w z)) := TheoryTransport.sentence (source_logicalTwentyFiveAllQueriesIff env w z)

theorem native_logicalTwentyFiveAllQueriesIff {m} (env : Fin 6 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyFiveAllQueriesIffSentence env w z)) := ZFReplay.replay (logicalTwentyFiveAllQueriesIff_kernel_certificate env w z)

def logicalTwentyFiveAllAssignmentBoundsSentence {m} (env : Fin 6 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((HornExprSyntax.graph LogicalInstantiateNodeSyntax.head6 w env row).imp ((HornExprBounds.environmentBound 6 row env))))).close

theorem source_logicalTwentyFiveAllAssignmentBounds {m} (env : Fin 6 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyFiveAllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph LogicalInstantiateNodeSyntax.head6 w env row) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph LogicalInstantiateNodeSyntax.head6 w env row) := .hyp (Or.inl rfl)
  exact LogicalInstantiateNodeSyntax.head6_bounds hZ w row env h0 h1 h2

theorem logicalTwentyFiveAllAssignmentBounds_kernel_certificate {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyFiveAllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_logicalTwentyFiveAllAssignmentBounds env w row)

theorem native_logicalTwentyFiveAllAssignmentBounds {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyFiveAllAssignmentBoundsSentence env w row)) := ZFReplay.replay (logicalTwentyFiveAllAssignmentBounds_kernel_certificate env w row)

def logicalTwentyFiveBoundedMatrixIffSentence {m} (env : Fin 6 → Fin m) (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalInstantiateNodeSyntax.boundedMatrix6 w row env).iff (LogicalInstantiateNodeSyntax.specificationMatrix6 w z row env))))).close

theorem source_logicalTwentyFiveBoundedMatrixIff {m} (env : Fin 6 → Fin m) (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyFiveBoundedMatrixIffSentence env w z row) := by
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
  exact LogicalInstantiateNode.matrix6_iff hZ w z row env h0 h1

theorem logicalTwentyFiveBoundedMatrixIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyFiveBoundedMatrixIffSentence env w z row)) := TheoryTransport.sentence (source_logicalTwentyFiveBoundedMatrixIff env w z row)

theorem native_logicalTwentyFiveBoundedMatrixIff {m} (env : Fin 6 → Fin m) (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyFiveBoundedMatrixIffSentence env w z row)) := ZFReplay.replay (logicalTwentyFiveBoundedMatrixIff_kernel_certificate env w z row)

def logicalTwentyFiveWholeNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalInstantiateNodeSyntax.node6 w row).iff (LogicalInstantiateNodeSyntax.specification6 w z row))))).close

theorem source_logicalTwentyFiveWholeNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyFiveWholeNodeIffSentence w z row) := by
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
  exact LogicalInstantiateNode.node6_iff hZ w z row h0 h1

theorem logicalTwentyFiveWholeNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyFiveWholeNodeIffSentence w z row)) := TheoryTransport.sentence (source_logicalTwentyFiveWholeNodeIff w z row)

theorem native_logicalTwentyFiveWholeNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyFiveWholeNodeIffSentence w z row)) := ZFReplay.replay (logicalTwentyFiveWholeNodeIff_kernel_certificate w z row)

def logicalTwentyFiveWholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalInstantiateNodeSyntax.node6 w row).iff (LogicalInstantiateNodeSyntax.normalized6 w z row))))).close

theorem source_logicalTwentyFiveWholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalTwentyFiveWholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalInstantiateNode.normalized_node6_iff hZ w z row h0 h1

theorem logicalTwentyFiveWholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalTwentyFiveWholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_logicalTwentyFiveWholeNormalizedNodeIff w z row)

theorem native_logicalTwentyFiveWholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalTwentyFiveWholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (logicalTwentyFiveWholeNormalizedNodeIff_kernel_certificate w z row)

def logicalRule20NestedHeadIffSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectLogicalAxiom.rule20.head w env row).iff (LogicalRule20Head.normalized w row env))))).close

theorem source_logicalRule20NestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule20NestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inl rfl)
  exact LogicalRule20Head.head_iff hZ w row env h0 h1

theorem logicalRule20NestedHeadIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule20NestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_logicalRule20NestedHeadIff env w row)

theorem native_logicalRule20NestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule20NestedHeadIffSentence env w row)) := ZFReplay.replay (logicalRule20NestedHeadIff_kernel_certificate env w row)

def logicalRule23NestedHeadIffSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectLogicalAxiom.rule23.head w env row).iff (LogicalRule23Head.normalized w row env))))).close

theorem source_logicalRule23NestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule23NestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inl rfl)
  exact LogicalRule23Head.head_iff hZ w row env h0 h1

theorem logicalRule23NestedHeadIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule23NestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_logicalRule23NestedHeadIff env w row)

theorem native_logicalRule23NestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule23NestedHeadIffSentence env w row)) := ZFReplay.replay (logicalRule23NestedHeadIff_kernel_certificate env w row)

def logicalRule25NestedHeadIffSentence {m} (env : Fin 6 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp (((HornExprSyntax.graph YesMetaZFC.Automation.ObjectLogicalAxiom.rule25.head w env row).iff (LogicalRule25Head.normalized w row env))))).close

theorem source_logicalRule25NestedHeadIff {m} (env : Fin 6 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule25NestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inl rfl)
  exact LogicalRule25Head.head_iff hZ w row env h0 h1

theorem logicalRule25NestedHeadIff_kernel_certificate {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule25NestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_logicalRule25NestedHeadIff env w row)

theorem native_logicalRule25NestedHeadIff {m} (env : Fin 6 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule25NestedHeadIffSentence env w row)) := ZFReplay.replay (logicalRule25NestedHeadIff_kernel_certificate env w row)

end PPAC.Migration.Internal.ObjectLogicalInstantiate
