import PPAC.Migration.Internal.LogicalOriginalNodes

/-! 原逻辑21／24及完整27模式纯关系析取的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectLogicalAbstract
open Source SourceAlgebra SourceLogic OmegaSyntax

def logicalRule21AtSuccessorsQueriesIffSentence {m} (env : Fin 5 → Fin m) (w z A B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp ((successor A z).imp ((successor B (env 0)).imp (((LogicalAbstractSyntax.bundle21 w env).iff (LogicalAbstractSyntax.atSuccessor21 w z A B env)))))))).close

theorem source_logicalRule21AtSuccessorsQueriesIff {m} (env : Fin 5 → Fin m) (w z A B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule21AtSuccessorsQueriesIffSentence env w z A B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B (env 0)) (Context.add (successor A z) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor A z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor B (env 0)) := .hyp (Or.inl rfl)
  exact LogicalAbstractAllQueries.at_successor21_iff hZ w z A B env h0 h1 h2 h3 h4

theorem logicalRule21AtSuccessorsQueriesIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule21AtSuccessorsQueriesIffSentence env w z A B)) := TheoryTransport.sentence (source_logicalRule21AtSuccessorsQueriesIff env w z A B)

theorem native_logicalRule21AtSuccessorsQueriesIff {m} (env : Fin 5 → Fin m) (w z A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule21AtSuccessorsQueriesIffSentence env w z A B)) := ZFReplay.replay (logicalRule21AtSuccessorsQueriesIff_kernel_certificate env w z A B)

def logicalRule21AtOneQueriesIffSentence {m} (env : Fin 5 → Fin m) (w z A : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp ((successor A z).imp (((LogicalAbstractSyntax.bundle21 w env).iff (LogicalAbstractSyntax.atOneSpecification21 w z A env))))))).close

theorem source_logicalRule21AtOneQueriesIff {m} (env : Fin 5 → Fin m) (w z A : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule21AtOneQueriesIffSentence env w z A) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor A z) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor A z) := .hyp (Or.inl rfl)
  exact LogicalAbstractAllQueries.at_one_bundle21_iff hZ w z A env h0 h1 h2 h3

theorem logicalRule21AtOneQueriesIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule21AtOneQueriesIffSentence env w z A)) := TheoryTransport.sentence (source_logicalRule21AtOneQueriesIff env w z A)

theorem native_logicalRule21AtOneQueriesIff {m} (env : Fin 5 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule21AtOneQueriesIffSentence env w z A)) := ZFReplay.replay (logicalRule21AtOneQueriesIff_kernel_certificate env w z A)

def logicalRule21AllQueriesIffSentence {m} (env : Fin 5 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((empty z).imp (((LogicalAbstractSyntax.bundle21 w env).iff (LogicalAbstractSyntax.specification21 w z env)))))).close

theorem source_logicalRule21AllQueriesIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule21AllQueriesIffSentence env w z) := by
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
  exact LogicalAbstractAllQueries.bundle21_iff hZ w z env h0 h1 h2

theorem logicalRule21AllQueriesIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule21AllQueriesIffSentence env w z)) := TheoryTransport.sentence (source_logicalRule21AllQueriesIff env w z)

theorem native_logicalRule21AllQueriesIff {m} (env : Fin 5 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule21AllQueriesIffSentence env w z)) := ZFReplay.replay (logicalRule21AllQueriesIff_kernel_certificate env w z)

def logicalRule21AllAssignmentBoundsSentence {m} (env : Fin 5 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((HornExprSyntax.graph LogicalAbstractNodeSyntax.head21 w env row).imp ((HornExprBounds.environmentBound 5 row env))))).close

theorem source_logicalRule21AllAssignmentBounds {m} (env : Fin 5 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule21AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph LogicalAbstractNodeSyntax.head21 w env row) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph LogicalAbstractNodeSyntax.head21 w env row) := .hyp (Or.inl rfl)
  exact LogicalAbstractNode.head21_bounds hZ w row env h0 h1 h2

theorem logicalRule21AllAssignmentBounds_kernel_certificate {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule21AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_logicalRule21AllAssignmentBounds env w row)

theorem native_logicalRule21AllAssignmentBounds {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule21AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (logicalRule21AllAssignmentBounds_kernel_certificate env w row)

def logicalRule21NumericNestedHeadIffSentence {m} (env : Fin 5 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp (((HornExprSyntax.graph LogicalAbstractNodeSyntax.head21 w env row).iff (LogicalRule21Head.normalized w row env))))).close

theorem source_logicalRule21NumericNestedHeadIff {m} (env : Fin 5 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule21NumericNestedHeadIffSentence env w row) := by
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
  exact LogicalRule21Head.head_iff hZ w row env h0 h1

theorem logicalRule21NumericNestedHeadIff_kernel_certificate {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule21NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_logicalRule21NumericNestedHeadIff env w row)

theorem native_logicalRule21NumericNestedHeadIff {m} (env : Fin 5 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule21NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (logicalRule21NumericNestedHeadIff_kernel_certificate env w row)

def logicalRule21WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalAbstractNodeSyntax.node21 w row).iff (LogicalAbstractNodeSyntax.normalized21 w z row))))).close

theorem source_logicalRule21WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule21WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalAbstractNode.normalized_node21_iff hZ w z row h0 h1

theorem logicalRule21WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule21WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_logicalRule21WholeNormalizedNodeIff w z row)

theorem native_logicalRule21WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule21WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (logicalRule21WholeNormalizedNodeIff_kernel_certificate w z row)

def logicalRule24AtSuccessorsQueriesIffSentence {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((successor A z).imp ((successor B (env 0)).imp (((LogicalAbstractSyntax.bundle24 w env).iff (LogicalAbstractSyntax.atSuccessor24 w z A B env)))))))).close

theorem source_logicalRule24AtSuccessorsQueriesIff {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule24AtSuccessorsQueriesIffSentence env w z A B) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor B (env 0)) (Context.add (successor A z) (Context.add (empty z) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (empty z) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor A z) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (successor B (env 0)) := .hyp (Or.inl rfl)
  exact LogicalAbstractAllQueries.at_successor24_iff hZ w z A B env h0 h1 h2 h3 h4

theorem logicalRule24AtSuccessorsQueriesIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule24AtSuccessorsQueriesIffSentence env w z A B)) := TheoryTransport.sentence (source_logicalRule24AtSuccessorsQueriesIff env w z A B)

theorem native_logicalRule24AtSuccessorsQueriesIff {m} (env : Fin 4 → Fin m) (w z A B : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule24AtSuccessorsQueriesIffSentence env w z A B)) := ZFReplay.replay (logicalRule24AtSuccessorsQueriesIff_kernel_certificate env w z A B)

def logicalRule24AtOneQueriesIffSentence {m} (env : Fin 4 → Fin m) (w z A : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp ((successor A z).imp (((LogicalAbstractSyntax.bundle24 w env).iff (LogicalAbstractSyntax.atOneSpecification24 w z A env))))))).close

theorem source_logicalRule24AtOneQueriesIff {m} (env : Fin 4 → Fin m) (w z A : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule24AtOneQueriesIffSentence env w z A) := by
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
  exact LogicalAbstractAllQueries.at_one_bundle24_iff hZ w z A env h0 h1 h2 h3

theorem logicalRule24AtOneQueriesIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule24AtOneQueriesIffSentence env w z A)) := TheoryTransport.sentence (source_logicalRule24AtOneQueriesIff env w z A)

theorem native_logicalRule24AtOneQueriesIff {m} (env : Fin 4 → Fin m) (w z A : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule24AtOneQueriesIffSentence env w z A)) := ZFReplay.replay (logicalRule24AtOneQueriesIff_kernel_certificate env w z A)

def logicalRule24AllQueriesIffSentence {m} (env : Fin 4 → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((empty z).imp (((LogicalAbstractSyntax.bundle24 w env).iff (LogicalAbstractSyntax.specification24 w z env)))))).close

theorem source_logicalRule24AllQueriesIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule24AllQueriesIffSentence env w z) := by
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
  exact LogicalAbstractAllQueries.bundle24_iff hZ w z env h0 h1 h2

theorem logicalRule24AllQueriesIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule24AllQueriesIffSentence env w z)) := TheoryTransport.sentence (source_logicalRule24AllQueriesIff env w z)

theorem native_logicalRule24AllQueriesIff {m} (env : Fin 4 → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule24AllQueriesIffSentence env w z)) := ZFReplay.replay (logicalRule24AllQueriesIff_kernel_certificate env w z)

def logicalRule24AllAssignmentBoundsSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornExprSyntax.graph LogicalAbstractNodeSyntax.head24 w env row).imp ((HornExprBounds.environmentBound 4 row env))))).close

theorem source_logicalRule24AllAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule24AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph LogicalAbstractNodeSyntax.head24 w env row) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph LogicalAbstractNodeSyntax.head24 w env row) := .hyp (Or.inl rfl)
  exact LogicalAbstractNode.head24_bounds hZ w row env h0 h1 h2

theorem logicalRule24AllAssignmentBounds_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule24AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_logicalRule24AllAssignmentBounds env w row)

theorem native_logicalRule24AllAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule24AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (logicalRule24AllAssignmentBounds_kernel_certificate env w row)

def logicalRule24NumericNestedHeadIffSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((HornExprSyntax.graph LogicalAbstractNodeSyntax.head24 w env row).iff (LogicalRule24Head.normalized w row env))))).close

theorem source_logicalRule24NumericNestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule24NumericNestedHeadIffSentence env w row) := by
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
  exact LogicalRule24Head.head_iff hZ w row env h0 h1

theorem logicalRule24NumericNestedHeadIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule24NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_logicalRule24NumericNestedHeadIff env w row)

theorem native_logicalRule24NumericNestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule24NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (logicalRule24NumericNestedHeadIff_kernel_certificate env w row)

def logicalRule24WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalAbstractNodeSyntax.node24 w row).iff (LogicalAbstractNodeSyntax.normalized24 w z row))))).close

theorem source_logicalRule24WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalRule24WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalAbstractNode.normalized_node24_iff hZ w z row h0 h1

theorem logicalRule24WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalRule24WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_logicalRule24WholeNormalizedNodeIff w z row)

theorem native_logicalRule24WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalRule24WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (logicalRule24WholeNormalizedNodeIff_kernel_certificate w z row)

def logicalAllTwentySevenWholeNodesIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalAllPatterns.node w row).iff (LogicalAllPatterns.specification w z row))))).close

theorem source_logicalAllTwentySevenWholeNodesIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalAllTwentySevenWholeNodesIffSentence w z row) := by
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
  exact LogicalAllPatterns.node_iff hZ w z row h0 h1

theorem logicalAllTwentySevenWholeNodesIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalAllTwentySevenWholeNodesIffSentence w z row)) := TheoryTransport.sentence (source_logicalAllTwentySevenWholeNodesIff w z row)

theorem native_logicalAllTwentySevenWholeNodesIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalAllTwentySevenWholeNodesIffSentence w z row)) := ZFReplay.replay (logicalAllTwentySevenWholeNodesIff_kernel_certificate w z row)

def logicalAllTwentySevenActualShapeTableIffSentence {m} (w row : Fin m) : Source.Sentence := (((LogicalOriginalNodeSyntax.table w row).iff (LogicalAllPatterns.node w row))).close

theorem source_logicalAllTwentySevenActualShapeTableIff {m} (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalAllTwentySevenActualShapeTableIffSentence w row) := by
  apply close_derives
  let Δ : Context m := Source.SetLanguage.ZF.at m
  exact LogicalOriginalNodes.raw_table_iff w row

theorem logicalAllTwentySevenActualShapeTableIff_kernel_certificate {m} (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalAllTwentySevenActualShapeTableIffSentence w row)) := TheoryTransport.sentence (source_logicalAllTwentySevenActualShapeTableIff w row)

theorem native_logicalAllTwentySevenActualShapeTableIff {m} (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalAllTwentySevenActualShapeTableIffSentence w row)) := ZFReplay.replay (logicalAllTwentySevenActualShapeTableIff_kernel_certificate w row)

def logicalAllTwentySevenActualTableSpecificationIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalOriginalNodeSyntax.table w row).iff (LogicalAllPatterns.specification w z row))))).close

theorem source_logicalAllTwentySevenActualTableSpecificationIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (logicalAllTwentySevenActualTableSpecificationIffSentence w z row) := by
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
  exact LogicalOriginalNodes.table_iff hZ w z row h0 h1

theorem logicalAllTwentySevenActualTableSpecificationIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (logicalAllTwentySevenActualTableSpecificationIffSentence w z row)) := TheoryTransport.sentence (source_logicalAllTwentySevenActualTableSpecificationIff w z row)

theorem native_logicalAllTwentySevenActualTableSpecificationIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (logicalAllTwentySevenActualTableSpecificationIffSentence w z row)) := ZFReplay.replay (logicalAllTwentySevenActualTableSpecificationIff_kernel_certificate w z row)

end PPAC.Migration.Internal.ObjectLogicalAbstract
