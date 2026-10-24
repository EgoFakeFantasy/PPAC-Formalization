import PPAC.Migration.Internal.LogicalStaticPatterns

/-! 原0–19／22／26完整纯关系节点的原核闭句，全部实际头证书已实例化。 -/
namespace PPAC.Migration.Internal.ObjectLogicalStatic
open Source SourceAlgebra SourceLogic OmegaSyntax

def staticLogicalAllQueriesIffSentence {m} (n : Nat) (isTerm : Bool) (env : Fin (n+1) → Fin m) (w z : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat (n+1) w env).imp ((empty z).imp (((LogicalStaticQueries.bundle n isTerm w env).iff (LogicalStaticQueries.types n isTerm w z env)))))).close

theorem source_staticLogicalAllQueriesIff {m} (n : Nat) (isTerm : Bool) (env : Fin (n+1) → Fin m) (w z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalAllQueriesIffSentence n isTerm env w z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (HornExprSyntax.environmentNat (n+1) w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat (n+1) w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact LogicalStaticQueries.bundle_iff hZ n isTerm w z env h0 h1 h2

theorem staticLogicalAllQueriesIff_kernel_certificate {m} (n : Nat) (isTerm : Bool) (env : Fin (n+1) → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalAllQueriesIffSentence n isTerm env w z)) := TheoryTransport.sentence (source_staticLogicalAllQueriesIff n isTerm env w z)

theorem native_staticLogicalAllQueriesIff {m} (n : Nat) (isTerm : Bool) (env : Fin (n+1) → Fin m) (w z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalAllQueriesIffSentence n isTerm env w z)) := ZFReplay.replay (staticLogicalAllQueriesIff_kernel_certificate n isTerm env w z)

def staticLogicalRule0WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 3 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule0.head) w row).iff (LogicalStaticNodeSyntax.normalized 3 false (@LogicalRule0Head.normalized) w z row))))).close

theorem source_staticLogicalRule0WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule0WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 3 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule0.head) (@LogicalRule0Head.normalized) LogicalStaticPatterns.rule0_head_variables (@LogicalRule0Head.head_iff) w z row h0 h1

theorem staticLogicalRule0WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule0WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule0WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule0WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule0WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule0WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule0AllAssignmentBoundsSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule0.head) w env row).imp ((HornExprBounds.environmentBound 4 row env))))).close

theorem source_staticLogicalRule0AllAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule0AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule0.head) w env row) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule0.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule0.head) LogicalStaticPatterns.rule0_head_variables w row env h0 h1 h2

theorem staticLogicalRule0AllAssignmentBounds_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule0AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule0AllAssignmentBounds env w row)

theorem native_staticLogicalRule0AllAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule0AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule0AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule0NumericNestedHeadIffSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule0.head) w env row).iff (LogicalRule0Head.normalized w row env))))).close

theorem source_staticLogicalRule0NumericNestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule0NumericNestedHeadIffSentence env w row) := by
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
  exact LogicalRule0Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule0NumericNestedHeadIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule0NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule0NumericNestedHeadIff env w row)

theorem native_staticLogicalRule0NumericNestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule0NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule0NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule1WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule1.head) w row).iff (LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule1Head.normalized) w z row))))).close

theorem source_staticLogicalRule1WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule1WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule1.head) (@LogicalRule1Head.normalized) LogicalStaticPatterns.rule1_head_variables (@LogicalRule1Head.head_iff) w z row h0 h1

theorem staticLogicalRule1WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule1WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule1WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule1WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule1WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule1WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule1AllAssignmentBoundsSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule1.head) w env row).imp ((HornExprBounds.environmentBound 2 row env))))).close

theorem source_staticLogicalRule1AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule1AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule1.head) w env row) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule1.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule1.head) LogicalStaticPatterns.rule1_head_variables w row env h0 h1 h2

theorem staticLogicalRule1AllAssignmentBounds_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule1AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule1AllAssignmentBounds env w row)

theorem native_staticLogicalRule1AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule1AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule1AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule1NumericNestedHeadIffSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule1.head) w env row).iff (LogicalRule1Head.normalized w row env))))).close

theorem source_staticLogicalRule1NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule1NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inl rfl)
  exact LogicalRule1Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule1NumericNestedHeadIff_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule1NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule1NumericNestedHeadIff env w row)

theorem native_staticLogicalRule1NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule1NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule1NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule2WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule2.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule2Head.normalized) w z row))))).close

theorem source_staticLogicalRule2WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule2WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule2.head) (@LogicalRule2Head.normalized) LogicalStaticPatterns.rule2_head_variables (@LogicalRule2Head.head_iff) w z row h0 h1

theorem staticLogicalRule2WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule2WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule2WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule2WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule2WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule2WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule2AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule2.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule2AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule2AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule2.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule2.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule2.head) LogicalStaticPatterns.rule2_head_variables w row env h0 h1 h2

theorem staticLogicalRule2AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule2AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule2AllAssignmentBounds env w row)

theorem native_staticLogicalRule2AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule2AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule2AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule2NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule2.head) w env row).iff (LogicalRule2Head.normalized w row env))))).close

theorem source_staticLogicalRule2NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule2NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule2Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule2NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule2NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule2NumericNestedHeadIff env w row)

theorem native_staticLogicalRule2NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule2NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule2NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule3WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule3.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule3Head.normalized) w z row))))).close

theorem source_staticLogicalRule3WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule3WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule3.head) (@LogicalRule3Head.normalized) LogicalStaticPatterns.rule3_head_variables (@LogicalRule3Head.head_iff) w z row h0 h1

theorem staticLogicalRule3WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule3WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule3WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule3WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule3WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule3WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule3AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule3.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule3AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule3AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule3.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule3.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule3.head) LogicalStaticPatterns.rule3_head_variables w row env h0 h1 h2

theorem staticLogicalRule3AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule3AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule3AllAssignmentBounds env w row)

theorem native_staticLogicalRule3AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule3AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule3AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule3NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule3.head) w env row).iff (LogicalRule3Head.normalized w row env))))).close

theorem source_staticLogicalRule3NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule3NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule3Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule3NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule3NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule3NumericNestedHeadIff env w row)

theorem native_staticLogicalRule3NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule3NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule3NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule4WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule4.head) w row).iff (LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule4Head.normalized) w z row))))).close

theorem source_staticLogicalRule4WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule4WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule4.head) (@LogicalRule4Head.normalized) LogicalStaticPatterns.rule4_head_variables (@LogicalRule4Head.head_iff) w z row h0 h1

theorem staticLogicalRule4WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule4WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule4WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule4WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule4WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule4WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule4AllAssignmentBoundsSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule4.head) w env row).imp ((HornExprBounds.environmentBound 2 row env))))).close

theorem source_staticLogicalRule4AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule4AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule4.head) w env row) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule4.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule4.head) LogicalStaticPatterns.rule4_head_variables w row env h0 h1 h2

theorem staticLogicalRule4AllAssignmentBounds_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule4AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule4AllAssignmentBounds env w row)

theorem native_staticLogicalRule4AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule4AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule4AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule4NumericNestedHeadIffSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule4.head) w env row).iff (LogicalRule4Head.normalized w row env))))).close

theorem source_staticLogicalRule4NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule4NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inl rfl)
  exact LogicalRule4Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule4NumericNestedHeadIff_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule4NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule4NumericNestedHeadIff env w row)

theorem native_staticLogicalRule4NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule4NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule4NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule5WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule5.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule5Head.normalized) w z row))))).close

theorem source_staticLogicalRule5WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule5WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule5.head) (@LogicalRule5Head.normalized) LogicalStaticPatterns.rule5_head_variables (@LogicalRule5Head.head_iff) w z row h0 h1

theorem staticLogicalRule5WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule5WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule5WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule5WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule5WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule5WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule5AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule5.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule5AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule5AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule5.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule5.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule5.head) LogicalStaticPatterns.rule5_head_variables w row env h0 h1 h2

theorem staticLogicalRule5AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule5AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule5AllAssignmentBounds env w row)

theorem native_staticLogicalRule5AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule5AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule5AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule5NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule5.head) w env row).iff (LogicalRule5Head.normalized w row env))))).close

theorem source_staticLogicalRule5NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule5NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule5Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule5NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule5NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule5NumericNestedHeadIff env w row)

theorem native_staticLogicalRule5NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule5NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule5NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule6WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule6.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule6Head.normalized) w z row))))).close

theorem source_staticLogicalRule6WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule6WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule6.head) (@LogicalRule6Head.normalized) LogicalStaticPatterns.rule6_head_variables (@LogicalRule6Head.head_iff) w z row h0 h1

theorem staticLogicalRule6WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule6WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule6WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule6WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule6WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule6WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule6AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule6.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule6AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule6AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule6.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule6.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule6.head) LogicalStaticPatterns.rule6_head_variables w row env h0 h1 h2

theorem staticLogicalRule6AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule6AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule6AllAssignmentBounds env w row)

theorem native_staticLogicalRule6AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule6AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule6AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule6NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule6.head) w env row).iff (LogicalRule6Head.normalized w row env))))).close

theorem source_staticLogicalRule6NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule6NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule6Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule6NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule6NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule6NumericNestedHeadIff env w row)

theorem native_staticLogicalRule6NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule6NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule6NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule7WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 0 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule7.head) w row).iff (LogicalStaticNodeSyntax.normalized 0 false (@LogicalRule7Head.normalized) w z row))))).close

theorem source_staticLogicalRule7WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule7WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 0 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule7.head) (@LogicalRule7Head.normalized) LogicalStaticPatterns.rule7_head_variables (@LogicalRule7Head.head_iff) w z row h0 h1

theorem staticLogicalRule7WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule7WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule7WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule7WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule7WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule7WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule7AllAssignmentBoundsSentence {m} (env : Fin 1 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule7.head) w env row).imp ((HornExprBounds.environmentBound 1 row env))))).close

theorem source_staticLogicalRule7AllAssignmentBounds {m} (env : Fin 1 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule7AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule7.head) w env row) (Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule7.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule7.head) LogicalStaticPatterns.rule7_head_variables w row env h0 h1 h2

theorem staticLogicalRule7AllAssignmentBounds_kernel_certificate {m} (env : Fin 1 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule7AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule7AllAssignmentBounds env w row)

theorem native_staticLogicalRule7AllAssignmentBounds {m} (env : Fin 1 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule7AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule7AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule7NumericNestedHeadIffSentence {m} (env : Fin 1 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 1 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule7.head) w env row).iff (LogicalRule7Head.normalized w row env))))).close

theorem source_staticLogicalRule7NumericNestedHeadIff {m} (env : Fin 1 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule7NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 1 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 1 w env) := .hyp (Or.inl rfl)
  exact LogicalRule7Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule7NumericNestedHeadIff_kernel_certificate {m} (env : Fin 1 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule7NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule7NumericNestedHeadIff env w row)

theorem native_staticLogicalRule7NumericNestedHeadIff {m} (env : Fin 1 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule7NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule7NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule8WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule8.head) w row).iff (LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule8Head.normalized) w z row))))).close

theorem source_staticLogicalRule8WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule8WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule8.head) (@LogicalRule8Head.normalized) LogicalStaticPatterns.rule8_head_variables (@LogicalRule8Head.head_iff) w z row h0 h1

theorem staticLogicalRule8WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule8WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule8WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule8WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule8WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule8WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule8AllAssignmentBoundsSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule8.head) w env row).imp ((HornExprBounds.environmentBound 2 row env))))).close

theorem source_staticLogicalRule8AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule8AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule8.head) w env row) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule8.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule8.head) LogicalStaticPatterns.rule8_head_variables w row env h0 h1 h2

theorem staticLogicalRule8AllAssignmentBounds_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule8AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule8AllAssignmentBounds env w row)

theorem native_staticLogicalRule8AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule8AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule8AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule8NumericNestedHeadIffSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule8.head) w env row).iff (LogicalRule8Head.normalized w row env))))).close

theorem source_staticLogicalRule8NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule8NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inl rfl)
  exact LogicalRule8Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule8NumericNestedHeadIff_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule8NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule8NumericNestedHeadIff env w row)

theorem native_staticLogicalRule8NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule8NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule8NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule9WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule9.head) w row).iff (LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule9Head.normalized) w z row))))).close

theorem source_staticLogicalRule9WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule9WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule9.head) (@LogicalRule9Head.normalized) LogicalStaticPatterns.rule9_head_variables (@LogicalRule9Head.head_iff) w z row h0 h1

theorem staticLogicalRule9WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule9WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule9WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule9WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule9WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule9WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule9AllAssignmentBoundsSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule9.head) w env row).imp ((HornExprBounds.environmentBound 2 row env))))).close

theorem source_staticLogicalRule9AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule9AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule9.head) w env row) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule9.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule9.head) LogicalStaticPatterns.rule9_head_variables w row env h0 h1 h2

theorem staticLogicalRule9AllAssignmentBounds_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule9AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule9AllAssignmentBounds env w row)

theorem native_staticLogicalRule9AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule9AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule9AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule9NumericNestedHeadIffSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule9.head) w env row).iff (LogicalRule9Head.normalized w row env))))).close

theorem source_staticLogicalRule9NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule9NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inl rfl)
  exact LogicalRule9Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule9NumericNestedHeadIff_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule9NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule9NumericNestedHeadIff env w row)

theorem native_staticLogicalRule9NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule9NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule9NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule10WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule10.head) w row).iff (LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule10Head.normalized) w z row))))).close

theorem source_staticLogicalRule10WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule10WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule10.head) (@LogicalRule10Head.normalized) LogicalStaticPatterns.rule10_head_variables (@LogicalRule10Head.head_iff) w z row h0 h1

theorem staticLogicalRule10WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule10WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule10WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule10WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule10WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule10WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule10AllAssignmentBoundsSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule10.head) w env row).imp ((HornExprBounds.environmentBound 2 row env))))).close

theorem source_staticLogicalRule10AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule10AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule10.head) w env row) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule10.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule10.head) LogicalStaticPatterns.rule10_head_variables w row env h0 h1 h2

theorem staticLogicalRule10AllAssignmentBounds_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule10AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule10AllAssignmentBounds env w row)

theorem native_staticLogicalRule10AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule10AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule10AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule10NumericNestedHeadIffSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule10.head) w env row).iff (LogicalRule10Head.normalized w row env))))).close

theorem source_staticLogicalRule10NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule10NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inl rfl)
  exact LogicalRule10Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule10NumericNestedHeadIff_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule10NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule10NumericNestedHeadIff env w row)

theorem native_staticLogicalRule10NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule10NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule10NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule11WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule11.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule11Head.normalized) w z row))))).close

theorem source_staticLogicalRule11WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule11WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule11.head) (@LogicalRule11Head.normalized) LogicalStaticPatterns.rule11_head_variables (@LogicalRule11Head.head_iff) w z row h0 h1

theorem staticLogicalRule11WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule11WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule11WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule11WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule11WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule11WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule11AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule11.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule11AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule11AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule11.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule11.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule11.head) LogicalStaticPatterns.rule11_head_variables w row env h0 h1 h2

theorem staticLogicalRule11AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule11AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule11AllAssignmentBounds env w row)

theorem native_staticLogicalRule11AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule11AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule11AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule11NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule11.head) w env row).iff (LogicalRule11Head.normalized w row env))))).close

theorem source_staticLogicalRule11NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule11NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule11Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule11NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule11NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule11NumericNestedHeadIff env w row)

theorem native_staticLogicalRule11NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule11NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule11NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule12WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule12.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule12Head.normalized) w z row))))).close

theorem source_staticLogicalRule12WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule12WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule12.head) (@LogicalRule12Head.normalized) LogicalStaticPatterns.rule12_head_variables (@LogicalRule12Head.head_iff) w z row h0 h1

theorem staticLogicalRule12WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule12WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule12WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule12WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule12WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule12WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule12AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule12.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule12AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule12AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule12.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule12.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule12.head) LogicalStaticPatterns.rule12_head_variables w row env h0 h1 h2

theorem staticLogicalRule12AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule12AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule12AllAssignmentBounds env w row)

theorem native_staticLogicalRule12AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule12AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule12AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule12NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule12.head) w env row).iff (LogicalRule12Head.normalized w row env))))).close

theorem source_staticLogicalRule12NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule12NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule12Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule12NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule12NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule12NumericNestedHeadIff env w row)

theorem native_staticLogicalRule12NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule12NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule12NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule13WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule13.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule13Head.normalized) w z row))))).close

theorem source_staticLogicalRule13WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule13WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule13.head) (@LogicalRule13Head.normalized) LogicalStaticPatterns.rule13_head_variables (@LogicalRule13Head.head_iff) w z row h0 h1

theorem staticLogicalRule13WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule13WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule13WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule13WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule13WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule13WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule13AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule13.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule13AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule13AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule13.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule13.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule13.head) LogicalStaticPatterns.rule13_head_variables w row env h0 h1 h2

theorem staticLogicalRule13AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule13AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule13AllAssignmentBounds env w row)

theorem native_staticLogicalRule13AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule13AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule13AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule13NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule13.head) w env row).iff (LogicalRule13Head.normalized w row env))))).close

theorem source_staticLogicalRule13NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule13NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule13Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule13NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule13NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule13NumericNestedHeadIff env w row)

theorem native_staticLogicalRule13NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule13NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule13NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule14WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule14.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule14Head.normalized) w z row))))).close

theorem source_staticLogicalRule14WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule14WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule14.head) (@LogicalRule14Head.normalized) LogicalStaticPatterns.rule14_head_variables (@LogicalRule14Head.head_iff) w z row h0 h1

theorem staticLogicalRule14WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule14WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule14WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule14WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule14WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule14WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule14AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule14.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule14AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule14AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule14.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule14.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule14.head) LogicalStaticPatterns.rule14_head_variables w row env h0 h1 h2

theorem staticLogicalRule14AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule14AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule14AllAssignmentBounds env w row)

theorem native_staticLogicalRule14AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule14AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule14AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule14NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule14.head) w env row).iff (LogicalRule14Head.normalized w row env))))).close

theorem source_staticLogicalRule14NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule14NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule14Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule14NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule14NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule14NumericNestedHeadIff env w row)

theorem native_staticLogicalRule14NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule14NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule14NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule15WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule15.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule15Head.normalized) w z row))))).close

theorem source_staticLogicalRule15WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule15WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule15.head) (@LogicalRule15Head.normalized) LogicalStaticPatterns.rule15_head_variables (@LogicalRule15Head.head_iff) w z row h0 h1

theorem staticLogicalRule15WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule15WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule15WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule15WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule15WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule15WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule15AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule15.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule15AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule15AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule15.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule15.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule15.head) LogicalStaticPatterns.rule15_head_variables w row env h0 h1 h2

theorem staticLogicalRule15AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule15AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule15AllAssignmentBounds env w row)

theorem native_staticLogicalRule15AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule15AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule15AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule15NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule15.head) w env row).iff (LogicalRule15Head.normalized w row env))))).close

theorem source_staticLogicalRule15NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule15NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule15Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule15NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule15NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule15NumericNestedHeadIff env w row)

theorem native_staticLogicalRule15NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule15NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule15NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule16WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 3 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule16.head) w row).iff (LogicalStaticNodeSyntax.normalized 3 false (@LogicalRule16Head.normalized) w z row))))).close

theorem source_staticLogicalRule16WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule16WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 3 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule16.head) (@LogicalRule16Head.normalized) LogicalStaticPatterns.rule16_head_variables (@LogicalRule16Head.head_iff) w z row h0 h1

theorem staticLogicalRule16WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule16WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule16WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule16WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule16WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule16WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule16AllAssignmentBoundsSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule16.head) w env row).imp ((HornExprBounds.environmentBound 4 row env))))).close

theorem source_staticLogicalRule16AllAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule16AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule16.head) w env row) (Context.add (HornExprSyntax.environmentNat 4 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 4 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule16.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule16.head) LogicalStaticPatterns.rule16_head_variables w row env h0 h1 h2

theorem staticLogicalRule16AllAssignmentBounds_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule16AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule16AllAssignmentBounds env w row)

theorem native_staticLogicalRule16AllAssignmentBounds {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule16AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule16AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule16NumericNestedHeadIffSentence {m} (env : Fin 4 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 4 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule16.head) w env row).iff (LogicalRule16Head.normalized w row env))))).close

theorem source_staticLogicalRule16NumericNestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule16NumericNestedHeadIffSentence env w row) := by
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
  exact LogicalRule16Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule16NumericNestedHeadIff_kernel_certificate {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule16NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule16NumericNestedHeadIff env w row)

theorem native_staticLogicalRule16NumericNestedHeadIff {m} (env : Fin 4 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule16NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule16NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule17WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule17.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule17Head.normalized) w z row))))).close

theorem source_staticLogicalRule17WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule17WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule17.head) (@LogicalRule17Head.normalized) LogicalStaticPatterns.rule17_head_variables (@LogicalRule17Head.head_iff) w z row h0 h1

theorem staticLogicalRule17WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule17WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule17WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule17WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule17WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule17WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule17AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule17.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule17AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule17AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule17.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule17.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule17.head) LogicalStaticPatterns.rule17_head_variables w row env h0 h1 h2

theorem staticLogicalRule17AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule17AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule17AllAssignmentBounds env w row)

theorem native_staticLogicalRule17AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule17AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule17AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule17NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule17.head) w env row).iff (LogicalRule17Head.normalized w row env))))).close

theorem source_staticLogicalRule17NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule17NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule17Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule17NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule17NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule17NumericNestedHeadIff env w row)

theorem native_staticLogicalRule17NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule17NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule17NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule18WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule18.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule18Head.normalized) w z row))))).close

theorem source_staticLogicalRule18WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule18WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule18.head) (@LogicalRule18Head.normalized) LogicalStaticPatterns.rule18_head_variables (@LogicalRule18Head.head_iff) w z row h0 h1

theorem staticLogicalRule18WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule18WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule18WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule18WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule18WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule18WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule18AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule18.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule18AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule18AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule18.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule18.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule18.head) LogicalStaticPatterns.rule18_head_variables w row env h0 h1 h2

theorem staticLogicalRule18AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule18AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule18AllAssignmentBounds env w row)

theorem native_staticLogicalRule18AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule18AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule18AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule18NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule18.head) w env row).iff (LogicalRule18Head.normalized w row env))))).close

theorem source_staticLogicalRule18NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule18NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule18Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule18NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule18NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule18NumericNestedHeadIff env w row)

theorem native_staticLogicalRule18NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule18NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule18NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule19WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule19.head) w row).iff (LogicalStaticNodeSyntax.normalized 2 false (@LogicalRule19Head.normalized) w z row))))).close

theorem source_staticLogicalRule19WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule19WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 2 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule19.head) (@LogicalRule19Head.normalized) LogicalStaticPatterns.rule19_head_variables (@LogicalRule19Head.head_iff) w z row h0 h1

theorem staticLogicalRule19WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule19WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule19WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule19WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule19WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule19WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule19AllAssignmentBoundsSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule19.head) w env row).imp ((HornExprBounds.environmentBound 3 row env))))).close

theorem source_staticLogicalRule19AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule19AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule19.head) w env row) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule19.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule19.head) LogicalStaticPatterns.rule19_head_variables w row env h0 h1 h2

theorem staticLogicalRule19AllAssignmentBounds_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule19AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule19AllAssignmentBounds env w row)

theorem native_staticLogicalRule19AllAssignmentBounds {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule19AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule19AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule19NumericNestedHeadIffSentence {m} (env : Fin 3 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule19.head) w env row).iff (LogicalRule19Head.normalized w row env))))).close

theorem source_staticLogicalRule19NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule19NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inl rfl)
  exact LogicalRule19Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule19NumericNestedHeadIff_kernel_certificate {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule19NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule19NumericNestedHeadIff env w row)

theorem native_staticLogicalRule19NumericNestedHeadIff {m} (env : Fin 3 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule19NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule19NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule22WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule22.head) w row).iff (LogicalStaticNodeSyntax.normalized 1 false (@LogicalRule22Head.normalized) w z row))))).close

theorem source_staticLogicalRule22WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule22WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 1 false (YesMetaZFC.Automation.ObjectLogicalAxiom.rule22.head) (@LogicalRule22Head.normalized) LogicalStaticPatterns.rule22_head_variables (@LogicalRule22Head.head_iff) w z row h0 h1

theorem staticLogicalRule22WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule22WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule22WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule22WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule22WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule22WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule22AllAssignmentBoundsSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule22.head) w env row).imp ((HornExprBounds.environmentBound 2 row env))))).close

theorem source_staticLogicalRule22AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule22AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule22.head) w env row) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule22.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule22.head) LogicalStaticPatterns.rule22_head_variables w row env h0 h1 h2

theorem staticLogicalRule22AllAssignmentBounds_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule22AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule22AllAssignmentBounds env w row)

theorem native_staticLogicalRule22AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule22AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule22AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule22NumericNestedHeadIffSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule22.head) w env row).iff (LogicalRule22Head.normalized w row env))))).close

theorem source_staticLogicalRule22NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule22NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inl rfl)
  exact LogicalRule22Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule22NumericNestedHeadIff_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule22NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule22NumericNestedHeadIff env w row)

theorem native_staticLogicalRule22NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule22NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule22NumericNestedHeadIff_kernel_certificate env w row)

def staticLogicalRule26WholeNormalizedNodeIffSentence {m} (w z row : Fin m) : Source.Sentence := ((omega w).imp ((empty z).imp (((LogicalStaticNodeSyntax.node 1 true (YesMetaZFC.Automation.ObjectLogicalAxiom.rule26.head) w row).iff (LogicalStaticNodeSyntax.normalized 1 true (@LogicalRule26Head.normalized) w z row))))).close

theorem source_staticLogicalRule26WholeNormalizedNodeIff {m} (w z row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule26WholeNormalizedNodeIffSentence w z row) := by
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
  exact LogicalStaticNode.normalized_node_iff hZ 1 true (YesMetaZFC.Automation.ObjectLogicalAxiom.rule26.head) (@LogicalRule26Head.normalized) LogicalStaticPatterns.rule26_head_variables (@LogicalRule26Head.head_iff) w z row h0 h1

theorem staticLogicalRule26WholeNormalizedNodeIff_kernel_certificate {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule26WholeNormalizedNodeIffSentence w z row)) := TheoryTransport.sentence (source_staticLogicalRule26WholeNormalizedNodeIff w z row)

theorem native_staticLogicalRule26WholeNormalizedNodeIff {m} (w z row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule26WholeNormalizedNodeIffSentence w z row)) := ZFReplay.replay (staticLogicalRule26WholeNormalizedNodeIff_kernel_certificate w z row)

def staticLogicalRule26AllAssignmentBoundsSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule26.head) w env row).imp ((HornExprBounds.environmentBound 2 row env))))).close

theorem source_staticLogicalRule26AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule26AllAssignmentBoundsSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule26.head) w env row) (Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule26.head) w env row) := .hyp (Or.inl rfl)
  exact LogicalStaticNode.head_bounds hZ (YesMetaZFC.Automation.ObjectLogicalAxiom.rule26.head) LogicalStaticPatterns.rule26_head_variables w row env h0 h1 h2

theorem staticLogicalRule26AllAssignmentBounds_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule26AllAssignmentBoundsSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule26AllAssignmentBounds env w row)

theorem native_staticLogicalRule26AllAssignmentBounds {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule26AllAssignmentBoundsSentence env w row)) := ZFReplay.replay (staticLogicalRule26AllAssignmentBounds_kernel_certificate env w row)

def staticLogicalRule26NumericNestedHeadIffSentence {m} (env : Fin 2 → Fin m) (w row : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 2 w env).imp (((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectLogicalAxiom.rule26.head) w env row).iff (LogicalRule26Head.normalized w row env))))).close

theorem source_staticLogicalRule26NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (staticLogicalRule26NumericNestedHeadIffSentence env w row) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat 2 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 2 w env) := .hyp (Or.inl rfl)
  exact LogicalRule26Head.head_iff hZ w row env h0 h1

theorem staticLogicalRule26NumericNestedHeadIff_kernel_certificate {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (staticLogicalRule26NumericNestedHeadIffSentence env w row)) := TheoryTransport.sentence (source_staticLogicalRule26NumericNestedHeadIff env w row)

theorem native_staticLogicalRule26NumericNestedHeadIff {m} (env : Fin 2 → Fin m) (w row : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (staticLogicalRule26NumericNestedHeadIffSentence env w row)) := ZFReplay.replay (staticLogicalRule26NumericNestedHeadIff_kernel_certificate env w row)

end PPAC.Migration.Internal.ObjectLogicalStatic
