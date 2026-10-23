import PPAC.Migration.Internal.OriginalFormulaTraceRules

/-! 原十一公式完整表分派、局部数值矩阵及真实子轨迹合成之原核证书。 -/
namespace PPAC.Migration.Internal.ObjectOriginalFormulaMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax
open YesMetaZFC.Automation.ObjectHorn (Rule)

def originalKindThreeWholeTableDispatchSentence {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 3 w xs r).imp (((HornStepSyntax.originalStep w r R).iff (HornStepSyntax.step OriginalFormulaClasses.selected w r R))))).close

theorem source_originalKindThreeWholeTableDispatch {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalKindThreeWholeTableDispatchSentence xs w r R) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNodeSyntax.constructor 5 3 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 3 w xs r) := .hyp (Or.inl rfl)
  exact OriginalFormulaDispatch.dispatch_iff hZ w r R xs h0 h1

theorem originalKindThreeWholeTableDispatch_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalKindThreeWholeTableDispatchSentence xs w r R)) := TheoryTransport.sentence (source_originalKindThreeWholeTableDispatch xs w r R)

theorem native_originalKindThreeWholeTableDispatch {m} (xs : Fin 5 → Fin m) (w r R : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalKindThreeWholeTableDispatchSentence xs w r R)) := ZFReplay.replay (originalKindThreeWholeTableDispatch_kernel_certificate xs w r R)

def originalKindThreeTraceSelectedIffSentence {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : Source.Sentence := ((omega w).imp ((SyntaxNodeSyntax.constructor 5 3 w xs r).imp ((HornUniversalTraceSyntax.value w V).imp (((HornLookupConditionSyntax.condition w r).iff (HornStepSyntax.step OriginalFormulaClasses.selected w r V)))))).close

theorem source_originalKindThreeTraceSelectedIff {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalKindThreeTraceSelectedIffSentence xs w r V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceSyntax.value w V) (Context.add (SyntaxNodeSyntax.constructor 5 3 w xs r) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (SyntaxNodeSyntax.constructor 5 3 w xs r) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornUniversalTraceSyntax.value w V) := .hyp (Or.inl rfl)
  exact OriginalFormulaDispatch.trace_iff_selected hZ w r V xs h0 h1 h2

theorem originalKindThreeTraceSelectedIff_kernel_certificate {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalKindThreeTraceSelectedIffSentence xs w r V)) := TheoryTransport.sentence (source_originalKindThreeTraceSelectedIff xs w r V)

theorem native_originalKindThreeTraceSelectedIff {m} (xs : Fin 5 → Fin m) (w r V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalKindThreeTraceSelectedIffSentence xs w r V)) := ZFReplay.replay (originalKindThreeTraceSelectedIff_kernel_certificate xs w r V)

def originalFormulaHeadMetadataSentence {m} (a kind : Nat) (j0 j1 j2 : Fin a) (e f : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w mode depth parameter n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat a w env).imp ((HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal kind) (List.ofFn (OriginalFormulaRowGraph.fields j0 j1 j2 e f))) w env r).imp ((OriginalTransformRowSyntax.row kind w mode depth parameter n q r).imp (((Formula.equal mode (env j0)).conj ((Formula.equal depth (env j1)).conj (.equal parameter (env j2))))))))).close

theorem source_originalFormulaHeadMetadata {m} (a kind : Nat) (j0 j1 j2 : Fin a) (e f : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w mode depth parameter n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaHeadMetadataSentence a kind j0 j1 j2 e f env w mode depth parameter n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row kind w mode depth parameter n q r) (Context.add (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal kind) (List.ofFn (OriginalFormulaRowGraph.fields j0 j1 j2 e f))) w env r) (Context.add (HornExprSyntax.environmentNat a w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat a w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (HornExprSyntax.graph (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal kind) (List.ofFn (OriginalFormulaRowGraph.fields j0 j1 j2 e f))) w env r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalTransformRowSyntax.row kind w mode depth parameter n q r) := .hyp (Or.inl rfl)
  exact OriginalFormulaRowGraph.metadata_eq hZ kind j0 j1 j2 e f w mode depth parameter n q r env h0 h1 h2 h3

theorem originalFormulaHeadMetadata_kernel_certificate {m} (a kind : Nat) (j0 j1 j2 : Fin a) (e f : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w mode depth parameter n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaHeadMetadataSentence a kind j0 j1 j2 e f env w mode depth parameter n q r)) := TheoryTransport.sentence (source_originalFormulaHeadMetadata a kind j0 j1 j2 e f env w mode depth parameter n q r)

theorem native_originalFormulaHeadMetadata {m} (a kind : Nat) (j0 j1 j2 : Fin a) (e f : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w mode depth parameter n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaHeadMetadataSentence a kind j0 j1 j2 e f env w mode depth parameter n q r)) := ZFReplay.replay (originalFormulaHeadMetadata_kernel_certificate a kind j0 j1 j2 e f env w mode depth parameter n q r)

def originalFormulaApplicationNumericIffSentence {m} (a : Nat) (i j : Fin a) (env : Fin a → Fin m) (w n : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat a w env).imp (((HornExprSyntax.graph (OriginalFormulaApplicationSyntax.expr i j) w env n).iff (OriginalFormulaApplicationSyntax.application w (env i) (env j) n))))).close

theorem source_originalFormulaApplicationNumericIff {m} (a : Nat) (i j : Fin a) (env : Fin a → Fin m) (w n : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaApplicationNumericIffSentence a i j env w n) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat a w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (HornExprSyntax.environmentNat a w env) := .hyp (Or.inl rfl)
  exact OriginalFormulaApplicationExpr.application_iff hZ i j w n env h0 h1

theorem originalFormulaApplicationNumericIff_kernel_certificate {m} (a : Nat) (i j : Fin a) (env : Fin a → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaApplicationNumericIffSentence a i j env w n)) := TheoryTransport.sentence (source_originalFormulaApplicationNumericIff a i j env w n)

theorem native_originalFormulaApplicationNumericIff {m} (a : Nat) (i j : Fin a) (env : Fin a → Fin m) (w n : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaApplicationNumericIffSentence a i j env w n)) := ZFReplay.replay (originalFormulaApplicationNumericIff_kernel_certificate a i j env w n)

def originalFormulaConstantNumericMatrixSentence {m} (three : Bool) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) w r env).iff (OriginalFormulaLocalData.constant tag w n q))))))).close

theorem source_originalFormulaConstantNumericMatrix {m} (three : Bool) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaConstantNumericMatrixSentence three tag env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) (Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) := .hyp (Or.inl rfl)
  exact OriginalFormulaMatrix.constant_at_row hZ three tag w n q r env h0 h1 h3 h2

theorem originalFormulaConstantNumericMatrix_kernel_certificate {m} (three : Bool) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaConstantNumericMatrixSentence three tag env w n q r)) := TheoryTransport.sentence (source_originalFormulaConstantNumericMatrix three tag env w n q r)

theorem native_originalFormulaConstantNumericMatrix {m} (three : Bool) (tag : Nat) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaConstantNumericMatrixSentence three tag env w n q r)) := ZFReplay.replay (originalFormulaConstantNumericMatrix_kernel_certificate three tag env w n q r)

def originalFormulaBinaryNumericMatrixSentence {m} (tag kind : Nat) (env : Fin 7 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) w r env).iff (OriginalFormulaLocalData.binary tag kind w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5) (env 6))))))).close

theorem source_originalFormulaBinaryNumericMatrix {m} (tag kind : Nat) (env : Fin 7 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaBinaryNumericMatrixSentence tag kind env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inl rfl)
  exact OriginalFormulaMatrix.binary_at_row hZ tag kind w n q r env h0 h1 h2

theorem originalFormulaBinaryNumericMatrix_kernel_certificate {m} (tag kind : Nat) (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaBinaryNumericMatrixSentence tag kind env w n q r)) := TheoryTransport.sentence (source_originalFormulaBinaryNumericMatrix tag kind env w n q r)

theorem native_originalFormulaBinaryNumericMatrix {m} (tag kind : Nat) (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaBinaryNumericMatrixSentence tag kind env w n q r)) := ZFReplay.replay (originalFormulaBinaryNumericMatrix_kernel_certificate tag kind env w n q r)

def originalFormulaNonbinderNumericMatrixSentence {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) w r env).iff (OriginalFormulaLocalData.unary tag w (env 0) (env 1) (env 2) n q (env 3) (env 4))))))).close

theorem source_originalFormulaNonbinderNumericMatrix {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaNonbinderNumericMatrixSentence tag env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inl rfl)
  exact OriginalFormulaMatrix.nonbinder_at_row hZ tag w n q r env h0 h1 h2

theorem originalFormulaNonbinderNumericMatrix_kernel_certificate {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaNonbinderNumericMatrixSentence tag env w n q r)) := TheoryTransport.sentence (source_originalFormulaNonbinderNumericMatrix tag env w n q r)

theorem native_originalFormulaNonbinderNumericMatrix {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaNonbinderNumericMatrixSentence tag env w n q r)) := ZFReplay.replay (originalFormulaNonbinderNumericMatrix_kernel_certificate tag env w n q r)

def originalFormulaBinderNumericMatrixSentence {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp ((successor childDepth (env 1)).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) w r env).iff (OriginalFormulaLocalData.unary tag w (env 0) childDepth (env 2) n q (env 3) (env 4)))))))).close

theorem source_originalFormulaBinderNumericMatrix {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaBinderNumericMatrixSentence tag env w n q r childDepth) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor childDepth (env 1)) (Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (successor childDepth (env 1)) := .hyp (Or.inl rfl)
  exact OriginalFormulaMatrix.binder_at_row hZ tag w n q r childDepth env h0 h1 h2 h3

theorem originalFormulaBinderNumericMatrix_kernel_certificate {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaBinderNumericMatrixSentence tag env w n q r childDepth)) := TheoryTransport.sentence (source_originalFormulaBinderNumericMatrix tag env w n q r childDepth)

theorem native_originalFormulaBinderNumericMatrix {m} (tag : Nat) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaBinderNumericMatrixSentence tag env w n q r childDepth)) := ZFReplay.replay (originalFormulaBinderNumericMatrix_kernel_certificate tag env w n q r childDepth)

def originalFormulaApplicationNumericMatrixSentence {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp (((HornUniversalTraceRules.tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r env).iff (OriginalFormulaLocalData.application w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5))))))).close

theorem source_originalFormulaApplicationNumericMatrix {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaApplicationNumericMatrixSentence env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inl rfl)
  exact OriginalFormulaMatrix.application_at_row hZ w n q r env h0 h1 h2

theorem originalFormulaApplicationNumericMatrix_kernel_certificate {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaApplicationNumericMatrixSentence env w n q r)) := TheoryTransport.sentence (source_originalFormulaApplicationNumericMatrix env w n q r)

theorem native_originalFormulaApplicationNumericMatrix {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaApplicationNumericMatrixSentence env w n q r)) := ZFReplay.replay (originalFormulaApplicationNumericMatrix_kernel_certificate env w n q r)

def originalFormulaBinderActualChildRunSentence {m} (env : Fin 5 → Fin m) (w childDepth : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((successor childDepth (env 1)).imp (((HornUniversalTraceRules.tracedPremise (OriginalFormulaExpr.unaryChild true) w env).iff (OriginalTransformRowSyntax.run 3 w (env 0) childDepth (env 2) (env 3) (env 4))))))).close

theorem source_originalFormulaBinderActualChildRun {m} (env : Fin 5 → Fin m) (w childDepth : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaBinderActualChildRunSentence env w childDepth) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (successor childDepth (env 1)) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (successor childDepth (env 1)) := .hyp (Or.inl rfl)
  exact OriginalFormulaChildren.binder_child_iff hZ w childDepth env h0 h1 h2

theorem originalFormulaBinderActualChildRun_kernel_certificate {m} (env : Fin 5 → Fin m) (w childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaBinderActualChildRunSentence env w childDepth)) := TheoryTransport.sentence (source_originalFormulaBinderActualChildRun env w childDepth)

theorem native_originalFormulaBinderActualChildRun {m} (env : Fin 5 → Fin m) (w childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaBinderActualChildRunSentence env w childDepth)) := ZFReplay.replay (originalFormulaBinderActualChildRun_kernel_certificate env w childDepth)

def originalElevenRuleTraceCompositionSentence {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (_hr : rule ∈ OriginalFormulaClasses.selected) (env : Fin rule.arity → Fin m) (w r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat rule.arity w env).imp ((HornUniversalTraceRules.tracedMatrix rule w r env).imp ((HornLookupConditionSyntax.condition w r))))).close

theorem source_originalElevenRuleTraceComposition {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (_hr : rule ∈ OriginalFormulaClasses.selected) (env : Fin rule.arity → Fin m) (w r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalElevenRuleTraceCompositionSentence rule _hr env w r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornUniversalTraceRules.tracedMatrix rule w r env) (Context.add (HornExprSyntax.environmentNat rule.arity w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat rule.arity w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornUniversalTraceRules.tracedMatrix rule w r env) := .hyp (Or.inl rfl)
  exact OriginalFormulaTraceRules.selected_condition hZ rule _hr w r env h0 h1 h2

theorem originalElevenRuleTraceComposition_kernel_certificate {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (_hr : rule ∈ OriginalFormulaClasses.selected) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalElevenRuleTraceCompositionSentence rule _hr env w r)) := TheoryTransport.sentence (source_originalElevenRuleTraceComposition rule _hr env w r)

theorem native_originalElevenRuleTraceComposition {m} (rule : YesMetaZFC.Automation.ObjectHorn.Rule) (_hr : rule ∈ OriginalFormulaClasses.selected) (env : Fin rule.arity → Fin m) (w r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalElevenRuleTraceCompositionSentence rule _hr env w r)) := ZFReplay.replay (originalElevenRuleTraceComposition_kernel_certificate rule _hr env w r)

def originalFormulaConstantTraceFromDataSentence {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (env : Fin 3 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 3 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp ((SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)).imp ((OriginalFormulaLocalData.constant tag w n q).imp ((HornLookupConditionSyntax.condition w r))))))).close

theorem source_originalFormulaConstantTraceFromData {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (env : Fin 3 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaConstantTraceFromDataSentence three tag _hr env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaLocalData.constant tag w n q) (Context.add (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) (Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 3 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 3 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (OriginalFormulaLocalData.constant tag w n q) := .hyp (Or.inl rfl)
  exact OriginalFormulaTraceRules.constant_condition hZ three tag _hr w n q r env h0 h1 h2 h3 h4

theorem originalFormulaConstantTraceFromData_kernel_certificate {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaConstantTraceFromDataSentence three tag _hr env w n q r)) := TheoryTransport.sentence (source_originalFormulaConstantTraceFromData three tag _hr env w n q r)

theorem native_originalFormulaConstantTraceFromData {m} (three : Bool) (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.constant tag) ∈ OriginalFormulaClasses.selected) (env : Fin 3 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaConstantTraceFromDataSentence three tag _hr env w n q r)) := ZFReplay.replay (originalFormulaConstantTraceFromData_kernel_certificate three tag _hr env w n q r)

def originalFormulaBinaryTraceFromDataSentence {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (env : Fin 7 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 7 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp ((OriginalFormulaLocalData.binary tag kind w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5) (env 6)).imp ((HornLookupConditionSyntax.condition w r)))))).close

theorem source_originalFormulaBinaryTraceFromData {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (env : Fin 7 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaBinaryTraceFromDataSentence tag kind _hr env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaLocalData.binary tag kind w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5) (env 6)) (Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 7 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 7 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalFormulaLocalData.binary tag kind w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5) (env 6)) := .hyp (Or.inl rfl)
  exact OriginalFormulaTraceRules.binary_condition hZ tag kind _hr w n q r env h0 h1 h2 h3

theorem originalFormulaBinaryTraceFromData_kernel_certificate {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaBinaryTraceFromDataSentence tag kind _hr env w n q r)) := TheoryTransport.sentence (source_originalFormulaBinaryTraceFromData tag kind _hr env w n q r)

theorem native_originalFormulaBinaryTraceFromData {m} (tag kind : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.binary tag kind) ∈ OriginalFormulaClasses.selected) (env : Fin 7 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaBinaryTraceFromDataSentence tag kind _hr env w n q r)) := ZFReplay.replay (originalFormulaBinaryTraceFromData_kernel_certificate tag kind _hr env w n q r)

def originalFormulaNonbinderTraceFromDataSentence {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp ((OriginalFormulaLocalData.unary tag w (env 0) (env 1) (env 2) n q (env 3) (env 4)).imp ((HornLookupConditionSyntax.condition w r)))))).close

theorem source_originalFormulaNonbinderTraceFromData {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaNonbinderTraceFromDataSentence tag _hr env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaLocalData.unary tag w (env 0) (env 1) (env 2) n q (env 3) (env 4)) (Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalFormulaLocalData.unary tag w (env 0) (env 1) (env 2) n q (env 3) (env 4)) := .hyp (Or.inl rfl)
  exact OriginalFormulaTraceRules.nonbinder_condition hZ tag _hr w n q r env h0 h1 h2 h3

theorem originalFormulaNonbinderTraceFromData_kernel_certificate {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaNonbinderTraceFromDataSentence tag _hr env w n q r)) := TheoryTransport.sentence (source_originalFormulaNonbinderTraceFromData tag _hr env w n q r)

theorem native_originalFormulaNonbinderTraceFromData {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag false) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaNonbinderTraceFromDataSentence tag _hr env w n q r)) := ZFReplay.replay (originalFormulaNonbinderTraceFromData_kernel_certificate tag _hr env w n q r)

def originalFormulaBinderTraceFromDataSentence {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp ((successor childDepth (env 1)).imp ((OriginalFormulaLocalData.unary tag w (env 0) childDepth (env 2) n q (env 3) (env 4)).imp ((HornLookupConditionSyntax.condition w r))))))).close

theorem source_originalFormulaBinderTraceFromData {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaBinderTraceFromDataSentence tag _hr env w n q r childDepth) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaLocalData.unary tag w (env 0) childDepth (env 2) n q (env 3) (env 4)) (Context.add (successor childDepth (env 1)) (Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (successor childDepth (env 1)) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (OriginalFormulaLocalData.unary tag w (env 0) childDepth (env 2) n q (env 3) (env 4)) := .hyp (Or.inl rfl)
  exact OriginalFormulaTraceRules.binder_condition hZ tag _hr w n q r childDepth env h0 h1 h2 h3 h4

theorem originalFormulaBinderTraceFromData_kernel_certificate {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaBinderTraceFromDataSentence tag _hr env w n q r childDepth)) := TheoryTransport.sentence (source_originalFormulaBinderTraceFromData tag _hr env w n q r childDepth)

theorem native_originalFormulaBinderTraceFromData {m} (tag : Nat) (_hr : (YesMetaZFC.Automation.ObjectSyntaxTransform.unary tag true) ∈ OriginalFormulaClasses.selected) (env : Fin 5 → Fin m) (w n q r childDepth : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaBinderTraceFromDataSentence tag _hr env w n q r childDepth)) := ZFReplay.replay (originalFormulaBinderTraceFromData_kernel_certificate tag _hr env w n q r childDepth)

def originalFormulaApplicationTraceFromDataSentence {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 6 w env).imp ((OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r).imp ((OriginalFormulaLocalData.application w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5)).imp ((HornLookupConditionSyntax.condition w r)))))).close

theorem source_originalFormulaApplicationTraceFromData {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalFormulaApplicationTraceFromDataSentence env w n q r) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (OriginalFormulaLocalData.application w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5)) (Context.add (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) (Context.add (HornExprSyntax.environmentNat 6 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 6 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (OriginalFormulaLocalData.application w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5)) := .hyp (Or.inl rfl)
  exact OriginalFormulaTraceRules.application_condition hZ w n q r env h0 h1 h2 h3

theorem originalFormulaApplicationTraceFromData_kernel_certificate {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalFormulaApplicationTraceFromDataSentence env w n q r)) := TheoryTransport.sentence (source_originalFormulaApplicationTraceFromData env w n q r)

theorem native_originalFormulaApplicationTraceFromData {m} (env : Fin 6 → Fin m) (w n q r : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalFormulaApplicationTraceFromDataSentence env w n q r)) := ZFReplay.replay (originalFormulaApplicationTraceFromData_kernel_certificate env w n q r)

end PPAC.Migration.Internal.ObjectOriginalFormulaMatrix
