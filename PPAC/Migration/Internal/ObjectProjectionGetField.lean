import PPAC.Migration.Internal.ProjectionField
import PPAC.Migration.Internal.ProjectionTag

/-! 原get对象ω归纳、field及七规则独立纯轨迹完整数值双条件的原核闭句。 -/
namespace PPAC.Migration.Internal.ObjectProjectionGetField
open Source SourceAlgebra SourceLogic OmegaSyntax

def projectionActualPremiseQueryIffSentence {m} (a : Nat) (e : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w V : Fin m) : Source.Sentence := ((ProjectionTraceSetSyntax.value w V).imp (((HornRuleSyntax.premise e w V env).iff (ProjectionExprQuery.query e w env)))).close

theorem source_projectionActualPremiseQueryIff {m} (a : Nat) (e : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionActualPremiseQueryIffSentence a e env w V) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSetSyntax.value w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProjectionTraceSetSyntax.value w V) := .hyp (Or.inl rfl)
  exact ProjectionTracePremises.premise_iff e w V env h0

theorem projectionActualPremiseQueryIff_kernel_certificate {m} (a : Nat) (e : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionActualPremiseQueryIffSentence a e env w V)) := TheoryTransport.sentence (source_projectionActualPremiseQueryIff a e env w V)

theorem native_projectionActualPremiseQueryIff {m} (a : Nat) (e : YesMetaZFC.Automation.ObjectHorn.Expr a) (env : Fin a → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionActualPremiseQueryIffSentence a e env w V)) := ZFReplay.replay (projectionActualPremiseQueryIff_kernel_certificate a e env w V)

def projectionActualPremisesQueriesIffSentence {m} (a : Nat) (es : List (YesMetaZFC.Automation.ObjectHorn.Expr a)) (env : Fin a → Fin m) (w V : Fin m) : Source.Sentence := ((ProjectionTraceSetSyntax.value w V).imp (((HornRuleSyntax.premises es w V env).iff (ProjectionExprQuery.premises es w env)))).close

theorem source_projectionActualPremisesQueriesIff {m} (a : Nat) (es : List (YesMetaZFC.Automation.ObjectHorn.Expr a)) (env : Fin a → Fin m) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionActualPremisesQueriesIffSentence a es env w V) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSetSyntax.value w V) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (ProjectionTraceSetSyntax.value w V) := .hyp (Or.inl rfl)
  exact ProjectionTracePremises.premises_iff es w V env h0

theorem projectionActualPremisesQueriesIff_kernel_certificate {m} (a : Nat) (es : List (YesMetaZFC.Automation.ObjectHorn.Expr a)) (env : Fin a → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionActualPremisesQueriesIffSentence a es env w V)) := TheoryTransport.sentence (source_projectionActualPremisesQueriesIff a es env w V)

theorem native_projectionActualPremisesQueriesIff {m} (a : Nat) (es : List (YesMetaZFC.Automation.ObjectHorn.Expr a)) (env : Fin a → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionActualPremisesQueriesIffSentence a es env w V)) := ZFReplay.replay (projectionActualPremisesQueriesIff_kernel_certificate a es env w V)

def projectionGetVariablesQueryIffSentence {m} (a : Nat) (jx ji jy : Fin a) (env : Fin a → Fin m) (w : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat a w env).imp (((ProjectionExprQuery.query (YesMetaZFC.Automation.ObjectHorn.Expr.node (.literal 1) (List.ofFn (ProjectionTracePremises.getFields jx ji jy))) w env).iff (ProjectionTraceSyntax.get w (env jx) (env ji) (env jy)))))).close

theorem source_projectionGetVariablesQueryIff {m} (a : Nat) (jx ji jy : Fin a) (env : Fin a → Fin m) (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetVariablesQueryIffSentence a jx ji jy env w) := by
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
  exact ProjectionTracePremises.get_variables_iff hZ jx ji jy w env h0 h1

theorem projectionGetVariablesQueryIff_kernel_certificate {m} (a : Nat) (jx ji jy : Fin a) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetVariablesQueryIffSentence a jx ji jy env w)) := TheoryTransport.sentence (source_projectionGetVariablesQueryIff a jx ji jy env w)

theorem native_projectionGetVariablesQueryIff {m} (a : Nat) (jx ji jy : Fin a) (env : Fin a → Fin m) (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetVariablesQueryIffSentence a jx ji jy env w)) := ZFReplay.replay (projectionGetVariablesQueryIff_kernel_certificate a jx ji jy env w)

def projectionArbitraryRawPairHeadTailSentence {m} (head : Bool) (a : Nat) (tag first rest : Fin a) (env : Fin a → Fin m) (w x : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat a w env).imp ((HornExprSyntax.graph (ProjectionRawPairExpr.rawPair tag first rest) w env x).imp ((RawCodeProjectionSyntax.step head w x (if head then env first else env rest)))))).close

theorem source_projectionArbitraryRawPairHeadTail {m} (head : Bool) (a : Nat) (tag first rest : Fin a) (env : Fin a → Fin m) (w x : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionArbitraryRawPairHeadTailSentence head a tag first rest env w x) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.graph (ProjectionRawPairExpr.rawPair tag first rest) w env x) (Context.add (HornExprSyntax.environmentNat a w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (HornExprSyntax.environmentNat a w env) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (HornExprSyntax.graph (ProjectionRawPairExpr.rawPair tag first rest) w env x) := .hyp (Or.inl rfl)
  exact ProjectionRawPairExpr.head_tail hZ head tag first rest w x env h0 h1 h2

theorem projectionArbitraryRawPairHeadTail_kernel_certificate {m} (head : Bool) (a : Nat) (tag first rest : Fin a) (env : Fin a → Fin m) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionArbitraryRawPairHeadTailSentence head a tag first rest env w x)) := TheoryTransport.sentence (source_projectionArbitraryRawPairHeadTail head a tag first rest env w x)

theorem native_projectionArbitraryRawPairHeadTail {m} (head : Bool) (a : Nat) (tag first rest : Fin a) (env : Fin a → Fin m) (w x : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionArbitraryRawPairHeadTailSentence head a tag first rest env w x)) := ZFReplay.replay (projectionArbitraryRawPairHeadTail_kernel_certificate head a tag first rest env w x)

def projectionSuccessorVariableIffSentence {m} (a : Nat) (j : Fin a) (env : Fin a → Fin m) (w s : Fin m) : Source.Sentence := ((HornExprSyntax.environmentNat a w env).imp (((HornExprSyntax.graph (.succ (.var j)) w env s).iff (successor s (env j))))).close

theorem source_projectionSuccessorVariableIff {m} (a : Nat) (j : Fin a) (env : Fin a → Fin m) (w s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionSuccessorVariableIffSentence a j env w s) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (HornExprSyntax.environmentNat a w env) (Source.SetLanguage.ZF.at m)
  have h0 : Derives Δ (HornExprSyntax.environmentNat a w env) := .hyp (Or.inl rfl)
  exact ProjectionRawPairExpr.successor_variable_iff j w s env h0

theorem projectionSuccessorVariableIff_kernel_certificate {m} (a : Nat) (j : Fin a) (env : Fin a → Fin m) (w s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionSuccessorVariableIffSentence a j env w s)) := TheoryTransport.sentence (source_projectionSuccessorVariableIff a j env w s)

theorem native_projectionSuccessorVariableIff {m} (a : Nat) (j : Fin a) (env : Fin a → Fin m) (w s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionSuccessorVariableIffSentence a j env w s)) := ZFReplay.replay (projectionSuccessorVariableIff_kernel_certificate a j env w s)

def projectionGetZeroConstructedSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((empty x).imp ((empty y).imp ((ProjectionTraceSyntax.get w x i y)))))).close

theorem source_projectionGetZeroConstructed {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetZeroConstructedSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty y) (Context.add (empty x) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty x) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (empty y) := .hyp (Or.inl rfl)
  exact ProjectionGetConstructors.zero_checked hZ w x i y h0 h1 h2 h3

theorem projectionGetZeroConstructed_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetZeroConstructedSentence w x i y)) := TheoryTransport.sentence (source_projectionGetZeroConstructed w x i y)

theorem native_projectionGetZeroConstructed {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetZeroConstructedSentence w x i y)) := ZFReplay.replay (projectionGetZeroConstructed_kernel_certificate w x i y)

def projectionGetHeadConstructedSentence {m} (w tag first rest p x z : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem tag w).imp ((Formula.mem first w).imp ((Formula.mem rest w).imp ((GodelPairSyntax.code w first rest p).imp ((StructuralNodeSyntax.raw w tag p x).imp ((empty z).imp ((ProjectionTraceSyntax.get w x z first))))))))).close

theorem source_projectionGetHeadConstructed {m} (w tag first rest p x z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetHeadConstructedSentence w tag first rest p x z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty z) (Context.add (StructuralNodeSyntax.raw w tag p x) (Context.add (GodelPairSyntax.code w first rest p) (Context.add (Formula.mem rest w) (Context.add (Formula.mem first w) (Context.add (Formula.mem tag w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))))
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
  have h1 : Derives Δ (Formula.mem tag w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h2 : Derives Δ (Formula.mem first w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h3 : Derives Δ (Formula.mem rest w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h4 : Derives Δ (GodelPairSyntax.code w first rest p) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h5 : Derives Δ (StructuralNodeSyntax.raw w tag p x) := .hyp (Or.inr (Or.inl rfl))
  have h6 : Derives Δ (empty z) := .hyp (Or.inl rfl)
  exact ProjectionGetConstructors.head_checked hZ w tag first rest p x z h0 h1 h2 h3 h4 h5 h6

theorem projectionGetHeadConstructed_kernel_certificate {m} (w tag first rest p x z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetHeadConstructedSentence w tag first rest p x z)) := TheoryTransport.sentence (source_projectionGetHeadConstructed w tag first rest p x z)

theorem native_projectionGetHeadConstructed {m} (w tag first rest p x z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetHeadConstructedSentence w tag first rest p x z)) := ZFReplay.replay (projectionGetHeadConstructed_kernel_certificate w tag first rest p x z)

def projectionGetTailConstructedSentence {m} (w tag first rest p x i s y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem tag w).imp ((Formula.mem first w).imp ((Formula.mem rest w).imp ((GodelPairSyntax.code w first rest p).imp ((StructuralNodeSyntax.raw w tag p x).imp ((successor s i).imp ((ProjectionTraceSyntax.get w rest i y).imp ((ProjectionTraceSyntax.get w x s y)))))))))).close

theorem source_projectionGetTailConstructed {m} (w tag first rest p x i s y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetTailConstructedSentence w tag first rest p x i s y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.get w rest i y) (Context.add (successor s i) (Context.add (StructuralNodeSyntax.raw w tag p x) (Context.add (GodelPairSyntax.code w first rest p) (Context.add (Formula.mem rest w) (Context.add (Formula.mem first w) (Context.add (Formula.mem tag w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))))))
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
  have h1 : Derives Δ (Formula.mem tag w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have h2 : Derives Δ (Formula.mem first w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have h3 : Derives Δ (Formula.mem rest w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h4 : Derives Δ (GodelPairSyntax.code w first rest p) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h5 : Derives Δ (StructuralNodeSyntax.raw w tag p x) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h6 : Derives Δ (successor s i) := .hyp (Or.inr (Or.inl rfl))
  have h7 : Derives Δ (ProjectionTraceSyntax.get w rest i y) := .hyp (Or.inl rfl)
  exact ProjectionGetConstructors.tail_checked hZ w tag first rest p x i s y h0 h1 h2 h3 h4 h5 h6 h7

theorem projectionGetTailConstructed_kernel_certificate {m} (w tag first rest p x i s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetTailConstructedSentence w tag first rest p x i s y)) := TheoryTransport.sentence (source_projectionGetTailConstructed w tag first rest p x i s y)

theorem native_projectionGetTailConstructed {m} (w tag first rest p x i s y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetTailConstructedSentence w tag first rest p x i s y)) := ZFReplay.replay (projectionGetTailConstructed_kernel_certificate w tag first rest p x i s y)

def projectionGetZeroIndexIffSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((empty i).imp (((ProjectionTraceSyntax.get w x i y).iff ((Formula.mem x w).conj (RawCodeGetSyntax.get w x i y)))))).close

theorem source_projectionGetZeroIndexIff {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetZeroIndexIffSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty i) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (empty i) := .hyp (Or.inl rfl)
  exact ProjectionGetZeroIndex.checked_iff hZ w x i y h0 h1

theorem projectionGetZeroIndexIff_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetZeroIndexIffSentence w x i y)) := TheoryTransport.sentence (source_projectionGetZeroIndexIff w x i y)

theorem native_projectionGetZeroIndexIff {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetZeroIndexIffSentence w x i y)) := ZFReplay.replay (projectionGetZeroIndexIff_kernel_certificate w x i y)

def projectionGetAllInternalCorrectSentence {m} (w : Fin m) : Source.Sentence := ((omega w).imp ((.all ((Formula.mem (Fin.last m) w.castSucc).imp (ProjectionGetInductionSyntax.correct w.castSucc (Fin.last m)))))).close

theorem source_projectionGetAllInternalCorrect {m} (w : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetAllInternalCorrectSentence w) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectionGetInduction.all_correct hZ w h0

theorem projectionGetAllInternalCorrect_kernel_certificate {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetAllInternalCorrectSentence w)) := TheoryTransport.sentence (source_projectionGetAllInternalCorrect w)

theorem native_projectionGetAllInternalCorrect {m} (w : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetAllInternalCorrectSentence w)) := ZFReplay.replay (projectionGetAllInternalCorrect_kernel_certificate w)

def projectionGetAtInternalIndexIffSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((ProjectionGetInductionSyntax.point w x i y)))).close

theorem source_projectionGetAtInternalIndexIff {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetAtInternalIndexIffSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inl rfl)
  exact ProjectionGetInduction.checked_at_index hZ w x i y h0 h1

theorem projectionGetAtInternalIndexIff_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetAtInternalIndexIffSentence w x i y)) := TheoryTransport.sentence (source_projectionGetAtInternalIndexIff w x i y)

theorem native_projectionGetAtInternalIndexIff {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetAtInternalIndexIffSentence w x i y)) := ZFReplay.replay (projectionGetAtInternalIndexIff_kernel_certificate w x i y)

def projectionGetAllCandidatesIffSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp (((ProjectionTraceSyntax.get w x i y).iff ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeGetSyntax.get w x i y)))))).close

theorem source_projectionGetAllCandidatesIff {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetAllCandidatesIffSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectionGetInduction.checked_iff hZ w x i y h0

theorem projectionGetAllCandidatesIff_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetAllCandidatesIffSentence w x i y)) := TheoryTransport.sentence (source_projectionGetAllCandidatesIff w x i y)

theorem native_projectionGetAllCandidatesIff {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetAllCandidatesIffSentence w x i y)) := ZFReplay.replay (projectionGetAllCandidatesIff_kernel_certificate w x i y)

def projectionGetSoundSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.get w x i y).imp ((RawCodeGetSyntax.get w x i y)))).close

theorem source_projectionGetSound {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetSoundSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.get w x i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectionTraceSyntax.get w x i y) := .hyp (Or.inl rfl)
  exact ProjectionGetInduction.checked_sound hZ w x i y h0 h1

theorem projectionGetSound_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetSoundSentence w x i y)) := TheoryTransport.sentence (source_projectionGetSound w x i y)

theorem native_projectionGetSound {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetSoundSentence w x i y)) := ZFReplay.replay (projectionGetSound_kernel_certificate w x i y)

def projectionGetCompleteSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((Formula.mem i w).imp ((RawCodeGetSyntax.get w x i y).imp ((ProjectionTraceSyntax.get w x i y)))))).close

theorem source_projectionGetComplete {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetCompleteSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeGetSyntax.get w x i y) (Context.add (Formula.mem i w) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (RawCodeGetSyntax.get w x i y) := .hyp (Or.inl rfl)
  exact ProjectionGetInduction.checked_complete hZ w x i y h0 h1 h2 h3

theorem projectionGetComplete_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetCompleteSentence w x i y)) := TheoryTransport.sentence (source_projectionGetComplete w x i y)

theorem native_projectionGetComplete {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetCompleteSentence w x i y)) := ZFReplay.replay (projectionGetComplete_kernel_certificate w x i y)

def projectionGetUniqueSentence {m} (w x i y z : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.get w x i y).imp ((ProjectionTraceSyntax.get w x i z).imp ((Formula.equal y z))))).close

theorem source_projectionGetUnique {m} (w x i y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetUniqueSentence w x i y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.get w x i z) (Context.add (ProjectionTraceSyntax.get w x i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectionTraceSyntax.get w x i y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectionTraceSyntax.get w x i z) := .hyp (Or.inl rfl)
  exact ProjectionGetInduction.checked_unique hZ w x i y z h0 h1 h2

theorem projectionGetUnique_kernel_certificate {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetUniqueSentence w x i y z)) := TheoryTransport.sentence (source_projectionGetUnique w x i y z)

theorem native_projectionGetUnique {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetUniqueSentence w x i y z)) := ZFReplay.replay (projectionGetUnique_kernel_certificate w x i y z)

def projectionGetObjectSuccessorStepSentence {m} (w i s : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((successor s i).imp ((ProjectionGetInductionSyntax.correct w i).imp ((ProjectionGetInductionSyntax.correct w s)))))).close

theorem source_projectionGetObjectSuccessorStep {m} (w i s : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetObjectSuccessorStepSentence w i s) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionGetInductionSyntax.correct w i) (Context.add (successor s i) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (successor s i) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (ProjectionGetInductionSyntax.correct w i) := .hyp (Or.inl rfl)
  exact ProjectionGetSuccessor.correct_successor hZ w i s h0 h1 h2 h3

theorem projectionGetObjectSuccessorStep_kernel_certificate {m} (w i s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetObjectSuccessorStepSentence w i s)) := TheoryTransport.sentence (source_projectionGetObjectSuccessorStep w i s)

theorem native_projectionGetObjectSuccessorStep {m} (w i s : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetObjectSuccessorStepSentence w i s)) := ZFReplay.replay (projectionGetObjectSuccessorStep_kernel_certificate w i s)

def projectionGetTailActualSubquerySentence {m} (env : Fin 5 → Fin m) (w V : Fin m) : Source.Sentence := ((omega w).imp ((HornExprSyntax.environmentNat 5 w env).imp ((ProjectionTraceSetSyntax.value w V).imp ((HornRuleSyntax.premises YesMetaZFC.Automation.ObjectProjection.getTail.premises w V env).imp ((ProjectionTraceSyntax.get w (env 2) (env 3) (env 4))))))).close

theorem source_projectionGetTailActualSubquery {m} (env : Fin 5 → Fin m) (w V : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionGetTailActualSubquerySentence env w V) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (HornRuleSyntax.premises YesMetaZFC.Automation.ObjectProjection.getTail.premises w V env) (Context.add (ProjectionTraceSetSyntax.value w V) (Context.add (HornExprSyntax.environmentNat 5 w env) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (HornExprSyntax.environmentNat 5 w env) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (ProjectionTraceSetSyntax.value w V) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (HornRuleSyntax.premises YesMetaZFC.Automation.ObjectProjection.getTail.premises w V env) := .hyp (Or.inl rfl)
  exact ProjectionGetLocal.tail_actual_child hZ w V env h0 h1 h2 h3

theorem projectionGetTailActualSubquery_kernel_certificate {m} (env : Fin 5 → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionGetTailActualSubquerySentence env w V)) := TheoryTransport.sentence (source_projectionGetTailActualSubquery env w V)

theorem native_projectionGetTailActualSubquery {m} (env : Fin 5 → Fin m) (w V : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionGetTailActualSubquerySentence env w V)) := ZFReplay.replay (projectionGetTailActualSubquery_kernel_certificate env w V)

def projectionFieldZeroConstructedSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem i w).imp ((empty x).imp ((empty y).imp ((ProjectionTraceSyntax.field w x i y)))))).close

theorem source_projectionFieldZeroConstructed {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldZeroConstructedSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (empty y) (Context.add (empty x) (Context.add (Formula.mem i w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (empty x) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (empty y) := .hyp (Or.inl rfl)
  exact ProjectionFieldConstructors.zero_checked hZ w x i y h0 h1 h2 h3

theorem projectionFieldZeroConstructed_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldZeroConstructedSentence w x i y)) := TheoryTransport.sentence (source_projectionFieldZeroConstructed w x i y)

theorem native_projectionFieldZeroConstructed {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldZeroConstructedSentence w x i y)) := ZFReplay.replay (projectionFieldZeroConstructed_kernel_certificate w x i y)

def projectionFieldRawConstructedSentence {m} (w tag p x i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem tag w).imp ((Formula.mem p w).imp ((StructuralNodeSyntax.raw w tag p x).imp ((ProjectionTraceSyntax.get w p i y).imp ((ProjectionTraceSyntax.field w x i y))))))).close

theorem source_projectionFieldRawConstructed {m} (w tag p x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldRawConstructedSentence w tag p x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.get w p i y) (Context.add (StructuralNodeSyntax.raw w tag p x) (Context.add (Formula.mem p w) (Context.add (Formula.mem tag w) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have h1 : Derives Δ (Formula.mem tag w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 : Derives Δ (Formula.mem p w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h3 : Derives Δ (StructuralNodeSyntax.raw w tag p x) := .hyp (Or.inr (Or.inl rfl))
  have h4 : Derives Δ (ProjectionTraceSyntax.get w p i y) := .hyp (Or.inl rfl)
  exact ProjectionFieldConstructors.positive_checked hZ w tag p x i y h0 h1 h2 h3 h4

theorem projectionFieldRawConstructed_kernel_certificate {m} (w tag p x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldRawConstructedSentence w tag p x i y)) := TheoryTransport.sentence (source_projectionFieldRawConstructed w tag p x i y)

theorem native_projectionFieldRawConstructed {m} (w tag p x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldRawConstructedSentence w tag p x i y)) := ZFReplay.replay (projectionFieldRawConstructed_kernel_certificate w tag p x i y)

def projectionFieldAllCandidatesIffSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp (((ProjectionTraceSyntax.field w x i y).iff ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeFieldSyntax.field w x i y)))))).close

theorem source_projectionFieldAllCandidatesIff {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldAllCandidatesIffSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact ProjectionField.checked_iff hZ w x i y h0

theorem projectionFieldAllCandidatesIff_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldAllCandidatesIffSentence w x i y)) := TheoryTransport.sentence (source_projectionFieldAllCandidatesIff w x i y)

theorem native_projectionFieldAllCandidatesIff {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldAllCandidatesIffSentence w x i y)) := ZFReplay.replay (projectionFieldAllCandidatesIff_kernel_certificate w x i y)

def projectionFieldSoundSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.field w x i y).imp ((RawCodeFieldSyntax.field w x i y)))).close

theorem source_projectionFieldSound {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldSoundSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.field w x i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inl rfl))
  have h1 : Derives Δ (ProjectionTraceSyntax.field w x i y) := .hyp (Or.inl rfl)
  exact ProjectionField.checked_sound hZ w x i y h0 h1

theorem projectionFieldSound_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldSoundSentence w x i y)) := TheoryTransport.sentence (source_projectionFieldSound w x i y)

theorem native_projectionFieldSound {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldSoundSentence w x i y)) := ZFReplay.replay (projectionFieldSound_kernel_certificate w x i y)

def projectionFieldCompleteSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((Formula.mem x w).imp ((Formula.mem i w).imp ((RawCodeFieldSyntax.field w x i y).imp ((ProjectionTraceSyntax.field w x i y)))))).close

theorem source_projectionFieldComplete {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldCompleteSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (RawCodeFieldSyntax.field w x i y) (Context.add (Formula.mem i w) (Context.add (Formula.mem x w) (Context.add (omega w) (Source.SetLanguage.ZF.at m))))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have h1 : Derives Δ (Formula.mem x w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h2 : Derives Δ (Formula.mem i w) := .hyp (Or.inr (Or.inl rfl))
  have h3 : Derives Δ (RawCodeFieldSyntax.field w x i y) := .hyp (Or.inl rfl)
  exact ProjectionField.checked_complete hZ w x i y h0 h1 h2 h3

theorem projectionFieldComplete_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldCompleteSentence w x i y)) := TheoryTransport.sentence (source_projectionFieldComplete w x i y)

theorem native_projectionFieldComplete {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldCompleteSentence w x i y)) := ZFReplay.replay (projectionFieldComplete_kernel_certificate w x i y)

def projectionFieldUniqueSentence {m} (w x i y z : Fin m) : Source.Sentence := ((omega w).imp ((ProjectionTraceSyntax.field w x i y).imp ((ProjectionTraceSyntax.field w x i z).imp ((Formula.equal y z))))).close

theorem source_projectionFieldUnique {m} (w x i y z : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (projectionFieldUniqueSentence w x i y z) := by
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  let Δ : Context m := Context.add (ProjectionTraceSyntax.field w x i z) (Context.add (ProjectionTraceSyntax.field w x i y) (Context.add (omega w) (Source.SetLanguage.ZF.at m)))
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    apply ZFContext.add
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inr (Or.inr (Or.inl rfl)))
  have h1 : Derives Δ (ProjectionTraceSyntax.field w x i y) := .hyp (Or.inr (Or.inl rfl))
  have h2 : Derives Δ (ProjectionTraceSyntax.field w x i z) := .hyp (Or.inl rfl)
  exact ProjectionField.checked_unique hZ w x i y z h0 h1 h2

theorem projectionFieldUnique_kernel_certificate {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (projectionFieldUniqueSentence w x i y z)) := TheoryTransport.sentence (source_projectionFieldUnique w x i y z)

theorem native_projectionFieldUnique {m} (w x i y z : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (projectionFieldUniqueSentence w x i y z)) := ZFReplay.replay (projectionFieldUnique_kernel_certificate w x i y z)

def originalSevenProjectionNumericIffsSentence {m} (w x i y : Fin m) : Source.Sentence := ((omega w).imp ((((ProjectionTraceSyntax.tag w x y).iff ((Formula.mem x w).conj (PairingProjectionSyntax.step true true w x y))).conj (((ProjectionTraceSyntax.get w x i y).iff ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeGetSyntax.get w x i y)))).conj ((ProjectionTraceSyntax.field w x i y).iff ((Formula.mem x w).conj ((Formula.mem i w).conj (RawCodeFieldSyntax.field w x i y)))))))).close

theorem source_originalSevenProjectionNumericIffs {m} (w x i y : Fin m) : Derives (Source.SetLanguage.ZF.at 0) (originalSevenProjectionNumericIffsSentence w x i y) := by
  apply close_derives
  apply Derives.impI
  let Δ : Context m := Context.add (omega w) (Source.SetLanguage.ZF.at m)
  have hZ : ZFContext.Evidence Δ := by
    apply ZFContext.add
    exact ZFContext.source_ZF m
  have h0 : Derives Δ (omega w) := .hyp (Or.inl rfl)
  exact Derives.conjI (ProjectionTag.checked_iff hZ w x y h0) (Derives.conjI (ProjectionGetInduction.checked_iff hZ w x i y h0) (ProjectionField.checked_iff hZ w x i y h0))

theorem originalSevenProjectionNumericIffs_kernel_certificate {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives ZFEquivalence.sourceZF []
    (Translation.sentence (originalSevenProjectionNumericIffsSentence w x i y)) := TheoryTransport.sentence (source_originalSevenProjectionNumericIffs w x i y)

theorem native_originalSevenProjectionNumericIffs {m} (w x i y : Fin m) : YesMetaZFC.Logic.FirstOrder.Derives nativeZF []
    (Translation.sentence (originalSevenProjectionNumericIffsSentence w x i y)) := ZFReplay.replay (originalSevenProjectionNumericIffs_kernel_certificate w x i y)

end PPAC.Migration.Internal.ObjectProjectionGetField
