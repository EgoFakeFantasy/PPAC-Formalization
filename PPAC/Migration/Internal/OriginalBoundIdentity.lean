import PPAC.Migration.Internal.HornVariableExpr
import PPAC.Migration.Internal.HornLookupPowerCondition

/-! 原模式0/3绑定变量：完整内部轨迹当且仅当输出码等于输入码。 -/
namespace PPAC.Migration.Internal.OriginalBoundIdentity
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornApplicationSyntax HornBinderSyntax
open OriginalScalarClasses
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (boundIdentity varCode)

def fields (three : Bool) : Fin 5 → Expr 3 := HornRowFields.five (.literal (mode three)) (.var 0) (.var 1)
  (varCode false (.var 2)) (varCode false (.var 2))

theorem actual_head (three : Bool) : (boundIdentity (mode three)).head = Expr.node (.literal 1) (List.ofFn (fields three)) := rfl

theorem application_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w r R : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r))
    (ha : Derives Γ (application (boundIdentity (mode three)) w r R)) : Derives Γ (.equal (xs 4) (xs 3)) := by
  let rule := boundIdentity (mode three)
  let B := body rule w r R
  let Δ := Context.add B (raisedContext 3 Γ)
  apply HornApplicationRules.eliminate_application rule w r R _ ha
  have hZ1 := HornBinderRules.zf_body 3 hZ B
  have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 (old 3 w) (fun i => old 3 (xs i)) (old 3 r)) := of_eq
    (SyntaxNodeSyntax.constructor_rename 5 1 w xs r (old 3)) (HornBinderRules.under_body 3 hc B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph (Expr.node (.literal 1) (List.ofFn (fields three))) (old 3 w) (slot 3) (old 3 r)) := .conjL (.conjR (.conjR hB))
  have hinput := HornRowFields.field_graph hZ1 1 (fields three) _ _ _ _ 3 hw1 (.conjL hB) hg hc1
  have houtput := HornRowFields.field_graph hZ1 1 (fields three) _ _ _ _ 4 hw1 (.conjL hB) hg hc1
  have he := HornExprUnique.unique hZ1 (varCode false (.var 2)) _ _ _ _ hw1 (.conjL hB) houtput hinput
  simpa only [Formula.rename] using he

theorem trace_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3)))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (.equal (xs 4) (xs 3)) := by
  let B := HornLookupConditionSyntax.witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w.castSucc (fun i => (xs i).castSucc) r.castSucc) := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r Fin.castSucc) (under hc B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (mode three) (xs 0).castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code true w.castSucc idx.castSucc (xs 3).castSucc) := of_eq (SyntaxVariableSyntax.code_rename true w idx (xs 3) Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ha := OriginalVariableDispatch.closed_member_application hZ1 three true _ _ _ _ _ hw1 hc1 hm1 hv1 (.conjR (.conjR hB)) (.conjL (.conjR hB))
  exact application_identity hZ1 three _ _ _ _ hw1 hc1 ha

theorem identity_trace {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3))) (he : Derives Γ (.equal (xs 4) (xs 3))) :
    Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env := OriginalLookupExpr.rowFields (xs 1) (xs 2) idx
  have hr := SyntaxNodeInjective.constructor_range hZ 5 1 w xs r hw hc
  have hn (i : Fin 5) : Derives Γ (.mem (xs i) w) := StructuralListTraceOrder.member_member hZ w (xs i) r hw hr (SyntaxConstructors.child_member hZ 5 1 w xs r i hw hc)
  have hi := SyntaxVariableDecode.index_natural true w idx (xs 3) hv
  have henv : Derives Γ (environmentNat 3 w env) := HornApplicationRules.intro_nat w env
    (fun i => Fin.cases (hn 1) (fun j => Fin.cases (hn 2) (fun k => Fin.cases hi (fun z => Fin.elim0 z) k) j) i)
  have h0 : Derives Γ (graph (.literal (mode three)) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (hn 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (hn 2) (.eqRefl _)
  have hx : Derives Γ (graph (.var 2) w env idx) := .conjI hi (.eqRefl _)
  have h3 : Derives Γ (graph (varCode false (.var 2)) w env (xs 3)) := HornVariableExpr.code_graph true (.var 2) w idx (xs 3) env hx hv
  have h4 := HornExprSyntax.output_subst (varCode false (.var 2)) w (xs 3) (xs 4) env (eq_symm he) h3
  have hs : ∀ i, Derives Γ (graph (fields three i) w env (xs i)) :=
    fun i => Fin.cases h0 (fun a => Fin.cases h1 (fun b => Fin.cases h2 (fun c => Fin.cases h3 (fun d => Fin.cases h4 (fun z => Fin.elim0 z) d) c) b) a) i
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 (fields three) w r env xs hw henv hs)) hc
  have hmem : boundIdentity (mode three) ∈ YesMetaZFC.Automation.ObjectSyntaxTransform.rules := by cases three <;> simp [mode, YesMetaZFC.Automation.ObjectSyntaxTransform.rules]
  have hall : ∀ i : Fin 3, i ∈ (boundIdentity (mode three)).head.variables := by cases three <;> decide
  exact OriginalScalarPositive.leaf_condition hZ (boundIdentity (mode three)) hmem rfl rfl hall w r env hw henv hh

theorem trace_iff_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (.equal (xs 4) (xs 3))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact trace_identity (ZFContext.add hZ _) three w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact identity_trace (ZFContext.add hZ _) three w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))

theorem power_trace_iff_identity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3))) :
    Derives Γ ((HornLookupPowerCondition.condition w r).iff (.equal (xs 4) (xs 3))) := by
  have hs := HornLookupSearchCondition.condition_iff hZ w r hw
  have hp := HornLookupPowerCondition.search_condition_iff hZ w r
  exact SyntaxTypeLocalTransfer.iff_trans hp (SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hs) (.conjL hs)) (trace_iff_identity hZ three w r idx xs hw hc hm hv))

theorem rejected_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral (mode three) (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code true w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).neg.iff (Formula.equal (xs 4) (xs 3)).neg) :=
  FormulaTransformCongruence.imp_congr (trace_iff_identity hZ three w r idx xs hw hc hm hv) (SyntaxTypeLocalTransfer.iff_refl .bot)

end PPAC.Migration.Internal.OriginalBoundIdentity
