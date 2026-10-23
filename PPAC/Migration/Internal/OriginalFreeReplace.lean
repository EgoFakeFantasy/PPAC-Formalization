import PPAC.Migration.Internal.OriginalFreeReplaceSound
import PPAC.Migration.Internal.HornLookupPowerCondition

/-! 原模式3自由变量的完整内部轨迹与独立查找执行双向对应。 -/
namespace PPAC.Migration.Internal.OriginalFreeReplace
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (freeReplace varCode)

theorem trace_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4)) := by
  let B := HornLookupConditionSyntax.witness w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hZ1 := ZFContext.under hZ B
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hc1 : Derives Δ (SyntaxNodeSyntax.constructor 5 1 w.castSucc (fun i => (xs i).castSucc) r.castSucc) := of_eq (SyntaxNodeSyntax.constructor_rename 5 1 w xs r Fin.castSucc) (under hc B)
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral 3 (xs 0).castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hv1 : Derives Δ (SyntaxVariableSyntax.code false w.castSucc idx.castSucc (xs 3).castSucc) := of_eq (SyntaxVariableSyntax.code_rename false w idx (xs 3) Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ha := OriginalVariableDispatch.closed_member_application hZ1 true false _ _ _ _ _ hw1 hc1 hm1 hv1 (.conjR (.conjR hB)) (.conjL (.conjR hB))
  have ho := OriginalFreeReplaceSound.application_execution hZ1 _ _ _ _ _ hw1 hc1 hv1 (.conjR (.conjR hB)) ha
  exact of_eq (LookupTableExecutionSyntax.executed_rename w (xs 2) idx (xs 4) Fin.castSucc).symm ho

theorem execution_trace {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3)))
    (he : Derives Γ (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) := by
  let env := HornLookupPositiveSyntax.env4 (xs 1) (xs 2) idx (xs 4)
  have hr := SyntaxNodeInjective.constructor_range hZ 5 1 w xs r hw hc
  have hn (i : Fin 5) : Derives Γ (.mem (xs i) w) := StructuralListTraceOrder.member_member hZ w (xs i) r hw hr (SyntaxConstructors.child_member hZ 5 1 w xs r i hw hc)
  have hi := SyntaxVariableDecode.index_natural false w idx (xs 3) hv
  have henv := HornLookupPositiveSyntax.env4_natural w (xs 1) (xs 2) idx (xs 4) (hn 1) (hn 2) hi (hn 4)
  have h0 : Derives Γ (graph (.literal 3) w env (xs 0)) := hm
  have h1 : Derives Γ (graph (.var 0) w env (xs 1)) := .conjI (hn 1) (.eqRefl _)
  have h2 : Derives Γ (graph (.var 1) w env (xs 2)) := .conjI (hn 2) (.eqRefl _)
  have hx : Derives Γ (graph (.var 2) w env idx) := .conjI hi (.eqRefl _)
  have h3 : Derives Γ (graph (varCode true (.var 2)) w env (xs 3)) := HornVariableExpr.code_graph false (.var 2) w idx (xs 3) env hx hv
  have h4 : Derives Γ (graph (.var 3) w env (xs 4)) := .conjI (hn 4) (.eqRefl _)
  have hs : ∀ i, Derives Γ (graph (OriginalFreeReplaceSound.fields i) w env (xs i)) :=
    fun i => Fin.cases h0 (fun a => Fin.cases h1 (fun b => Fin.cases h2 (fun c => Fin.cases h3 (fun d => Fin.cases h4 (fun z => Fin.elim0 z) d) c) b) a) i
  have hh := Derives.impE (.conjR (HornExprConstructor.constructor_iff hZ 5 1 OriginalFreeReplaceSound.fields w r env xs hw henv hs)) hc
  exact OriginalScalarPositive.free_three hZ w r env hw henv hh he

theorem trace_iff_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).iff (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact trace_execution (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact execution_trace (ZFContext.add hZ _) w r idx xs (add hw _) (add hc _) (add hm _) (add hv _) (.hyp (Or.inl rfl))

theorem power_trace_iff_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3))) :
    Derives Γ ((HornLookupPowerCondition.condition w r).iff (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4))) := by
  have hs := HornLookupSearchCondition.condition_iff hZ w r hw
  have hp := HornLookupPowerCondition.search_condition_iff hZ w r
  exact SyntaxTypeLocalTransfer.iff_trans hp (SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hs) (.conjL hs)) (trace_iff_execution hZ w r idx xs hw hc hm hv))

theorem rejected_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w r idx : Fin m) (xs : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w xs r)) (hm : Derives Γ (SyntaxNumeralSyntax.numeral 3 (xs 0)))
    (hv : Derives Γ (SyntaxVariableSyntax.code false w idx (xs 3))) :
    Derives Γ ((HornLookupConditionSyntax.condition w r).neg.iff (LookupTableExecutionSyntax.executed w (xs 2) idx (xs 4)).neg) :=
  FormulaTransformCongruence.imp_congr (trace_iff_execution hZ w r idx xs hw hc hm hv) (SyntaxTypeLocalTransfer.iff_refl .bot)

end PPAC.Migration.Internal.OriginalFreeReplace
