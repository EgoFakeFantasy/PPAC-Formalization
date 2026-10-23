import PPAC.Migration.Internal.OriginalFormulaMatrix

/-! 全十一真实原公式规则的子运行合成；原搜索界及实际通用轨迹见证在内部消去。 -/
namespace PPAC.Migration.Internal.OriginalFormulaTraceRules
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornUniversalTraceRules
open YesMetaZFC.Automation.ObjectHorn (Rule)
open YesMetaZFC.Automation.ObjectSyntaxTransform (constant binary unary)

theorem selected_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (hr : rule ∈ OriginalFormulaClasses.selected)
    (w r : Fin m) (env : Fin rule.arity → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat rule.arity w env)) (ht : Derives Γ (tracedMatrix rule w r env)) :
    Derives Γ (HornLookupConditionSyntax.condition w r) :=
  OriginalRuleHeadVariables.apply_original_rule hZ rule (OriginalFormulaClasses.selected_mem rule hr) w r env hw hn ht

theorem constant_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (tag : Nat) (hr : (constant tag) ∈ OriginalFormulaClasses.selected)
    (w n q r : Fin m) (env : Fin 3 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 3 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)))
    (hd : Derives Γ (OriginalFormulaLocalData.constant tag w n q)) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  selected_condition hZ (constant tag) hr w r env hw hn
    (.impE (.conjR (OriginalFormulaMatrix.constant_at_row hZ three tag w n q r env hw hn hm hc)) hd)

theorem binary_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag kind : Nat) (hr : (binary tag kind) ∈ OriginalFormulaClasses.selected)
    (w n q r : Fin m) (env : Fin 7 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 7 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r))

    (hd : Derives Γ (OriginalFormulaLocalData.binary tag kind w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5) (env 6))) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  selected_condition hZ (binary tag kind) hr w r env hw hn
    (.impE (.conjR (OriginalFormulaMatrix.binary_at_row hZ tag kind w n q r env hw hn hc)) hd)

theorem nonbinder_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (hr : (unary tag false) ∈ OriginalFormulaClasses.selected)
    (w n q r : Fin m) (env : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 5 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r))

    (hd : Derives Γ (OriginalFormulaLocalData.unary tag w (env 0) (env 1) (env 2) n q (env 3) (env 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  selected_condition hZ (unary tag false) hr w r env hw hn
    (.impE (.conjR (OriginalFormulaMatrix.nonbinder_at_row hZ tag w n q r env hw hn hc)) hd)

theorem binder_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (hr : (unary tag true) ∈ OriginalFormulaClasses.selected)
    (w n q r childDepth : Fin m) (env : Fin 5 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 5 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r))
    (hs : Derives Γ (successor childDepth (env 1)))
    (hd : Derives Γ (OriginalFormulaLocalData.unary tag w (env 0) childDepth (env 2) n q (env 3) (env 4))) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  selected_condition hZ (unary tag true) hr w r env hw hn
    (.impE (.conjR (OriginalFormulaMatrix.binder_at_row hZ tag w n q r childDepth env hw hn hc hs)) hd)

theorem application_condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w n q r : Fin m) (env : Fin 6 → Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (environmentNat 6 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r))

    (hd : Derives Γ (OriginalFormulaLocalData.application w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5))) : Derives Γ (HornLookupConditionSyntax.condition w r) :=
  selected_condition hZ (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) (by simp [OriginalFormulaClasses.selected]) w r env hw hn
    (.impE (.conjR (OriginalFormulaMatrix.application_at_row hZ w n q r env hw hn hc)) hd)

end PPAC.Migration.Internal.OriginalFormulaTraceRules
