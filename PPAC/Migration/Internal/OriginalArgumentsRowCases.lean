import PPAC.Migration.Internal.OriginalArgumentsNilValue

/-! 给定真实原五字段候选行，nil/cons局部矩阵精确判定全部输入/输出候选的结构与子轨迹。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsRowCases
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornUniversalTraceRules
open YesMetaZFC.Automation.ObjectSyntaxTransform (nilArguments consArguments)

theorem nil_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (w n q r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((tracedMatrix nilArguments w r env).iff ((StructuralListSyntax.nilCode w n).conj (StructuralListSyntax.nilCode w q))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := tracedMatrix nilArguments w r env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ0 := ZFContext.add hZ E
    have hh := Derives.conjL hE
    rw [OriginalArgumentsExpr.actual_nil_head] at hh
    have hfirst := HornRowFields.field_graph hZ0 2 OriginalArgumentsExpr.nilFields w r env (HornRowFields.five (env 0) (env 1) (env 2) n q) 3 (add hw E) (add hn E) hh (add hc E)
    have hsecond := HornRowFields.field_graph hZ0 2 OriginalArgumentsExpr.nilFields w r env (HornRowFields.five (env 0) (env 1) (env 2) n q) 4 (add hw E) (add hn E) hh (add hc E)
    exact .conjI (.impE (.conjL (OriginalArgumentsNilValue.nil_iff hZ0 w n env (add hw E) (add hn E))) hfirst)
      (.impE (.conjL (OriginalArgumentsNilValue.nil_iff hZ0 w q env (add hw E) (add hn E))) hsecond)
  · apply Derives.impI
    let E := (StructuralListSyntax.nilCode w n).conj (StructuralListSyntax.nilCode w q)
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have he := OriginalArgumentsRuleMatrix.nil_matrix_iff (ZFContext.add hZ E) three w n q r env (add hw E) (add hn E) (add hm E) (.conjL hE) (.conjR hE)
    exact .impE (.conjR he) (add hc E)

theorem cons_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n q r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((tracedMatrix consArguments w r env).iff
      (((StructuralListSyntax.consCode w (env 3) (env 4) n).conj (StructuralListSyntax.consCode w (env 5) (env 6) q)).conj
        ((OriginalTransformRowSyntax.run 1 w (env 0) (env 1) (env 2) (env 3) (env 5)).conj
          (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 6))))) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := tracedMatrix consArguments w r env
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ0 := ZFContext.add hZ E
    have hh := Derives.conjL hE
    rw [OriginalArgumentsExpr.actual_cons_head] at hh
    have hv (i : Fin 7) : Derives (Context.add E Γ) (graph (.var i) w env (env i)) := .conjI (environmentNat_at _ _ (add hn E) i) (.eqRefl _)
    have hfirst := HornRowFields.field_graph hZ0 2 OriginalArgumentsExpr.consFields w r env (HornRowFields.five (env 0) (env 1) (env 2) n q) 3 (add hw E) (add hn E) hh (add hc E)
    have hsecond := HornRowFields.field_graph hZ0 2 OriginalArgumentsExpr.consFields w r env (HornRowFields.five (env 0) (env 1) (env 2) n q) 4 (add hw E) (add hn E) hh (add hc E)
    have hN := Derives.impE (.conjL (HornExprStructural.cons_iff hZ0 (.var 3) (.var 4) w (env 3) (env 4) n env (add hw E) (add hn E) (hv 3) (hv 4))) hfirst
    have hQ := Derives.impE (.conjL (HornExprStructural.cons_iff hZ0 (.var 5) (.var 6) w (env 5) (env 6) q env (add hw E) (add hn E) (hv 5) (hv 6))) hsecond
    have he := OriginalArgumentsRuleMatrix.cons_matrix_iff hZ0 w n q r env (add hw E) (add hn E) hN hQ
    exact .conjI (.conjI hN hQ) (.conjR (.impE (.conjL he) hE))
  · apply Derives.impI
    let E := ((StructuralListSyntax.consCode w (env 3) (env 4) n).conj (StructuralListSyntax.consCode w (env 5) (env 6) q)).conj
      ((OriginalTransformRowSyntax.run 1 w (env 0) (env 1) (env 2) (env 3) (env 5)).conj (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 6)))
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have he := OriginalArgumentsRuleMatrix.cons_matrix_iff (ZFContext.add hZ E) w n q r env (add hw E) (add hn E) (.conjL (.conjL hE)) (.conjR (.conjL hE))
    exact .impE (.conjR he) (.conjI (add hc E) (.conjR hE))

end PPAC.Migration.Internal.OriginalArgumentsRowCases
