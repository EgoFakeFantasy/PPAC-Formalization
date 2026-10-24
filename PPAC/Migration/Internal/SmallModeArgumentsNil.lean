import PPAC.Migration.Internal.SmallModeArgumentsGuard
import PPAC.Migration.Internal.OriginalArgumentsRowCases

/-! 任意固定小模式的原nil矩阵与真实候选行；原cons设施保持不变。 -/
namespace PPAC.Migration.Internal.SmallModeArgumentsNil
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornUniversalTraceRules
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (nilArguments)

theorem nil_matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (hk : k < 4) (w n q r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral k (env 0)))
    (hN : Derives Γ (StructuralListSyntax.nilCode w n)) (hQ : Derives Γ (StructuralListSyntax.nilCode w q)) :
    Derives Γ ((tracedMatrix nilArguments w r env).iff (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r)) :=
  SyntaxTypeLocalTransfer.iff_trans (OriginalArgumentsRuleMatrix.nil_matrix_iff_head w r env (SmallModeArgumentsGuard.nil_guard hZ k hk w env hw hn hm))
    (OriginalArgumentsExpr.nil_head_iff hZ w n q r env hw hn hN hQ)

theorem nil_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (hk : k < 4) (w n q r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral k (env 0)))
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
    have he := SmallModeArgumentsNil.nil_matrix_iff (ZFContext.add hZ E) k hk w n q r env (add hw E) (add hn E) (add hm E) (.conjL hE) (.conjR hE)
    exact .impE (.conjR he) (add hc E)

end PPAC.Migration.Internal.SmallModeArgumentsNil
