import PPAC.Migration.Internal.SmallModeFormulaMatrix
import PPAC.Migration.Internal.OriginalFormulaArityApplications

/-! 每个固定mode<4的原常量arity赋值正式消去／重建；原三槽赋值、界和真实trace不变。 -/
namespace PPAC.Migration.Internal.SmallModeFormulaConstantApplication
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax OriginalFormulaCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (constant binary unary)

theorem constant_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (modeIndex : Nat) (hSmall : modeIndex < 4) (tag : Nat) (hr : (constant tag) ∈ OriginalFormulaClasses.selected)
    (w mode depth parameter n q r V : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral modeIndex mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornApplicationSyntax.application (constant tag) w r V).iff (OriginalFormulaLocalData.constant tag w n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := HornApplicationSyntax.application (constant tag) w r V
    let B := HornApplicationSyntax.body (constant tag) w r V
    let Δ := Context.add B (raisedContext 3 (Context.add E Γ))
    apply HornApplicationRules.eliminate_application (constant tag) w r V _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 3)) := HornBinderRules.under_body 3 (add hp E) B
    have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 n) (old 3 q) (old 3 r)) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r (old 3)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 3 w) (old 3 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 3)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := Derives.impE (.conjL (HornUniversalTraceRules.matrix_iff (constant tag) (old 3 w) (old 3 V) (old 3 r) (slot 3) hv1)) (.conjR (.conjR hB))
    have hh := Derives.conjL ht
    rw [OriginalFormulaExpr.actual_constant_head tag] at hh
    have he := OriginalFormulaRowGraph.metadata_eq hZ1 3 0 1 2 (Expr.node (.literal tag) []) (Expr.node (.literal tag) []) (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 n) (old 3 q) (old 3 r) (slot 3) hw1 (.conjL hB) hh hc1
    have hcEnv := OriginalRowMetadataSubstitution.row_fields 3 _ _ _ _ _ _ _ _ _ _ (.conjL he) (.conjL (.conjR he)) (.conjR (.conjR he)) hc1
    have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral modeIndex (old 3 mode)) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ (old 3)) (lift hm)
    have hmEnv := SyntaxNumeralSyntax.output_subst modeIndex (old 3 mode) (slot 3 0) (.conjL he) hm1
    have hd := Derives.impE (.conjL (SmallModeFormulaMatrix.constant_at_row hZ1 modeIndex hSmall tag (old 3 w) (old 3 n) (old 3 q) (old 3 r) (slot 3) hw1 (.conjL hB) hmEnv hcEnv)) ht
    exact of_eq (OriginalFormulaLocalData.constant_rename tag w n q (old 3)).symm hd
  · apply Derives.impI
    let E := OriginalFormulaLocalData.constant tag w n q
    let env := OriginalLookupExpr.rowFields mode depth parameter
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ0 := ZFContext.add hZ E
    have hn : Derives (Context.add E Γ) (environmentNat 3 w env) := by
      apply HornApplicationRules.intro_nat
      intro i
      exact Fin.cases (OriginalArgumentsMetadata.field_natural hZ0 3 w mode depth parameter n q r 0 (add hw E) (add hc E))
        (fun j => Fin.cases (OriginalArgumentsMetadata.field_natural hZ0 3 w mode depth parameter n q r 1 (add hw E) (add hc E))
          (fun _ => OriginalArgumentsMetadata.field_natural hZ0 3 w mode depth parameter n q r 2 (add hw E) (add hc E)) j) i
    have htMatrix := Derives.impE (.conjR (SmallModeFormulaMatrix.constant_at_row hZ0 modeIndex hSmall tag w n q r env (add hw E) hn (add hm E) (add hc E))) hE
    have hmatrix := Derives.impE (.conjR (HornUniversalTraceRules.matrix_iff (constant tag) w V r env (add hv E))) htMatrix
    have hb := OriginalScalarPositive.head_bound hZ0 (constant tag) (OriginalRuleHeadVariables.head_variables (constant tag) (OriginalFormulaClasses.selected_mem (constant tag) hr)) w r env (add hw E) hn (.conjL htMatrix)
    have ho := HornApplicationRules.intro_application (constant tag) w r V env hn hb hmatrix
    exact ho

end PPAC.Migration.Internal.SmallModeFormulaConstantApplication
