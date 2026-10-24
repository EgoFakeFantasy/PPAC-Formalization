import PPAC.Migration.Internal.SmallModeArgumentsNil
import PPAC.Migration.Internal.OriginalArgumentCaseSyntax

/-! 原nilArguments的arity=3存在赋值实际消去／构造，保持任意内部候选行。 -/
namespace PPAC.Migration.Internal.SmallModeArgumentsNilApplication
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (nilArguments rules)

theorem application_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (hk : k < 4)
    (w mode depth parameter input output r V : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral k mode))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornApplicationSyntax.application nilArguments w r V).iff (OriginalArgumentCaseSyntax.nilData w input output)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := HornApplicationSyntax.application nilArguments w r V
    let B := HornApplicationSyntax.body nilArguments w r V
    let Δ := Context.add B (raisedContext 3 (Context.add E Γ))
    apply HornApplicationRules.eliminate_application nilArguments w r V _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 3)) := HornBinderRules.under_body 3 (add hp E) B
    have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (lift hw)
    have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral k (old 3 mode)) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ (old 3)) (lift hm)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 2 (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 input) (old 3 output) (old 3 r)) := of_eq (OriginalTransformRowSyntax.row_rename 2 _ _ _ _ _ _ _ (old 3)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 3 w) (old 3 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 3)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hmatrix := Derives.impE (.conjL (HornUniversalTraceRules.matrix_iff nilArguments (old 3 w) (old 3 V) (old 3 r) (slot 3) hv1)) (.conjR (.conjR hB))
    have he := OriginalArgumentsMetadata.nil_metadata hZ1 _ _ _ _ _ _ _ (slot 3) hw1 (.conjL hB) (.conjL hmatrix) hc1
    have hmEnv := SyntaxNumeralSyntax.output_subst k (old 3 mode) (slot 3 0) (.conjL he) hm1
    have hcEnv := OriginalRowMetadataSubstitution.row_fields 2 _ _ _ _ _ _ _ _ _ _ (.conjL he) (.conjL (.conjR he)) (.conjR (.conjR he)) hc1
    have ho := Derives.impE (.conjL (SmallModeArgumentsNil.nil_at_row hZ1 k hk (old 3 w) (old 3 input) (old 3 output) (old 3 r) (slot 3) hw1 (.conjL hB) hmEnv hcEnv)) hmatrix
    exact of_eq (OriginalArgumentCaseSyntax.nilData_rename w input output (old 3)).symm ho
  · apply Derives.impI
    let E := OriginalArgumentCaseSyntax.nilData w input output
    let env := OriginalLookupExpr.rowFields mode depth parameter
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ0 := ZFContext.add hZ E
    have hn : Derives (Context.add E Γ) (environmentNat 3 w env) := by
      apply HornApplicationRules.intro_nat
      intro i
      exact Fin.cases (OriginalArgumentsMetadata.field_natural hZ0 2 w mode depth parameter input output r 0 (add hw E) (add hc E))
        (fun j => Fin.cases (OriginalArgumentsMetadata.field_natural hZ0 2 w mode depth parameter input output r 1 (add hw E) (add hc E))
          (fun _ => OriginalArgumentsMetadata.field_natural hZ0 2 w mode depth parameter input output r 2 (add hw E) (add hc E)) j) i
    have ht := Derives.impE (.conjR (SmallModeArgumentsNil.nil_matrix_iff hZ0 k hk w input output r env (add hw E) hn (add hm E) (.conjL hE) (.conjR hE))) (add hc E)
    have hmatrix := Derives.impE (.conjR (HornUniversalTraceRules.matrix_iff nilArguments w V r env (add hv E))) ht
    have hb := OriginalScalarPositive.head_bound hZ0 nilArguments (OriginalRuleHeadVariables.head_variables nilArguments (by simp [rules])) w r env (add hw E) hn (.conjL ht)
    exact HornApplicationRules.intro_application nilArguments w r V env hn hb hmatrix

end PPAC.Migration.Internal.SmallModeArgumentsNilApplication
