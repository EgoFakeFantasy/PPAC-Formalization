import PPAC.Migration.Internal.OriginalArgumentRunNaturality
import PPAC.Migration.Internal.OriginalArgumentsNilApplication

/-! 原consArguments的arity=7赋值块与四个真实内部组件存在量词双向转换。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsConsApplication
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax OriginalArgumentCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (consArguments rules)

theorem application_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter input output r V : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 2 w mode depth parameter input output r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornApplicationSyntax.application consArguments w r V).iff (consCase w mode depth parameter input output)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := HornApplicationSyntax.application consArguments w r V
    let B := HornApplicationSyntax.body consArguments w r V
    let Δ := Context.add B (raisedContext 7 (Context.add E Γ))
    apply HornApplicationRules.eliminate_application consArguments w r V _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 7 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 7)) := HornBinderRules.under_body 7 (add hp E) B
    have hw1 : Derives Δ (omega (old 7 w)) := of_eq (omega_rename w (old 7)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 2 (old 7 w) (old 7 mode) (old 7 depth) (old 7 parameter) (old 7 input) (old 7 output) (old 7 r)) := of_eq (OriginalTransformRowSyntax.row_rename 2 _ _ _ _ _ _ _ (old 7)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 7 w) (old 7 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 7)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hmatrix := Derives.impE (.conjL (HornUniversalTraceRules.matrix_iff consArguments (old 7 w) (old 7 V) (old 7 r) (slot 7) hv1)) (.conjR (.conjR hB))
    have he := OriginalArgumentsMetadata.cons_metadata hZ1 _ _ _ _ _ _ _ (slot 7) hw1 (.conjL hB) (.conjL hmatrix) hc1
    have hcEnv := OriginalRowMetadataSubstitution.row_fields 2 _ _ _ _ _ _ _ _ _ _ (.conjL he) (.conjL (.conjR he)) (.conjR (.conjR he)) hc1
    have hd := Derives.impE (.conjL (OriginalArgumentsRowCases.cons_at_row hZ1 (old 7 w) (old 7 input) (old 7 output) (old 7 r) (slot 7) hw1 (.conjL hB) hcEnv)) hmatrix
    have hfirst := OriginalRowMetadataSubstitution.run_fields 1 _ _ _ _ _ _ _ _ _ (eq_symm (.conjL he)) (eq_symm (.conjL (.conjR he))) (eq_symm (.conjR (.conjR he))) (.conjL (.conjR hd))
    have hrest := OriginalRowMetadataSubstitution.run_fields 2 _ _ _ _ _ _ _ _ _ (eq_symm (.conjL he)) (eq_symm (.conjL (.conjR he))) (eq_symm (.conjR (.conjR he))) (.conjR (.conjR hd))
    have hout := intro_cons (old 7 w) (old 7 mode) (old 7 depth) (old 7 parameter) (old 7 input) (old 7 output) (slot 7 3) (slot 7 4) (slot 7 5) (slot 7 6) (.conjI (.conjL hd) (.conjI hfirst hrest))
    exact of_eq (consCase_rename w mode depth parameter input output (old 7)).symm hout
  · apply Derives.impI
    let E := consCase w mode depth parameter input output
    let B := consBody w mode depth parameter input output
    let Δ := Context.add B (raisedContext 4 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 4 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 4 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 4)) := HornBinderRules.under_body 4 (add hp E) B
    have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 2 (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 input) (old 4 output) (old 4 r)) := of_eq (OriginalTransformRowSyntax.row_rename 2 _ _ _ _ _ _ _ (old 4)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 4 w) (old 4 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 4)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hfirst := Derives.conjL (Derives.conjR hB)
    have hrest := Derives.conjR (Derives.conjR hB)
    have hmode := OriginalArgumentsMetadata.field_natural hZ1 2 _ _ _ _ _ _ _ 0 hw1 hc1
    have hdepth := OriginalArgumentsMetadata.field_natural hZ1 2 _ _ _ _ _ _ _ 1 hw1 hc1
    have hparameter := OriginalArgumentsMetadata.field_natural hZ1 2 _ _ _ _ _ _ _ 2 hw1 hc1
    have hh := OriginalArgumentRunNaturality.input_natural hZ1 1 _ _ _ _ _ _ hw1 hfirst
    have hH := OriginalArgumentRunNaturality.output_natural hZ1 1 _ _ _ _ _ _ hw1 hfirst
    have ht := OriginalArgumentRunNaturality.input_natural hZ1 2 _ _ _ _ _ _ hw1 hrest
    have hT := OriginalArgumentRunNaturality.output_natural hZ1 2 _ _ _ _ _ _ hw1 hrest
    let env : Fin 7 → Fin (m+4) := Fin.cases (old 4 mode) (Fin.cases (old 4 depth) (Fin.cases (old 4 parameter) (Fin.cases (slot 4 0) (Fin.cases (slot 4 1) (Fin.cases (slot 4 2) (fun _ => slot 4 3))))))
    have hn : Derives Δ (environmentNat 7 (old 4 w) env) := by
      apply HornApplicationRules.intro_nat
      intro i
      exact Fin.cases hmode (fun j => Fin.cases hdepth (fun k => Fin.cases hparameter (fun l => Fin.cases hh (fun a => Fin.cases ht (fun b => Fin.cases hH (fun _ => hT) b) a) l) k) j) i
    have htMatrix := Derives.impE (.conjR (OriginalArgumentsRuleMatrix.cons_matrix_iff hZ1 (old 4 w) (old 4 input) (old 4 output) (old 4 r) env hw1 hn (.conjL (.conjL hB)) (.conjR (.conjL hB)))) (.conjI hc1 (.conjI hfirst hrest))
    have hmatrix := Derives.impE (.conjR (HornUniversalTraceRules.matrix_iff consArguments (old 4 w) (old 4 V) (old 4 r) env hv1)) htMatrix
    have hb := OriginalScalarPositive.head_bound hZ1 consArguments (OriginalRuleHeadVariables.head_variables consArguments (by simp [rules])) _ _ env hw1 hn (.conjL htMatrix)
    have ho := HornApplicationRules.intro_application consArguments (old 4 w) (old 4 r) (old 4 V) env hn hb hmatrix
    exact of_eq (HornApplicationSyntax.application_rename consArguments w r V (old 4)).symm ho

end PPAC.Migration.Internal.OriginalArgumentsConsApplication
