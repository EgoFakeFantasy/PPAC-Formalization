import PPAC.Migration.Internal.OriginalFormulaBinderDepth

/-! 原公式常量／二元／否定／关系应用的arity赋值块正式消去与重建。 -/
namespace PPAC.Migration.Internal.OriginalFormulaArityApplications
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax OriginalFormulaCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (constant binary unary)

theorem constant_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (tag : Nat) (hr : (constant tag) ∈ OriginalFormulaClasses.selected)
    (w mode depth parameter n q r V : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
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
    have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (old 3 mode)) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ (old 3)) (lift hm)
    have hmEnv := SyntaxNumeralSyntax.output_subst (OriginalScalarClasses.mode three) (old 3 mode) (slot 3 0) (.conjL he) hm1
    have hd := Derives.impE (.conjL (OriginalFormulaMatrix.constant_at_row hZ1 three tag (old 3 w) (old 3 n) (old 3 q) (old 3 r) (slot 3) hw1 (.conjL hB) hmEnv hcEnv)) ht
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
    have htMatrix := Derives.impE (.conjR (OriginalFormulaMatrix.constant_at_row hZ0 three tag w n q r env (add hw E) hn (add hm E) (add hc E))) hE
    have hmatrix := Derives.impE (.conjR (HornUniversalTraceRules.matrix_iff (constant tag) w V r env (add hv E))) htMatrix
    have hb := OriginalScalarPositive.head_bound hZ0 (constant tag) (OriginalRuleHeadVariables.head_variables (constant tag) (OriginalFormulaClasses.selected_mem (constant tag) hr)) w r env (add hw E) hn (.conjL htMatrix)
    have ho := HornApplicationRules.intro_application (constant tag) w r V env hn hb hmatrix
    exact ho

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag kind : Nat) (hr : (binary tag kind) ∈ OriginalFormulaClasses.selected)
    (w mode depth parameter n q r V : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornApplicationSyntax.application (binary tag kind) w r V).iff (binaryCase tag kind w mode depth parameter n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := HornApplicationSyntax.application (binary tag kind) w r V
    let B := HornApplicationSyntax.body (binary tag kind) w r V
    let Δ := Context.add B (raisedContext 7 (Context.add E Γ))
    apply HornApplicationRules.eliminate_application (binary tag kind) w r V _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 7 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 7)) := HornBinderRules.under_body 7 (add hp E) B
    have hw1 : Derives Δ (omega (old 7 w)) := of_eq (omega_rename w (old 7)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 (old 7 w) (old 7 mode) (old 7 depth) (old 7 parameter) (old 7 n) (old 7 q) (old 7 r)) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r (old 7)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 7 w) (old 7 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 7)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := Derives.impE (.conjL (HornUniversalTraceRules.matrix_iff (binary tag kind) (old 7 w) (old 7 V) (old 7 r) (slot 7) hv1)) (.conjR (.conjR hB))
    have hh := Derives.conjL ht
    rw [OriginalFormulaExpr.actual_binary_head tag kind] at hh
    have he := OriginalFormulaRowGraph.metadata_eq hZ1 3 0 1 2 (Expr.node (.literal tag) [.var 3,.var 4]) (Expr.node (.literal tag) [.var 5,.var 6]) (old 7 w) (old 7 mode) (old 7 depth) (old 7 parameter) (old 7 n) (old 7 q) (old 7 r) (slot 7) hw1 (.conjL hB) hh hc1
    have hcEnv := OriginalRowMetadataSubstitution.row_fields 3 _ _ _ _ _ _ _ _ _ _ (.conjL he) (.conjL (.conjR he)) (.conjR (.conjR he)) hc1
    have hd := Derives.impE (.conjL (OriginalFormulaMatrix.binary_at_row hZ1 tag kind (old 7 w) (old 7 n) (old 7 q) (old 7 r) (slot 7) hw1 (.conjL hB) hcEnv)) ht
    have hfix := OriginalFormulaDataSubstitution.binary_metadata tag kind (old 7 w) (slot 7 0) (slot 7 1) (slot 7 2) (old 7 n) (old 7 q) (slot 7 3) (slot 7 4) (slot 7 5) (slot 7 6) (old 7 mode) (old 7 depth) (old 7 parameter) (eq_symm (.conjL he)) (eq_symm (.conjL (.conjR he))) (eq_symm (.conjR (.conjR he))) hd
    have ho := intro_binary tag kind (old 7 w) (old 7 mode) (old 7 depth) (old 7 parameter) (old 7 n) (old 7 q) (slot 7 3) (slot 7 4) (slot 7 5) (slot 7 6) hfix
    exact of_eq (binaryCase_rename tag kind w mode depth parameter n q (old 7)).symm ho
  · apply Derives.impI
    let E := binaryCase tag kind w mode depth parameter n q
    let B := binaryBody tag kind w mode depth parameter n q
    let Δ := Context.add B (raisedContext 4 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 4 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 4 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 4)) := HornBinderRules.under_body 4 (add hp E) B
    have hw1 : Derives Δ (omega (old 4 w)) := of_eq (omega_rename w (old 4)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 (old 4 w) (old 4 mode) (old 4 depth) (old 4 parameter) (old 4 n) (old 4 q) (old 4 r)) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r (old 4)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 4 w) (old 4 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 4)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hMode := OriginalArgumentsMetadata.field_natural hZ1 3 _ _ _ _ _ _ _ 0 hw1 hc1
    have hDepth := OriginalArgumentsMetadata.field_natural hZ1 3 _ _ _ _ _ _ _ 1 hw1 hc1
    have hParam := OriginalArgumentsMetadata.field_natural hZ1 3 _ _ _ _ _ _ _ 2 hw1 hc1
    have hFirst := Derives.conjL (Derives.conjR hB)
    have hSecond := Derives.conjR (Derives.conjR hB)
    have hx := OriginalArgumentRunNaturality.input_natural hZ1 kind _ _ _ _ _ _ hw1 hFirst
    have hX := OriginalArgumentRunNaturality.output_natural hZ1 kind _ _ _ _ _ _ hw1 hFirst
    have hy := OriginalArgumentRunNaturality.input_natural hZ1 kind _ _ _ _ _ _ hw1 hSecond
    have hY := OriginalArgumentRunNaturality.output_natural hZ1 kind _ _ _ _ _ _ hw1 hSecond
    let env : Fin 7 → Fin (m+4) := (Fin.cases (old 4 mode) (Fin.cases (old 4 depth) (Fin.cases (old 4 parameter) (Fin.cases (slot 4 0) (Fin.cases (slot 4 1) (Fin.cases (slot 4 2) (fun _ => (slot 4 3))))))))
    have hn : Derives Δ (environmentNat 7 (old 4 w) env) := by
      apply HornApplicationRules.intro_nat
      intro i
      exact Fin.cases hMode (fun j7 => Fin.cases hDepth (fun j6 => Fin.cases hParam (fun j5 => Fin.cases hx (fun j4 => Fin.cases hy (fun j3 => Fin.cases hX (fun _ => hY) j3) j4) j5) j6) j7) i
    have htMatrix := Derives.impE (.conjR (OriginalFormulaMatrix.binary_at_row hZ1 tag kind (old 4 w) (old 4 n) (old 4 q) (old 4 r) env hw1 hn hc1)) hB
    have hmatrix := Derives.impE (.conjR (HornUniversalTraceRules.matrix_iff (binary tag kind) (old 4 w) (old 4 V) (old 4 r) env hv1)) htMatrix
    have hb := OriginalScalarPositive.head_bound hZ1 (binary tag kind) (OriginalRuleHeadVariables.head_variables (binary tag kind) (OriginalFormulaClasses.selected_mem (binary tag kind) hr)) (old 4 w) (old 4 r) env hw1 hn (.conjL htMatrix)
    have ho := HornApplicationRules.intro_application (binary tag kind) (old 4 w) (old 4 r) (old 4 V) env hn hb hmatrix
    exact of_eq (HornApplicationSyntax.application_rename (binary tag kind) w r V (old 4)).symm ho

theorem nonbinder_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (hr : (unary tag false) ∈ OriginalFormulaClasses.selected)
    (w mode depth parameter n q r V : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornApplicationSyntax.application (unary tag false) w r V).iff (unaryCase tag w mode depth parameter n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := HornApplicationSyntax.application (unary tag false) w r V
    let B := HornApplicationSyntax.body (unary tag false) w r V
    let Δ := Context.add B (raisedContext 5 (Context.add E Γ))
    apply HornApplicationRules.eliminate_application (unary tag false) w r V _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 5 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 5)) := HornBinderRules.under_body 5 (add hp E) B
    have hw1 : Derives Δ (omega (old 5 w)) := of_eq (omega_rename w (old 5)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 (old 5 w) (old 5 mode) (old 5 depth) (old 5 parameter) (old 5 n) (old 5 q) (old 5 r)) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r (old 5)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 5 w) (old 5 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 5)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := Derives.impE (.conjL (HornUniversalTraceRules.matrix_iff (unary tag false) (old 5 w) (old 5 V) (old 5 r) (slot 5) hv1)) (.conjR (.conjR hB))
    have hh := Derives.conjL ht
    rw [OriginalFormulaExpr.actual_unary_head tag false] at hh
    have he := OriginalFormulaRowGraph.metadata_eq hZ1 3 0 1 2 (Expr.node (.literal tag) [.var 3]) (Expr.node (.literal tag) [.var 4]) (old 5 w) (old 5 mode) (old 5 depth) (old 5 parameter) (old 5 n) (old 5 q) (old 5 r) (slot 5) hw1 (.conjL hB) hh hc1
    have hcEnv := OriginalRowMetadataSubstitution.row_fields 3 _ _ _ _ _ _ _ _ _ _ (.conjL he) (.conjL (.conjR he)) (.conjR (.conjR he)) hc1
    have hd := Derives.impE (.conjL (OriginalFormulaMatrix.nonbinder_at_row hZ1 tag (old 5 w) (old 5 n) (old 5 q) (old 5 r) (slot 5) hw1 (.conjL hB) hcEnv)) ht
    have hfix := OriginalFormulaDataSubstitution.unary_metadata tag (old 5 w) (slot 5 0) (slot 5 1) (slot 5 2) (old 5 n) (old 5 q) (slot 5 3) (slot 5 4) (old 5 mode) (old 5 depth) (old 5 parameter) (eq_symm (.conjL he)) (eq_symm (.conjL (.conjR he))) (eq_symm (.conjR (.conjR he))) hd
    have ho := intro_unary tag (old 5 w) (old 5 mode) (old 5 depth) (old 5 parameter) (old 5 n) (old 5 q) (slot 5 3) (slot 5 4) hfix
    exact of_eq (unaryCase_rename tag w mode depth parameter n q (old 5)).symm ho
  · apply Derives.impI
    let E := unaryCase tag w mode depth parameter n q
    let B := unaryBody tag w mode depth parameter n q
    let Δ := Context.add B (raisedContext 2 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 2 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 2)) := HornBinderRules.under_body 2 (add hp E) B
    have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 n) (old 2 q) (old 2 r)) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r (old 2)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 2 w) (old 2 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 2)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hMode := OriginalArgumentsMetadata.field_natural hZ1 3 _ _ _ _ _ _ _ 0 hw1 hc1
    have hDepth := OriginalArgumentsMetadata.field_natural hZ1 3 _ _ _ _ _ _ _ 1 hw1 hc1
    have hParam := OriginalArgumentsMetadata.field_natural hZ1 3 _ _ _ _ _ _ _ 2 hw1 hc1
    have hChild := Derives.conjR hB
    have hx := OriginalArgumentRunNaturality.input_natural hZ1 3 _ _ _ _ _ _ hw1 hChild
    have hX := OriginalArgumentRunNaturality.output_natural hZ1 3 _ _ _ _ _ _ hw1 hChild
    let env : Fin 5 → Fin (m+2) := (Fin.cases (old 2 mode) (Fin.cases (old 2 depth) (Fin.cases (old 2 parameter) (Fin.cases (slot 2 0) (fun _ => (slot 2 1))))))
    have hn : Derives Δ (environmentNat 5 (old 2 w) env) := by
      apply HornApplicationRules.intro_nat
      intro i
      exact Fin.cases hMode (fun j5 => Fin.cases hDepth (fun j4 => Fin.cases hParam (fun j3 => Fin.cases hx (fun _ => hX) j3) j4) j5) i
    have htMatrix := Derives.impE (.conjR (OriginalFormulaMatrix.nonbinder_at_row hZ1 tag (old 2 w) (old 2 n) (old 2 q) (old 2 r) env hw1 hn hc1)) hB
    have hmatrix := Derives.impE (.conjR (HornUniversalTraceRules.matrix_iff (unary tag false) (old 2 w) (old 2 V) (old 2 r) env hv1)) htMatrix
    have hb := OriginalScalarPositive.head_bound hZ1 (unary tag false) (OriginalRuleHeadVariables.head_variables (unary tag false) (OriginalFormulaClasses.selected_mem (unary tag false) hr)) (old 2 w) (old 2 r) env hw1 hn (.conjL htMatrix)
    have ho := HornApplicationRules.intro_application (unary tag false) (old 2 w) (old 2 r) (old 2 V) env hn hb hmatrix
    exact of_eq (HornApplicationSyntax.application_rename (unary tag false) w r V (old 2)).symm ho

theorem application_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w mode depth parameter n q r V : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r V).iff (applicationCase w mode depth parameter n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := HornApplicationSyntax.application (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r V
    let B := HornApplicationSyntax.body (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r V
    let Δ := Context.add B (raisedContext 6 (Context.add E Γ))
    apply HornApplicationRules.eliminate_application (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r V _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 6 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 6)) := HornBinderRules.under_body 6 (add hp E) B
    have hw1 : Derives Δ (omega (old 6 w)) := of_eq (omega_rename w (old 6)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 (old 6 w) (old 6 mode) (old 6 depth) (old 6 parameter) (old 6 n) (old 6 q) (old 6 r)) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r (old 6)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 6 w) (old 6 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 6)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := Derives.impE (.conjL (HornUniversalTraceRules.matrix_iff (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) (old 6 w) (old 6 V) (old 6 r) (slot 6) hv1)) (.conjR (.conjR hB))
    have hh := Derives.conjL ht
    rw [OriginalFormulaExpr.actual_application_head ] at hh
    have he := OriginalFormulaRowGraph.metadata_eq hZ1 3 0 1 2 (OriginalFormulaApplicationSyntax.expr 3 4) (OriginalFormulaApplicationSyntax.expr 3 5) (old 6 w) (old 6 mode) (old 6 depth) (old 6 parameter) (old 6 n) (old 6 q) (old 6 r) (slot 6) hw1 (.conjL hB) hh hc1
    have hcEnv := OriginalRowMetadataSubstitution.row_fields 3 _ _ _ _ _ _ _ _ _ _ (.conjL he) (.conjL (.conjR he)) (.conjR (.conjR he)) hc1
    have hd := Derives.impE (.conjL (OriginalFormulaMatrix.application_at_row hZ1 (old 6 w) (old 6 n) (old 6 q) (old 6 r) (slot 6) hw1 (.conjL hB) hcEnv)) ht
    have hfix := OriginalFormulaDataSubstitution.application_metadata  (old 6 w) (slot 6 0) (slot 6 1) (slot 6 2) (old 6 n) (old 6 q) (slot 6 3) (slot 6 4) (slot 6 5) (old 6 mode) (old 6 depth) (old 6 parameter) (eq_symm (.conjL he)) (eq_symm (.conjL (.conjR he))) (eq_symm (.conjR (.conjR he))) hd
    have ho := intro_application  (old 6 w) (old 6 mode) (old 6 depth) (old 6 parameter) (old 6 n) (old 6 q) (slot 6 3) (slot 6 4) (slot 6 5) hfix
    exact of_eq (applicationCase_rename w mode depth parameter n q (old 6)).symm ho
  · apply Derives.impI
    let E := applicationCase w mode depth parameter n q
    let B := applicationBody  w mode depth parameter n q
    let Δ := Context.add B (raisedContext 3 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 3 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 3 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 3)) := HornBinderRules.under_body 3 (add hp E) B
    have hw1 : Derives Δ (omega (old 3 w)) := of_eq (omega_rename w (old 3)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 (old 3 w) (old 3 mode) (old 3 depth) (old 3 parameter) (old 3 n) (old 3 q) (old 3 r)) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r (old 3)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 3 w) (old 3 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 3)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hMode := OriginalArgumentsMetadata.field_natural hZ1 3 _ _ _ _ _ _ _ 0 hw1 hc1
    have hDepth := OriginalArgumentsMetadata.field_natural hZ1 3 _ _ _ _ _ _ _ 1 hw1 hc1
    have hParam := OriginalArgumentsMetadata.field_natural hZ1 3 _ _ _ _ _ _ _ 2 hw1 hc1
    have hChild := Derives.conjR hB
    have hSymbol := OriginalFormulaApplicationNaturality.symbol_natural _ _ _ _ (.conjL (.conjL hB))
    have hArgs := OriginalArgumentRunNaturality.input_natural hZ1 2 _ _ _ _ _ _ hw1 hChild
    have hNewArgs := OriginalArgumentRunNaturality.output_natural hZ1 2 _ _ _ _ _ _ hw1 hChild
    let env : Fin 6 → Fin (m+3) := (Fin.cases (old 3 mode) (Fin.cases (old 3 depth) (Fin.cases (old 3 parameter) (Fin.cases (slot 3 0) (Fin.cases (slot 3 1) (fun _ => (slot 3 2)))))))
    have hn : Derives Δ (environmentNat 6 (old 3 w) env) := by
      apply HornApplicationRules.intro_nat
      intro i
      exact Fin.cases hMode (fun j6 => Fin.cases hDepth (fun j5 => Fin.cases hParam (fun j4 => Fin.cases hSymbol (fun j3 => Fin.cases hArgs (fun _ => hNewArgs) j3) j4) j5) j6) i
    have htMatrix := Derives.impE (.conjR (OriginalFormulaMatrix.application_at_row hZ1 (old 3 w) (old 3 n) (old 3 q) (old 3 r) env hw1 hn hc1)) hB
    have hmatrix := Derives.impE (.conjR (HornUniversalTraceRules.matrix_iff (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) (old 3 w) (old 3 V) (old 3 r) env hv1)) htMatrix
    have hb := OriginalScalarPositive.head_bound hZ1 (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) (OriginalRuleHeadVariables.head_variables (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) (OriginalFormulaClasses.selected_mem (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) (by simp [OriginalFormulaClasses.selected]))) (old 3 w) (old 3 r) env hw1 hn (.conjL htMatrix)
    have ho := HornApplicationRules.intro_application (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) (old 3 w) (old 3 r) (old 3 V) env hn hb hmatrix
    exact of_eq (HornApplicationSyntax.application_rename (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r V (old 3)).symm ho

end PPAC.Migration.Internal.OriginalFormulaArityApplications
