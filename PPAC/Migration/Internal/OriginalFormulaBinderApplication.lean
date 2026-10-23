import PPAC.Migration.Internal.OriginalFormulaArityApplications

/-! 原量词arity=5实际赋值消去；后继深度见证保持对象存在量词。 -/
namespace PPAC.Migration.Internal.OriginalFormulaBinderApplication
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax OriginalFormulaCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Expr)
open YesMetaZFC.Automation.ObjectSyntaxTransform (unary)

theorem at_successor_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (hr : (unary tag true) ∈ OriginalFormulaClasses.selected)
    (w mode depth parameter n q r V childDepth : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V))
    (hs : Derives Γ (successor childDepth depth)) :
    Derives Γ ((HornApplicationSyntax.application (unary tag true) w r V).iff (unaryCase tag w mode childDepth parameter n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := HornApplicationSyntax.application (unary tag true) w r V
    let B := HornApplicationSyntax.body (unary tag true) w r V
    let Δ := Context.add B (raisedContext 5 (Context.add E Γ))
    apply HornApplicationRules.eliminate_application (unary tag true) w r V _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 5 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 5)) := HornBinderRules.under_body 5 (add hp E) B
    have hw1 : Derives Δ (omega (old 5 w)) := of_eq (omega_rename w (old 5)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 (old 5 w) (old 5 mode) (old 5 depth) (old 5 parameter) (old 5 n) (old 5 q) (old 5 r)) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r (old 5)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 5 w) (old 5 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 5)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := Derives.impE (.conjL (HornUniversalTraceRules.matrix_iff (unary tag true) (old 5 w) (old 5 V) (old 5 r) (slot 5) hv1)) (.conjR (.conjR hB))
    have hh := Derives.conjL ht
    rw [OriginalFormulaExpr.actual_unary_head tag true] at hh
    have he := OriginalFormulaRowGraph.metadata_eq hZ1 3 0 1 2 (Expr.node (.literal tag) [.var 3]) (Expr.node (.literal tag) [.var 4]) (old 5 w) (old 5 mode) (old 5 depth) (old 5 parameter) (old 5 n) (old 5 q) (old 5 r) (slot 5) hw1 (.conjL hB) hh hc1
    have hcEnv := OriginalRowMetadataSubstitution.row_fields 3 _ _ _ _ _ _ _ _ _ _ (.conjL he) (.conjL (.conjR he)) (.conjR (.conjR he)) hc1
    have hs1 : Derives Δ (successor (old 5 childDepth) (old 5 depth)) := of_eq (successor_rename childDepth depth (old 5)) (lift hs)
    have hsEnv := FreeWeakenValueSyntax.successor_input_subst (old 5 childDepth) (old 5 depth) (slot 5 1) (.conjL (.conjR he)) hs1
    have hd := Derives.impE (.conjL (OriginalFormulaMatrix.binder_at_row hZ1 tag (old 5 w) (old 5 n) (old 5 q) (old 5 r) (old 5 childDepth) (slot 5) hw1 (.conjL hB) hcEnv hsEnv)) ht
    have hfix := OriginalFormulaDataSubstitution.unary_metadata tag (old 5 w) (slot 5 0) (old 5 childDepth) (slot 5 2) (old 5 n) (old 5 q) (slot 5 3) (slot 5 4) (old 5 mode) (old 5 childDepth) (old 5 parameter) (eq_symm (.conjL he)) (.eqRefl (old 5 childDepth)) (eq_symm (.conjR (.conjR he))) hd
    have ho := intro_unary tag (old 5 w) (old 5 mode) (old 5 childDepth) (old 5 parameter) (old 5 n) (old 5 q) (slot 5 3) (slot 5 4) hfix
    exact of_eq (unaryCase_rename tag w mode childDepth parameter n q (old 5)).symm ho
  · apply Derives.impI
    let E := unaryCase tag w mode childDepth parameter n q
    let B := unaryBody tag w mode childDepth parameter n q
    let Δ := Context.add B (raisedContext 2 (Context.add E Γ))
    apply HornBinderRules.eliminate_many 2 B _ (.hyp (Or.inl rfl))
    have hZ1 := HornBinderRules.zf_body 2 (ZFContext.add hZ E) B
    have lift {p : Formula m} (hp : Derives Γ p) : Derives Δ (p.rename (old 2)) := HornBinderRules.under_body 2 (add hp E) B
    have hw1 : Derives Δ (omega (old 2 w)) := of_eq (omega_rename w (old 2)) (lift hw)
    have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 (old 2 w) (old 2 mode) (old 2 depth) (old 2 parameter) (old 2 n) (old 2 q) (old 2 r)) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r (old 2)) (lift hc)
    have hv1 : Derives Δ (HornUniversalTraceSyntax.value (old 2 w) (old 2 V)) := of_eq (HornUniversalTraceSyntax.value_rename w V (old 2)) (lift hv)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs2 : Derives Δ (successor (old 2 childDepth) (old 2 depth)) := of_eq (successor_rename childDepth depth (old 2)) (lift hs)
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
    have htMatrix := Derives.impE (.conjR (OriginalFormulaMatrix.binder_at_row hZ1 tag (old 2 w) (old 2 n) (old 2 q) (old 2 r) (old 2 childDepth) env hw1 hn hc1 hs2)) hB
    have hmatrix := Derives.impE (.conjR (HornUniversalTraceRules.matrix_iff (unary tag true) (old 2 w) (old 2 V) (old 2 r) env hv1)) htMatrix
    have hb := OriginalScalarPositive.head_bound hZ1 (unary tag true) (OriginalRuleHeadVariables.head_variables (unary tag true) (OriginalFormulaClasses.selected_mem (unary tag true) hr)) (old 2 w) (old 2 r) env hw1 hn (.conjL htMatrix)
    have ho := HornApplicationRules.intro_application (unary tag true) (old 2 w) (old 2 r) (old 2 V) env hn hb hmatrix
    exact of_eq (HornApplicationSyntax.application_rename (unary tag true) w r V (old 2)).symm ho

theorem application_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat)
    (hr : (unary tag true) ∈ OriginalFormulaClasses.selected) (w mode depth parameter n q r V : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w mode depth parameter n q r))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V)) :
    Derives Γ ((HornApplicationSyntax.application (unary tag true) w r V).iff (binderCase tag w mode depth parameter n q)) := by
  have he := InsertExistence.exists_insert depth depth (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let S := successor (Fin.last m) depth.castSucc
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) he
  have hZ1 := ZFContext.under hZ S
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hc1 : Derives Δ (OriginalTransformRowSyntax.row 3 w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc q.castSucc r.castSucc) := of_eq (OriginalTransformRowSyntax.row_rename 3 w mode depth parameter n q r Fin.castSucc) (under hc S)
  have hv1 : Derives Δ (HornUniversalTraceSyntax.value w.castSucc V.castSucc) := of_eq (HornUniversalTraceSyntax.value_rename w V Fin.castSucc) (under hv S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have ha := at_successor_iff hZ1 tag hr w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc q.castSucc r.castSucc V.castSucc (Fin.last m) hw1 hc1 hv1 hS
  have hb := OriginalFormulaBinderDepth.case_at_successor hZ1 tag w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc q.castSucc (Fin.last m) hS
  have ho := SyntaxTypeLocalTransfer.iff_trans ha (Derives.conjI (.conjR hb) (.conjL hb))
  simpa only [Formula.raise, Formula.iff, Formula.rename, HornApplicationSyntax.application_rename, binderCase_rename] using ho

end PPAC.Migration.Internal.OriginalFormulaBinderApplication
