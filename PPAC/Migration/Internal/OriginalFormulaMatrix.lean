import PPAC.Migration.Internal.OriginalFormulaLocalData

/-! 全十一原公式局部矩阵与纯数值head／真实子运行精确对应；原常量模式守卫实际消去。 -/
namespace PPAC.Migration.Internal.OriginalFormulaMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornUniversalTraceRules
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (constant binary unary nilArguments)

theorem constant_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (tag : Nat) (w : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0))) :
    Derives Γ (HornRuleSyntax.guards (constant tag).guards w env) := OriginalArgumentsModeGuard.nil_guard hZ three w env hw hn hm

theorem constant_matrix_iff_head {m} {Γ : Context m} (tag : Nat) (w r : Fin m) (env : Fin 3 → Fin m)
    (hg : Derives Γ (HornRuleSyntax.guards (constant tag).guards w env)) :
    Derives Γ ((tracedMatrix (constant tag) w r env).iff (graph (constant tag).head w env r)) := by
  apply Derives.conjI
  · exact .impI (.conjL (.hyp (Or.inl rfl)))
  · exact .impI (.conjI (.hyp (Or.inl rfl)) (.conjI (add hg _) HornRuleSyntax.truth_proved))

theorem binary_matrix_iff_graphs {m} {Γ : Context m} (tag kind : Nat) (w r : Fin m) (env : Fin 7 → Fin m) :
    Derives Γ ((tracedMatrix (binary tag kind) w r env).iff
      ((graph (binary tag kind).head w env r).conj ((tracedPremise (OriginalFormulaExpr.binaryLeft kind) w env).conj (tracedPremise (OriginalFormulaExpr.binaryRight kind) w env)))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hE : Derives (Context.add (tracedMatrix (binary tag kind) w r env) Γ) (tracedMatrix (binary tag kind) w r env) := .hyp (Or.inl rfl)
    have hp := Derives.conjR (Derives.conjR hE)
    exact .conjI (.conjL hE) (.conjI (.conjL hp) (.conjL (.conjR hp)))
  · apply Derives.impI
    have hE : Derives (Context.add ((graph (binary tag kind).head w env r).conj ((tracedPremise (OriginalFormulaExpr.binaryLeft kind) w env).conj (tracedPremise (OriginalFormulaExpr.binaryRight kind) w env))) Γ)
      ((graph (binary tag kind).head w env r).conj ((tracedPremise (OriginalFormulaExpr.binaryLeft kind) w env).conj (tracedPremise (OriginalFormulaExpr.binaryRight kind) w env))) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hE) (.conjI HornRuleSyntax.truth_proved (.conjI (.conjL (.conjR hE)) (.conjI (.conjR (.conjR hE)) HornRuleSyntax.truth_proved)))

theorem unary_matrix_iff_graphs {m} {Γ : Context m} (tag : Nat) (binder : Bool) (w r : Fin m) (env : Fin 5 → Fin m) :
    Derives Γ ((tracedMatrix (unary tag binder) w r env).iff ((graph (unary tag binder).head w env r).conj (tracedPremise (OriginalFormulaExpr.unaryChild binder) w env))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hE : Derives (Context.add (tracedMatrix (unary tag binder) w r env) Γ) (tracedMatrix (unary tag binder) w r env) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hE) (.conjL (.conjR (.conjR hE)))
  · apply Derives.impI
    have hE : Derives (Context.add ((graph (unary tag binder).head w env r).conj (tracedPremise (OriginalFormulaExpr.unaryChild binder) w env)) Γ)
      ((graph (unary tag binder).head w env r).conj (tracedPremise (OriginalFormulaExpr.unaryChild binder) w env)) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hE) (.conjI HornRuleSyntax.truth_proved (.conjI (.conjR hE) HornRuleSyntax.truth_proved))

theorem application_matrix_iff_graphs {m} {Γ : Context m} (w r : Fin m) (env : Fin 6 → Fin m) :
    Derives Γ ((tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r env).iff
      ((graph (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3).head w env r).conj (tracedPremise OriginalFormulaExpr.applicationChild w env))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hE : Derives (Context.add (tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r env) Γ) (tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r env) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hE) (.conjL (.conjR (.conjR hE)))
  · apply Derives.impI
    have hE : Derives (Context.add ((graph (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3).head w env r).conj (tracedPremise OriginalFormulaExpr.applicationChild w env)) Γ)
      ((graph (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3).head w env r).conj (tracedPremise OriginalFormulaExpr.applicationChild w env)) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hE) (.conjI HornRuleSyntax.truth_proved (.conjI (.conjR hE) HornRuleSyntax.truth_proved))

theorem constant_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (tag : Nat) (w n q r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((tracedMatrix (constant tag) w r env).iff (OriginalFormulaLocalData.constant tag w n q)) :=
  SyntaxTypeLocalTransfer.iff_trans (constant_matrix_iff_head tag w r env (constant_guard hZ three tag w env hw hn hm))
    (OriginalFormulaExpr.constant_at_row hZ tag w n q r env hw hn hc)

theorem binary_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag kind : Nat) (w n q r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((tracedMatrix (binary tag kind) w r env).iff (OriginalFormulaLocalData.binary tag kind w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5) (env 6))) :=
  SyntaxTypeLocalTransfer.iff_trans (binary_matrix_iff_graphs tag kind w r env)
    (FormulaCodeCongruence.conj_congr (OriginalFormulaExpr.binary_at_row hZ tag kind w n q r env hw hn hc)
      (FormulaCodeCongruence.conj_congr (OriginalFormulaChildren.binary_left_iff hZ kind w env hw hn) (OriginalFormulaChildren.binary_right_iff hZ kind w env hw hn)))

theorem nonbinder_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w n q r : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((tracedMatrix (unary tag false) w r env).iff (OriginalFormulaLocalData.unary tag w (env 0) (env 1) (env 2) n q (env 3) (env 4))) :=
  SyntaxTypeLocalTransfer.iff_trans (unary_matrix_iff_graphs tag false w r env)
    (FormulaCodeCongruence.conj_congr (OriginalFormulaExpr.unary_at_row hZ tag false w n q r env hw hn hc) (OriginalFormulaChildren.nonbinder_child_iff hZ w env hw hn))

theorem binder_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w n q r childDepth : Fin m) (env : Fin 5 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 5 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r))
    (hs : Derives Γ (successor childDepth (env 1))) :
    Derives Γ ((tracedMatrix (unary tag true) w r env).iff (OriginalFormulaLocalData.unary tag w (env 0) childDepth (env 2) n q (env 3) (env 4))) :=
  SyntaxTypeLocalTransfer.iff_trans (unary_matrix_iff_graphs tag true w r env)
    (FormulaCodeCongruence.conj_congr (OriginalFormulaExpr.unary_at_row hZ tag true w n q r env hw hn hc) (OriginalFormulaChildren.binder_child_iff hZ w childDepth env hw hn hs))

theorem application_at_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n q r : Fin m) (env : Fin 6 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 6 w env))
    (hc : Derives Γ (OriginalTransformRowSyntax.row 3 w (env 0) (env 1) (env 2) n q r)) :
    Derives Γ ((tracedMatrix (YesMetaZFC.Automation.ObjectSyntaxTransform.application 3) w r env).iff (OriginalFormulaLocalData.application w (env 0) (env 1) (env 2) n q (env 3) (env 4) (env 5))) :=
  SyntaxTypeLocalTransfer.iff_trans (application_matrix_iff_graphs w r env)
    (FormulaCodeCongruence.conj_congr (OriginalFormulaExpr.application_at_row hZ w n q r env hw hn hc) (OriginalFormulaChildren.application_child_iff hZ w env hw hn))

end PPAC.Migration.Internal.OriginalFormulaMatrix
