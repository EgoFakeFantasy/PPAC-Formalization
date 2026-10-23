import PPAC.Migration.Internal.FormulaTransformExecutionSyntax

/-! 实际内部递归图的逐点算子传输；无需把内部自然数视为外部标准数。 -/
namespace PPAC.Migration.Internal.FormulaTransformRecursionCorrectness
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeCongruence SyntaxTypeLocalTransfer FormulaTransformCongruence
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem history_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f x y : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((OrdinalRecursionSyntax.history FormulaTransformRecursionSyntax.matrix (FormulaTransformRecursionSyntax.one w) f x y).iff
      (OrdinalRecursionSyntax.history SyntaxMixedFormulaRecursionSyntax.matrix (SyntaxMixedFormulaRecursionSyntax.one w) f x y)) := by
  apply ex_congr
  have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hv := FormulaTransformOperatorCorrectness.value_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc x.castSucc (Fin.last m) y.castSucc hw1
  exact conj_congr (iff_refl _) (of_eq (by simp only [FormulaTransformRecursionSyntax.matrix_operator, SyntaxMixedFormulaRecursionSyntax.matrix_operator]; rfl) hv)

theorem equations_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((OrdinalRecursionSyntax.equations FormulaTransformRecursionSyntax.matrix (FormulaTransformRecursionSyntax.one w) f d).iff
      (OrdinalRecursionSyntax.equations SyntaxMixedFormulaRecursionSyntax.matrix (SyntaxMixedFormulaRecursionSyntax.one w) f d)) := by
  apply all_congr
  apply imp_congr (iff_refl _)
  apply all_congr
  apply imp_congr (iff_refl _)
  have hw2 := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  exact history_iff (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) w.castSucc.castSucc f.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) (of_eq (by simp only [omega_rename]) hw2)

theorem graph_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((FormulaTransformRecursionSyntax.graph w f d).iff (SyntaxMixedFormulaRecursionSyntax.graph w f d)) :=
  conj_congr (iff_refl _) (equations_iff hZ w f d hw)

theorem evaluation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n v : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((FormulaTransformEvaluationSyntax.evaluation w n v).iff (SyntaxMixedFormulaEvaluationSyntax.evaluation w n v)) := by
  apply ex_congr
  apply ex_congr
  have hw2 := Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  exact conj_congr (iff_refl _) (conj_congr
    (graph_iff (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) w.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc
      (of_eq (by simp only [omega_rename]) hw2)) (iff_refl _))

theorem execution_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((FormulaTransformExecutionSyntax.executed w R S a b c d n q).iff (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)) := by
  apply conj_congr (iff_refl _)
  apply ex_congr
  have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  exact conj_congr (evaluation_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc n.castSucc (Fin.last m) hw1) (iff_refl _)

theorem graph_unique_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d f : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((OrdinalRecursionExistenceSyntax.uniqueAt FormulaTransformRecursionSyntax.matrix (FormulaTransformRecursionSyntax.one w) d f).iff
      (OrdinalRecursionExistenceSyntax.uniqueAt SyntaxMixedFormulaRecursionSyntax.matrix (SyntaxMixedFormulaRecursionSyntax.one w) d f)) := by
  apply all_congr
  have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  exact imp_congr (graph_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) d.castSucc hw1) (iff_refl _)

theorem graph_fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((OrdinalRecursionExistenceSyntax.fiber FormulaTransformRecursionSyntax.matrix (FormulaTransformRecursionSyntax.one w) d).iff
      (OrdinalRecursionExistenceSyntax.fiber SyntaxMixedFormulaRecursionSyntax.matrix (SyntaxMixedFormulaRecursionSyntax.one w) d)) := by
  apply ex_congr
  have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  exact conj_congr (graph_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) d.castSucc hw1)
    (graph_unique_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc d.castSucc (Fin.last m) hw1)

theorem recursors_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) :
    Derives Γ ((FormulaTransformRecursionSyntax.recursors w).iff (SyntaxMixedFormulaRecursionSyntax.recursors w)) := by
  apply all_congr
  have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  exact imp_congr (iff_refl _) (graph_fiber_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) hw1)

theorem actual_recursors {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (FormulaTransformRecursionSyntax.recursors w) :=
  .impE (.conjR (recursors_iff hZ w hw)) (SyntaxMixedFormulaRecursors.all_unique hZ w)

theorem graph_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (OrdinalSyntax.ordinal d)) :
    Derives Γ (FormulaTransformRecursionSyntax.graphExists w d) := by
  have he : Derives Γ ((FormulaTransformRecursionSyntax.graphExists w d).iff (SyntaxMixedFormulaRecursionSyntax.graphExists w d)) := by
    apply ex_congr
    have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
    exact graph_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) d.castSucc hw1
  exact .impE (.conjR he) (SyntaxMixedFormulaRecursors.exists_graph hZ w d hd)

theorem evaluation_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) :
    Derives Γ (FormulaTransformEvaluationSyntax.existsValue w n) := by
  have he : Derives Γ ((FormulaTransformEvaluationSyntax.existsValue w n).iff (SyntaxMixedFormulaEvaluationSyntax.existsValue w n)) := by
    apply ex_congr
    have hw1 : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
    exact evaluation_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc n.castSucc (Fin.last m) hw1
  exact .impE (.conjR he) (SyntaxMixedFormulaEvaluationExistence.at_natural hZ w n hw hn)

end PPAC.Migration.Internal.FormulaTransformRecursionCorrectness
