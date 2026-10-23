import PPAC.Migration.Internal.OriginalArgumentsModeGuard

/-! 原nil/cons完整矩阵与真实数值行/子轨迹的双向对应；候选中间行均对象绑定。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsRuleMatrix
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornUniversalTraceRules
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectSyntaxTransform (nilArguments consArguments rules)

theorem head_child_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env)) :
    Derives Γ ((tracedPremise OriginalArgumentsTraceRules.headPremise w env).iff
      (OriginalTransformRowSyntax.run 1 w (env 0) (env 1) (env 2) (env 3) (env 5))) := by
  apply FormulaCodeCongruence.ex_congr
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hn1 := of_eq (environmentNat_rename 7 w env Fin.castSucc) (Derives.rename Fin.castSucc hn)
  exact FormulaCodeCongruence.conj_congr
    (OriginalArgumentsExpr.head_premise_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1)
    (SyntaxTypeLocalTransfer.iff_refl _)

theorem tail_child_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env)) :
    Derives Γ ((tracedPremise OriginalArgumentsTraceRules.tailPremise w env).iff
      (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 6))) := by
  apply FormulaCodeCongruence.ex_congr
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  have hn1 := of_eq (environmentNat_rename 7 w env Fin.castSucc) (Derives.rename Fin.castSucc hn)
  exact FormulaCodeCongruence.conj_congr
    (OriginalArgumentsExpr.tail_premise_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) (fun i => (env i).castSucc) hw1 hn1)
    (SyntaxTypeLocalTransfer.iff_refl _)

theorem nil_matrix_iff_head {m} {Γ : Context m} (w r : Fin m) (env : Fin 3 → Fin m)
    (hg : Derives Γ (HornRuleSyntax.guards nilArguments.guards w env)) :
    Derives Γ ((tracedMatrix nilArguments w r env).iff (graph nilArguments.head w env r)) := by
  apply Derives.conjI
  · exact .impI (.conjL (.hyp (Or.inl rfl)))
  · exact .impI (.conjI (.hyp (Or.inl rfl)) (.conjI (add hg _) HornRuleSyntax.truth_proved))

theorem cons_matrix_iff_graphs {m} {Γ : Context m} (w r : Fin m) (env : Fin 7 → Fin m) :
    Derives Γ ((tracedMatrix consArguments w r env).iff
      ((graph consArguments.head w env r).conj ((tracedPremise OriginalArgumentsTraceRules.headPremise w env).conj (tracedPremise OriginalArgumentsTraceRules.tailPremise w env)))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hE : Derives (Context.add (tracedMatrix consArguments w r env) Γ) (tracedMatrix consArguments w r env) := .hyp (Or.inl rfl)
    have hp := Derives.conjR (Derives.conjR hE)
    exact .conjI (.conjL hE) (.conjI (.conjL hp) (.conjL (.conjR hp)))
  · apply Derives.impI
    have hE : Derives (Context.add ((graph consArguments.head w env r).conj ((tracedPremise OriginalArgumentsTraceRules.headPremise w env).conj (tracedPremise OriginalArgumentsTraceRules.tailPremise w env))) Γ)
      ((graph consArguments.head w env r).conj ((tracedPremise OriginalArgumentsTraceRules.headPremise w env).conj (tracedPremise OriginalArgumentsTraceRules.tailPremise w env))) := .hyp (Or.inl rfl)
    exact .conjI (.conjL hE) (.conjI HornRuleSyntax.truth_proved (.conjI (.conjL (.conjR hE)) (.conjI (.conjR (.conjR hE)) HornRuleSyntax.truth_proved)))

theorem nil_matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (w n q r : Fin m) (env : Fin 3 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 3 w env))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (env 0)))
    (hN : Derives Γ (StructuralListSyntax.nilCode w n)) (hQ : Derives Γ (StructuralListSyntax.nilCode w q)) :
    Derives Γ ((tracedMatrix nilArguments w r env).iff (OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r)) :=
  SyntaxTypeLocalTransfer.iff_trans (nil_matrix_iff_head w r env (OriginalArgumentsModeGuard.nil_guard hZ three w env hw hn hm))
    (OriginalArgumentsExpr.nil_head_iff hZ w n q r env hw hn hN hQ)

theorem cons_matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n q r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hN : Derives Γ (StructuralListSyntax.consCode w (env 3) (env 4) n))
    (hQ : Derives Γ (StructuralListSyntax.consCode w (env 5) (env 6) q)) :
    Derives Γ ((tracedMatrix consArguments w r env).iff
      ((OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r).conj
        ((OriginalTransformRowSyntax.run 1 w (env 0) (env 1) (env 2) (env 3) (env 5)).conj
          (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 6))))) :=
  SyntaxTypeLocalTransfer.iff_trans (cons_matrix_iff_graphs w r env)
    (FormulaCodeCongruence.conj_congr (OriginalArgumentsExpr.cons_head_iff hZ w n q r env hw hn hN hQ)
      (FormulaCodeCongruence.conj_congr (head_child_iff hZ w env hw hn) (tail_child_iff hZ w env hw hn)))

theorem original_cons_matrix_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w V n q r : Fin m) (env : Fin 7 → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat 7 w env))
    (hv : Derives Γ (HornUniversalTraceSyntax.value w V))
    (hN : Derives Γ (StructuralListSyntax.consCode w (env 3) (env 4) n))
    (hQ : Derives Γ (StructuralListSyntax.consCode w (env 5) (env 6) q)) :
    Derives Γ ((HornRuleSyntax.matrix consArguments w r V env).iff
      ((OriginalTransformRowSyntax.row 2 w (env 0) (env 1) (env 2) n q r).conj
        ((OriginalTransformRowSyntax.run 1 w (env 0) (env 1) (env 2) (env 3) (env 5)).conj
          (OriginalTransformRowSyntax.run 2 w (env 0) (env 1) (env 2) (env 4) (env 6))))) :=
  SyntaxTypeLocalTransfer.iff_trans (HornUniversalTraceRules.matrix_iff consArguments w V r env hv) (cons_matrix_iff hZ w n q r env hw hn hN hQ)

end PPAC.Migration.Internal.OriginalArgumentsRuleMatrix
