import PPAC.Migration.Internal.OriginalBinderStepSyntax

/-! 真实量词提升点上，统一对象归纳实际给出原始子运行与实际历史read的精确对应。 -/
namespace PPAC.Migration.Internal.OriginalBinderReadAtLift
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem aligned_execution_iff {m} {Γ : Context m} (w K S H A b C c x X : Fin m)
    (ha : Derives Γ (.equal A C)) (hs : Derives Γ (.equal H S)) :
    Derives Γ ((FormulaTransformExecutionSyntax.executed w K S A b A c x X).iff
      (FormulaTransformExecutionSyntax.executed w K H A b C c x X)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact FreeSubstProgramBinder.execution_subst_free w K S A b C c x X H (add (eq_symm hs) _)
      (FreeSubstProgramBinder.execution_subst_bound w K S A b A c x X C (add ha _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact FreeSubstProgramBinder.execution_subst_bound w K S A b C c x X A (add (eq_symm ha) _)
      (FreeSubstProgramBinder.execution_subst_free w K H A b C c x X S (add hs _) (.hyp (Or.inl rfl)))

theorem read_at_lift_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three universal : Bool)
    (w n mode depth P a b c I J R S h x X A C K H D : Fin m)
    (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hd : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b a c A C K H)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode D (OriginalOperationFrameSyntax.parameter three P S) x X).iff
      (FormulaTransformHistorySyntax.read w h x K H A b C c X)) := by
  have hh := OriginalUniformInductionRules.binder_prefix hZ three w n mode depth P a b c I J R S A C K H D hw hi hf hd hl
  have ht := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b a c A C K H hl
  have hCode := Derives.conjR (Derives.impE (.conjL (FormulaCodeKnownLogical.quantified_iff hZ universal w a b x n A hw hc (.conjL (.conjR ht)))) hn)
  have hx := SyntaxConstructors.child_member hZ 1 (SyntaxLogicalSyntax.quantifierTag universal) w (fun _ => x) n 0 hw hc
  have hRun := OriginalFormulaInductionSyntax.prefixIH_at w mode D (OriginalOperationFrameSyntax.parameter three P S) K S A b A c n x X (.conjR (.conjR hh)) hx hCode
  have hAlign := aligned_execution_iff w K S H A b C c x X (.conjL hh) (.conjL (.conjR hh))
  have hOrd := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hn))
  have hRead := OriginalHistoryRead.read_iff_executed hZ w h n x K H A b C c X hw hOrd hx hg
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans hRun hAlign) (.conjI (.conjR hRead) (.conjL hRead))

end PPAC.Migration.Internal.OriginalBinderReadAtLift
