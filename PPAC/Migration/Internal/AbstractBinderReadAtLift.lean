import PPAC.Migration.Internal.AbstractUniformInductionRules
import PPAC.Migration.Internal.OriginalBinderStepSyntax

/-! 真实mode1提升后的子frame直接给出历史读取，无A=C或H=S假设。 -/
namespace PPAC.Migration.Internal.AbstractBinderReadAtLift
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem read_at_lift_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h x X A C K H D : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (AbstractUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) (hd : Derives Γ (successor D depth))
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w R S a b c e A C K H)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode D P x X).iff
      (FormulaTransformHistorySyntax.read w h x K H A b C e X)) := by
  have hp := AbstractUniformInductionRules.binder_prefix hZ w n mode depth P a b c e R S A C K H D hw hi hf hd hl
  have ht := SyntaxCodedMixedBinderTyping.input_of_lifted w R S a b c e A C K H hl
  have hCode := Derives.conjR (Derives.impE (.conjL (FormulaCodeKnownLogical.quantified_iff hZ universal w a b x n A hw hc (.conjL (.conjR ht)))) hn)
  have hx := SyntaxConstructors.child_member hZ 1 (SyntaxLogicalSyntax.quantifierTag universal) w (fun _ => x) n 0 hw hc
  have hRun := OriginalFormulaInductionSyntax.prefixIH_at w mode D P K H A b C e n x X hp hx hCode
  have hOrd := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hn))
  have hRead := OriginalHistoryRead.read_iff_executed hZ w h n x K H A b C e X hw hOrd hx hg
  exact SyntaxTypeLocalTransfer.iff_trans hRun (.conjI (.conjR hRead) (.conjL hRead))

end PPAC.Migration.Internal.AbstractBinderReadAtLift
