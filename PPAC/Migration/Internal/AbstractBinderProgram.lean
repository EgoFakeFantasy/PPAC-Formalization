import PPAC.Migration.Internal.AbstractBinderCaseBridge
import PPAC.Migration.Internal.SmallModeLogicalDispatch

/-! 实际mode1两个量词的整条运行与实际历史程序对应；统一对象归纳前提仍明确保留。 -/
namespace PPAC.Migration.Internal.AbstractBinderProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w n mode depth P a b c e R S h x q : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (AbstractUniformInductionSyntax.allFramesIH w n))
    (hf : Derives Γ (AbstractOperationFrameSyntax.frame w mode depth P a b c e R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth P n q).iff
      (FormulaTransformLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b c e n q)) := by
  have hm := AbstractOperationFrameSyntax.mode_number w mode depth P a b c e R S hf
  have hd := AbstractOperationFrameSyntax.metadata w mode depth P a b c e R S hf
  have hDispatch := SmallModeLogicalDispatch.run_iff_quantified hZ 1 (by decide) universal w mode depth P n q x hw hm (.conjL hd) (.conjR hd) hc
  exact SyntaxTypeLocalTransfer.iff_trans hDispatch (AbstractBinderCaseBridge.quantified_iff hZ universal w n mode depth P a b c e R S h q hw hi hf hn hg)

end PPAC.Migration.Internal.AbstractBinderProgram
