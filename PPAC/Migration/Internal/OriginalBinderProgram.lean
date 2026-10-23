import PPAC.Migration.Internal.OriginalBinderRunDispatch

/-! 原mode0／3两个量词的整条运行与实际历史程序对应；统一对象归纳前提仍明确保留。 -/
namespace PPAC.Migration.Internal.OriginalBinderProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three universal : Bool)
    (w n mode depth P a b c I J R S h x q : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (OriginalUniformInductionSyntax.allFramesIH three w n))
    (hf : Derives Γ (OriginalOperationFrameSyntax.frame three w mode depth P a b c I J R S))
    (hn : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hc : Derives Γ (SyntaxLogicalSyntax.singleCode (SyntaxLogicalSyntax.quantifierTag universal) w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q).iff
      (FormulaTransformLogicalSyntax.single (SyntaxLogicalSyntax.quantifierTag universal) true w h R S a b a c n q)) := by
  have hm := OriginalOperationFrameSyntax.mode_number three w mode depth P a b c I J R S hf
  have hd := OriginalOperationFrameSyntax.metadata three w mode depth P a b c I J R S hf
  have hDispatch := OriginalBinderRunDispatch.run_iff_quantified hZ three universal w mode depth (OriginalOperationFrameSyntax.parameter three P S) n q x hw hm (.conjL hd) (.conjR hd) hc
  exact SyntaxTypeLocalTransfer.iff_trans hDispatch (OriginalBinderCaseBridge.quantified_iff hZ three universal w n mode depth P a b c I J R S h q hw hi hf hn hg)

end PPAC.Migration.Internal.OriginalBinderProgram
