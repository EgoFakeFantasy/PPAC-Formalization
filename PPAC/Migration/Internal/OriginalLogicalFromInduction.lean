import PPAC.Migration.Internal.OriginalHistoryFromInduction

/-! 原非量词连接词的完整运行对应，历史比较前提由真实递归图与对象归纳假设实际推导。 -/
namespace PPAC.Migration.Internal.OriginalLogicalFromInduction
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter h R S a b c d n q x : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hmeta : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (hF : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hC : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hi : Derives Γ (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.single 4 false w h R S a b c d n q)) := by
  have hn := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hF))
  have ha := OriginalHistoryFromInduction.from_graph hZ w mode depth parameter h R S a b c d n hw hn hg hi
  exact OriginalLogicalProgram.negation_iff hZ three w mode depth parameter h R S a b c d n q x hw hm hmeta hF hC ha

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (kind : Fin 4)
    (w mode depth parameter h R S a b c d n q x y : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hmeta : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (hF : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hC : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (hi : Derives Γ (OriginalFormulaInductionSyntax.prefixIH w mode depth parameter R S a b c d n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.binary kind w h R S a b c d n q)) := by
  have hn := NaturalOrderBasic.ordinal hZ w n hw (.conjL (FormulaCodeProperties.guards w n a b hF))
  have ha := OriginalHistoryFromInduction.from_graph hZ w mode depth parameter h R S a b c d n hw hn hg hi
  exact OriginalLogicalProgram.binary_iff hZ three kind w mode depth parameter h R S a b c d n q x y hw hm hmeta hF hC ha

end PPAC.Migration.Internal.OriginalLogicalFromInduction
