import PPAC.Migration.Internal.OriginalLogicalRunDispatch

/-! 原mode0／3完整非量词连接词运行与实际历史程序；内部归纳比较守卫待后续归纳实际消去。 -/
namespace PPAC.Migration.Internal.OriginalLogicalProgram
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter h R S a b c d n q x : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hmeta : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (hF : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hC : Derives Γ (SyntaxLogicalSyntax.singleCode 4 w x n))
    (ha : Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.single 4 false w h R S a b c d n q)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (OriginalLogicalRunDispatch.run_iff_negation hZ three w mode depth parameter n q x hw hm (.conjL hmeta) (.conjR hmeta) hC)
    (OriginalLogicalCaseBridge.negation_iff hZ w mode depth parameter h R S a b c d n q hw hF ha)

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (kind : Fin 4)
    (w mode depth parameter h R S a b c d n q x y : Fin m)
    (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hmeta : Derives Γ (OriginalTermTraceSyntax.metadata w depth parameter))
    (hF : Derives Γ (FormulaCodeSyntax.formulaCode w n a b))
    (hC : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n))
    (ha : Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter n q).iff (FormulaTransformLogicalSyntax.binary kind w h R S a b c d n q)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (OriginalLogicalRunDispatch.run_iff_binary hZ three kind w mode depth parameter n q x y hw hm (.conjL hmeta) (.conjR hmeta) hC)
    (OriginalLogicalCaseBridge.binary_iff hZ kind w mode depth parameter h R S a b c d n q hw hF ha)

end PPAC.Migration.Internal.OriginalLogicalProgram
