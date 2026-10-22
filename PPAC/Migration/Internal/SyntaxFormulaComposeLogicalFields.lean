import PPAC.Migration.Internal.SyntaxFormulaComposeAdvanced

/-! 已知两阶段逻辑字段的正式复合：否定/四二元/两量词消费同一内部归纳性质。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaComposeLogicalFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFormulaComposeSyntax SyntaxLogicalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S T U K L r s t u g h a b c d e f n q v x X Z : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f))
    (he : Derives Γ (earlier w n)) (hx : Derives Γ (.mem x n))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hn : Derives Γ (singleCode tag w x n)) (hq : Derives Γ (singleCode tag w X q)) (hv : Derives Γ (singleCode tag w Z v)) : Derives Γ (result w K L a b e f n v) := by
  have hf := Derives.impE (.conjL (SyntaxRenameCodeFields.single_iff hZ tag advance valid w R S a b c d n q x X hw (SyntaxFormulaComposeDiagrams.map_R w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.map_S w R S T U K L r s t u g h a b c d e f hd) hn hq)) h1
  have hs := Derives.impE (.conjL (SyntaxRenameCodeFields.single_iff hZ tag advance valid w T U c d e f q v X Z hw (SyntaxFormulaComposeDiagrams.map_T w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.map_U w R S T U K L r s t u g h a b c d e f hd) hq hv)) h2
  have hc := SyntaxFormulaComposeAdvanced.check hZ advance w n x R S T U K L a b c d e f X Z hw he hx (SyntaxFormulaComposeDiagrams.bound_code w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.free_code w R S T U K L r s t u g h a b c d e f hd) hf hs
  exact .impE (.conjR (SyntaxRenameCodeFields.single_iff hZ tag advance valid w K L a b e f n v x Z hw (SyntaxFormulaComposeDiagrams.map_K w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.map_L w R S T U K L r s t u g h a b c d e f hd) hn hv)) hc

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f))
    (he : Derives Γ (earlier w n)) (hx : Derives Γ (.mem x n)) (hy : Derives Γ (.mem y n))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hn : Derives Γ (binaryCode kind w x y n)) (hq : Derives Γ (binaryCode kind w X Y q)) (hv : Derives Γ (binaryCode kind w Z W v)) : Derives Γ (result w K L a b e f n v) := by
  have hf := Derives.impE (.conjL (SyntaxRenameCodeFields.binary_iff hZ kind w R S a b c d n q x y X Y hw (SyntaxFormulaComposeDiagrams.map_R w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.map_S w R S T U K L r s t u g h a b c d e f hd) hn hq)) h1
  have hs := Derives.impE (.conjL (SyntaxRenameCodeFields.binary_iff hZ kind w T U c d e f q v X Y Z W hw (SyntaxFormulaComposeDiagrams.map_T w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.map_U w R S T U K L r s t u g h a b c d e f hd) hq hv)) h2
  have hx' := child w n x R S T U K L a b c d e f X Z he hx (SyntaxFormulaComposeDiagrams.bound_code w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.free_code w R S T U K L r s t u g h a b c d e f hd) (.conjL hf) (.conjL hs)
  have hy' := child w n y R S T U K L a b c d e f Y W he hy (SyntaxFormulaComposeDiagrams.bound_code w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.free_code w R S T U K L r s t u g h a b c d e f hd) (.conjR hf) (.conjR hs)
  exact .impE (.conjR (SyntaxRenameCodeFields.binary_iff hZ kind w K L a b e f n v x y Z W hw (SyntaxFormulaComposeDiagrams.map_K w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.map_L w R S T U K L r s t u g h a b c d e f hd) hn hv)) (.conjI hx' hy')
end PPAC.Migration.Internal.SyntaxFormulaComposeLogicalFields
