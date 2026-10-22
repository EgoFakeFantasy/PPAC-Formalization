import PPAC.Migration.Internal.SyntaxFormulaComposeBinders

/-! 给定两阶段实际构造字段的四原子复合；成员式显式保留原零符号及两段符号相等。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaComposeAtomFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFormulaComposeSyntax
open SyntaxAtomSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool) (w R S T U K L r s t u g h a b c d e f n q v : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (nullaryTag truth) w Fin.elim0 n)) : Derives Γ (result w K L a b e f n v) := by
  have hEq := Derives.impE (.conjL (SyntaxRenameKnownFields.nullary_iff hZ truth w R S r s a b c d n q hw (SyntaxFormulaComposeDiagrams.encoded_r w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_s w R S T U K L r s t u g h a b c d e f hd) hc)) h1
  have hn := SyntaxRenameJudgmentSubst.subst_n w T U c d e f q v n (eq_symm hEq) h2
  have hv := Derives.impE (.conjL (SyntaxRenameKnownFields.nullary_iff hZ truth w T U t u c d e f n v hw (SyntaxFormulaComposeDiagrams.encoded_t w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_u w R S T U K L r s t u g h a b c d e f hd) hc)) hn
  exact .impE (.conjR (SyntaxRenameKnownFields.nullary_iff hZ truth w K L g h a b e f n v hw (SyntaxFormulaComposeDiagrams.encoded_g w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_h w R S T U K L r s t u g h a b c d e f hd) hc)) hv

theorem equality {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S T U K L r s t u g h a b c d e f n q v x y X Y Z W : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hn : Derives Γ (equalCode w x y n)) (hq : Derives Γ (equalCode w X Y q)) (hv : Derives Γ (equalCode w Z W v)) : Derives Γ (result w K L a b e f n v) := by
  have hf := Derives.impE (.conjL (SyntaxRenameKnownFields.equality_iff hZ w R S r s a b c d n q x y X Y hw (SyntaxFormulaComposeDiagrams.encoded_r w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_s w R S T U K L r s t u g h a b c d e f hd) hn hq)) h1
  have hs := Derives.impE (.conjL (SyntaxRenameKnownFields.equality_iff hZ w T U t u c d e f q v X Y Z W hw (SyntaxFormulaComposeDiagrams.encoded_t w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_u w R S T U K L r s t u g h a b c d e f hd) hq hv)) h2
  have hx := SyntaxComposeTerms.forward hZ w r s t u g h a b c d e f x X Z hw (SyntaxFormulaComposeDiagrams.bound w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.free w R S T U K L r s t u g h a b c d e f hd) (.conjL (hf)) (.conjL (hs))
  have hy := SyntaxComposeTerms.forward hZ w r s t u g h a b c d e f y Y W hw (SyntaxFormulaComposeDiagrams.bound w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.free w R S T U K L r s t u g h a b c d e f hd) (.conjR (hf)) (.conjR (hs))
  exact .impE (.conjR (SyntaxRenameKnownFields.equality_iff hZ w K L g h a b e f n v x y Z W hw (SyntaxFormulaComposeDiagrams.encoded_g w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_h w R S T U K L r s t u g h a b c d e f hd) hn hv)) (.conjI hx hy)

theorem membership {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R S T U K L r s t u g h a b c d e f n q v z z1 z2 x y X Y Z W : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (SyntaxFormulaComposeDiagrams.diagrams w R S T U K L r s t u g h a b c d e f))
    (h1 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (h2 : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w T U c d e f q v))
    (hn : Derives Γ (memberCode w z x y n)) (hq : Derives Γ (memberCode w z1 X Y q)) (hv : Derives Γ (memberCode w z2 Z W v)) : Derives Γ (result w K L a b e f n v) := by
  have hf := Derives.impE (.conjL (SyntaxRenameKnownFields.membership_iff hZ w R S r s a b c d n q z z1 x y X Y hw (SyntaxFormulaComposeDiagrams.encoded_r w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_s w R S T U K L r s t u g h a b c d e f hd) hn hq)) h1
  have hs := Derives.impE (.conjL (SyntaxRenameKnownFields.membership_iff hZ w T U t u c d e f q v z1 z2 X Y Z W hw (SyntaxFormulaComposeDiagrams.encoded_t w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_u w R S T U K L r s t u g h a b c d e f hd) hq hv)) h2
  have hx := SyntaxComposeTerms.forward hZ w r s t u g h a b c d e f x X Z hw (SyntaxFormulaComposeDiagrams.bound w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.free w R S T U K L r s t u g h a b c d e f hd) (.conjL (.conjR (.conjR hf))) (.conjL (.conjR (.conjR hs)))
  have hy := SyntaxComposeTerms.forward hZ w r s t u g h a b c d e f y Y W hw (SyntaxFormulaComposeDiagrams.bound w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.free w R S T U K L r s t u g h a b c d e f hd) (.conjR (.conjR (.conjR hf))) (.conjR (.conjR (.conjR hs)))
  exact .impE (.conjR (SyntaxRenameKnownFields.membership_iff hZ w K L g h a b e f n v z z2 x y Z W hw (SyntaxFormulaComposeDiagrams.encoded_g w R S T U K L r s t u g h a b c d e f hd) (SyntaxFormulaComposeDiagrams.encoded_h w R S T U K L r s t u g h a b c d e f hd) hn hv)) (.conjI (.conjL hf) (.conjI (eq_trans (.conjL (.conjR hf)) (.conjL (.conjR hs))) (.conjI hx hy)))
end PPAC.Migration.Internal.SyntaxFormulaComposeAtomFields
