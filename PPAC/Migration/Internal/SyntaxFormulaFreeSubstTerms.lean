import PPAC.Migration.Internal.SyntaxFormulaFreeSubstUnique
import PPAC.Migration.Internal.SyntaxWeakenFreeTerm

/-! 原列表的实际目标项字段精确决定free变量替换，bound变量保持。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaFreeSubstTerms
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxIdentityMapSyntax (identityCode)
open SyntaxFreeSubstSyntax (codeConversion)
open SyntaxMapCodeSyntax (encoded)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem bound_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w b a c R S r s n q i j : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w b R))
    (hr : Derives Γ (encoded w r b b R)) (hs : Derives Γ (encoded w s a c S))
    (hn : Derives Γ (SyntaxVariableSyntax.code true w i n)) (hq : Derives Γ (SyntaxVariableSyntax.code true w j q)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w r s b a b c n q).iff ((Formula.mem i b).conj (.equal i j))) :=
  SyntaxWeakenFreeTerm.bound_iff hZ w b a c R S r s n q i j hw hR hr hs hn hq

theorem free_field_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w b a c L R S r s n q i j : Fin m) (hw : Derives Γ (omega w))
    (hS : Derives Γ (codeConversion w a c L S))
    (hr : Derives Γ (encoded w r b b R)) (hs : Derives Γ (encoded w s a c S))
    (hn : Derives Γ (SyntaxVariableSyntax.code false w i n)) (hq : Derives Γ (SyntaxVariableSyntax.code false w j q)) :
    Derives Γ ((SyntaxRenameTermSyntax.renamed w r s b a b c n q).iff
      ((Formula.mem i a).conj (StructuralListFieldSyntax.field w L i q))) := by
  have hk : Derives Γ ((SyntaxRenameTermSyntax.renamed w r s b a b c n q).iff
      ((Formula.mem i a).conj (GraphSyntax.edge s i j))) := by
    simpa [SyntaxTermSyntax.limit, SyntaxIndexMapSyntax.selectMap] using
      SyntaxRenameTermKnown.known_iff hZ false w r s b a b c n q i j hw (.conjI (.conjR hr) (.conjR hs)) hn hq
  have he := SyntaxFreeSubstFields.field_at_code hZ w a c L S s i j q hw hS hs hq
  exact SyntaxTypeLocalTransfer.iff_trans hk (SyntaxWeakenFreeTerm.repeat_guard_iff _ _ _ he)

end PPAC.Migration.Internal.SyntaxFormulaFreeSubstTerms
