import PPAC.Migration.Internal.SyntaxFormulaFreeSubstUnique
import PPAC.Migration.Internal.SyntaxRenameKnownFields

/-! 全内部原项列表参数的free替换在两个常量和两个原子构造上的精确端点律。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaFreeSubstAtoms
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxIdentityMapSyntax (identityCode)
open SyntaxFreeSubstSyntax (codeConversion)
open SyntaxMapCodeSyntax (encoded)
open SyntaxFormulaFreeSubstSyntax (substituted)
open SyntaxRenameKnownFieldsSyntax (equalOperands memberOperands)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w b a c L n q R S r s : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w b R)) (hS : Derives Γ (codeConversion w a c L S))
    (hr : Derives Γ (encoded w r b b R)) (hs : Derives Γ (encoded w s a c S))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ ((substituted w b a c L n q).iff (.equal n q)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L n q R S hw hR hS)
    (SyntaxRenameKnownFields.nullary_iff hZ truth w R S r s b a b c n q hw hr hs hc)

theorem equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w b a c L n q R S r s x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w b R)) (hS : Derives Γ (codeConversion w a c L S))
    (hr : Derives Γ (encoded w r b b R)) (hs : Derives Γ (encoded w s a c S))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) (hd : Derives Γ (SyntaxAtomSyntax.equalCode w X Y q)) :
    Derives Γ ((substituted w b a c L n q).iff (equalOperands w r s b a b c x y X Y)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L n q R S hw hR hS)
    (SyntaxRenameKnownFields.equality_iff hZ w R S r s b a b c n q x y X Y hw hr hs hc hd)

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w b a c L n q R S r s z Z x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w b R)) (hS : Derives Γ (codeConversion w a c L S))
    (hr : Derives Γ (encoded w r b b R)) (hs : Derives Γ (encoded w s a c S))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) (hd : Derives Γ (SyntaxAtomSyntax.memberCode w Z X Y q)) :
    Derives Γ ((substituted w b a c L n q).iff (memberOperands w r s b a b c z Z x y X Y)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L n q R S hw hR hS)
    (SyntaxRenameKnownFields.membership_iff hZ w R S r s b a b c n q z Z x y X Y hw hr hs hc hd)
end PPAC.Migration.Internal.SyntaxFormulaFreeSubstAtoms
