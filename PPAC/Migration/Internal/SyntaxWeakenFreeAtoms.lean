import PPAC.Migration.Internal.SyntaxWeakenFreeUnique
import PPAC.Migration.Internal.SyntaxRenameKnownFields

/-! 全内部 free 头槽弱化在原两个常量及两个原子构造上的精确双条件。 -/
namespace PPAC.Migration.Internal.SyntaxWeakenFreeAtoms
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxIdentityMapSyntax (identityCode)
open SyntaxFreeShiftSyntax (shiftCode)
open SyntaxMapCodeSyntax (encoded)
open SyntaxWeakenFreeSyntax (weakened)
open SyntaxRenameKnownFieldsSyntax (equalOperands memberOperands)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem nullary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (truth : Bool)
    (w a b B n q R S r s : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w a R)) (hS : Derives Γ (shiftCode w b B S))
    (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b B S))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 0 (SyntaxAtomSyntax.nullaryTag truth) w Fin.elim0 n)) :
    Derives Γ ((weakened w a b B n q).iff (.equal n q)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B n q R S hw hR hS)
    (SyntaxRenameKnownFields.nullary_iff hZ truth w R S r s a b a B n q hw hr hs hc)

theorem equality_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B n q R S r s x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w a R)) (hS : Derives Γ (shiftCode w b B S))
    (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b B S))
    (hc : Derives Γ (SyntaxAtomSyntax.equalCode w x y n)) (hd : Derives Γ (SyntaxAtomSyntax.equalCode w X Y q)) :
    Derives Γ ((weakened w a b B n q).iff (equalOperands w r s a b a B x y X Y)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B n q R S hw hR hS)
    (SyntaxRenameKnownFields.equality_iff hZ w R S r s a b a B n q x y X Y hw hr hs hc hd)

theorem membership_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B n q R S r s z Z x y X Y : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w a R)) (hS : Derives Γ (shiftCode w b B S))
    (hr : Derives Γ (encoded w r a a R)) (hs : Derives Γ (encoded w s b B S))
    (hc : Derives Γ (SyntaxAtomSyntax.memberCode w z x y n)) (hd : Derives Γ (SyntaxAtomSyntax.memberCode w Z X Y q)) :
    Derives Γ ((weakened w a b B n q).iff (memberOperands w r s a b a B z Z x y X Y)) :=
  SyntaxTypeLocalTransfer.iff_trans
    (SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B n q R S hw hR hS)
    (SyntaxRenameKnownFields.membership_iff hZ w R S r s a b a B n q z Z x y X Y hw hr hs hc hd)
end PPAC.Migration.Internal.SyntaxWeakenFreeAtoms
