import PPAC.Migration.Internal.SyntaxWeakenFreeUnique
import PPAC.Migration.Internal.SyntaxWeakenFreeLift
import PPAC.Migration.Internal.SyntaxRenameCodeFields
import PPAC.Migration.Internal.FormulaCodeCongruence

/-! 自由头槽弱化的逻辑构造子精确双条件，量词保留实际后继域与任意恒等码。 -/
namespace PPAC.Migration.Internal.SyntaxWeakenFreeLogical
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxWeakenFreeSyntax (weakened)
open SyntaxIdentityMapSyntax (identityCode)
open SyntaxFreeShiftSyntax (shiftCode)
open SyntaxLogicalSyntax (singleCode binaryCode quantifierTag)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B n q x X R S : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w a R)) (hS : Derives Γ (shiftCode w b B S))
    (hn : Derives Γ (singleCode 4 w x n)) (hq : Derives Γ (singleCode 4 w X q)) :
    Derives Γ ((weakened w a b B n q).iff (weakened w a b B x X)) := by
  have hp := SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B n q R S hw hR hS
  have hr := SyntaxRenameCodeFields.single_iff hZ 4 false (Or.inl ⟨rfl, rfl⟩)
    w R S a b a B n q x X hw (SyntaxIdentityCode.map_code w a R hR)
      (SyntaxFreeShiftCode.map_code w b B S hS) hn hq
  have hc := SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B x X R S hw hR hS
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans hp hr)
    (.conjI (.conjR hc) (.conjL hc))

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w a b B n q x y X Y R S : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w a R)) (hS : Derives Γ (shiftCode w b B S))
    (hn : Derives Γ (binaryCode kind w x y n)) (hq : Derives Γ (binaryCode kind w X Y q)) :
    Derives Γ ((weakened w a b B n q).iff
      ((weakened w a b B x X).conj (weakened w a b B y Y))) := by
  have hp := SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B n q R S hw hR hS
  have hr := SyntaxRenameCodeFields.binary_iff hZ kind w R S a b a B n q x y X Y hw
    (SyntaxIdentityCode.map_code w a R hR) (SyntaxFreeShiftCode.map_code w b B S hS) hn hq
  have hx := SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B x X R S hw hR hS
  have hy := SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B y Y R S hw hR hS
  have hc := FormulaCodeCongruence.conj_congr hx hy
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans hp hr)
    (.conjI (.conjR hc) (.conjL hc))

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w a b B n q x X R S u L : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w a R)) (hS : Derives Γ (shiftCode w b B S))
    (hu : Derives Γ (successor u a)) (hL : Derives Γ (identityCode w u L))
    (hn : Derives Γ (singleCode (quantifierTag universal) w x n))
    (hq : Derives Γ (singleCode (quantifierTag universal) w X q)) :
    Derives Γ ((weakened w a b B n q).iff (weakened w u b B x X)) := by
  have hp := SyntaxWeakenFreeUnique.at_codes_iff hZ w a b B n q R S hw hR hS
  have hl := SyntaxWeakenFreeLift.identity_lift hZ w a R u L hw hR hu hL
  have hr := SyntaxRenameCodeFields.quantified_at_lift hZ universal w R S a b a B n q x X u u L hw
    (SyntaxFreeShiftCode.map_code w b B S hS) hl hn hq
  have hc := SyntaxWeakenFreeUnique.at_codes_iff hZ w u b B x X L S hw hL hS
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans hp hr)
    (.conjI (.conjR hc) (.conjL hc))

theorem forall_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B n q x X R S u L : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w a R)) (hS : Derives Γ (shiftCode w b B S))
    (hu : Derives Γ (successor u a)) (hL : Derives Γ (identityCode w u L))
    (hn : Derives Γ (singleCode 9 w x n)) (hq : Derives Γ (singleCode 9 w X q)) :
    Derives Γ ((weakened w a b B n q).iff (weakened w u b B x X)) :=
  quantified_iff hZ true w a b B n q x X R S u L hw hR hS hu hL hn hq

theorem exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w a b B n q x X R S u L : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w a R)) (hS : Derives Γ (shiftCode w b B S))
    (hu : Derives Γ (successor u a)) (hL : Derives Γ (identityCode w u L))
    (hn : Derives Γ (singleCode 10 w x n)) (hq : Derives Γ (singleCode 10 w X q)) :
    Derives Γ ((weakened w a b B n q).iff (weakened w u b B x X)) :=
  quantified_iff hZ false w a b B n q x X R S u L hw hR hS hu hL hn hq

end PPAC.Migration.Internal.SyntaxWeakenFreeLogical
