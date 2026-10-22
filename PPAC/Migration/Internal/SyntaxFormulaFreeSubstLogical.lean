import PPAC.Migration.Internal.SyntaxFormulaFreeSubstUnique
import PPAC.Migration.Internal.SyntaxWeakenFreeLift
import PPAC.Migration.Internal.SyntaxRenameCodeFields
import PPAC.Migration.Internal.FormulaCodeCongruence

/-! 原项列表参数的free替换逻辑端点双条件；量词下bound恒等真实提升、原free列表保持。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaFreeSubstLogical
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxFormulaFreeSubstSyntax (substituted)
open SyntaxIdentityMapSyntax (identityCode)
open SyntaxFreeSubstSyntax (codeConversion)
open SyntaxLogicalSyntax (singleCode binaryCode quantifierTag)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem negation_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w b a c L n q x X R S : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w b R)) (hS : Derives Γ (codeConversion w a c L S))
    (hn : Derives Γ (singleCode 4 w x n)) (hq : Derives Γ (singleCode 4 w X q)) :
    Derives Γ ((substituted w b a c L n q).iff (substituted w b a c L x X)) := by
  have hp := SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L n q R S hw hR hS
  have hr := SyntaxRenameCodeFields.single_iff hZ 4 false (Or.inl ⟨rfl, rfl⟩)
    w R S b a b c n q x X hw (SyntaxIdentityCode.map_code w b R hR)
      (SyntaxFreeSubstCode.map_of_conversion w a c L S hS) hn hq
  have hc := SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L x X R S hw hR hS
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans hp hr)
    (.conjI (.conjR hc) (.conjL hc))

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w b a c L n q x y X Y R S : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w b R)) (hS : Derives Γ (codeConversion w a c L S))
    (hn : Derives Γ (binaryCode kind w x y n)) (hq : Derives Γ (binaryCode kind w X Y q)) :
    Derives Γ ((substituted w b a c L n q).iff
      ((substituted w b a c L x X).conj (substituted w b a c L y Y))) := by
  have hp := SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L n q R S hw hR hS
  have hr := SyntaxRenameCodeFields.binary_iff hZ kind w R S b a b c n q x y X Y hw
    (SyntaxIdentityCode.map_code w b R hR) (SyntaxFreeSubstCode.map_of_conversion w a c L S hS) hn hq
  have hx := SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L x X R S hw hR hS
  have hy := SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L y Y R S hw hR hS
  have hc := FormulaCodeCongruence.conj_congr hx hy
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans hp hr)
    (.conjI (.conjR hc) (.conjL hc))

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool)
    (w b a c L n q x X R S u K : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w b R)) (hS : Derives Γ (codeConversion w a c L S))
    (hu : Derives Γ (successor u b)) (hK : Derives Γ (identityCode w u K))
    (hn : Derives Γ (singleCode (quantifierTag universal) w x n))
    (hq : Derives Γ (singleCode (quantifierTag universal) w X q)) :
    Derives Γ ((substituted w b a c L n q).iff (substituted w u a c L x X)) := by
  have hp := SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w b a c L n q R S hw hR hS
  have hl := SyntaxWeakenFreeLift.identity_lift hZ w b R u K hw hR hu hK
  have hr := SyntaxRenameCodeFields.quantified_at_lift hZ universal w R S b a b c n q x X u u K hw
    (SyntaxFreeSubstCode.map_of_conversion w a c L S hS) hl hn hq
  have hc := SyntaxFormulaFreeSubstUnique.at_codes_iff hZ w u a c L x X K S hw hK hS
  exact SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans hp hr)
    (.conjI (.conjR hc) (.conjL hc))

theorem forall_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w b a c L n q x X R S u K : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w b R)) (hS : Derives Γ (codeConversion w a c L S))
    (hu : Derives Γ (successor u b)) (hK : Derives Γ (identityCode w u K))
    (hn : Derives Γ (singleCode 9 w x n)) (hq : Derives Γ (singleCode 9 w X q)) :
    Derives Γ ((substituted w b a c L n q).iff (substituted w u a c L x X)) :=
  quantified_iff hZ true w b a c L n q x X R S u K hw hR hS hu hK hn hq

theorem exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w b a c L n q x X R S u K : Fin m) (hw : Derives Γ (omega w))
    (hR : Derives Γ (identityCode w b R)) (hS : Derives Γ (codeConversion w a c L S))
    (hu : Derives Γ (successor u b)) (hK : Derives Γ (identityCode w u K))
    (hn : Derives Γ (singleCode 10 w x n)) (hq : Derives Γ (singleCode 10 w X q)) :
    Derives Γ ((substituted w b a c L n q).iff (substituted w u a c L x X)) :=
  quantified_iff hZ false w b a c L n q x X R S u K hw hR hS hu hK hn hq

end PPAC.Migration.Internal.SyntaxFormulaFreeSubstLogical
