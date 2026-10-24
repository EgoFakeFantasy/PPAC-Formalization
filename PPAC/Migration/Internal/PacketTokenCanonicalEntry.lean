import PPAC.Migration.Internal.PacketTokenAcceptedSyntax

/-! Actual canonical entry membership is equivalent to the independently defined acceptance formula. -/
namespace PPAC.Migration.Internal.PacketTokenCanonicalEntry
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokenSyntax PacketTokenAcceptedSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem entry_iff {m} {Γ : Context m} (tag : Nat) (w V n t a : Fin m)
    (hv : Derives Γ (PacketTraceCore.value w V)) : Derives Γ ((tagEntry tag w V n t a).iff (tagAccepted tag w n t a)) := by
  apply FormulaCodeCongruence.ex_congr
  have hv1 := of_eq (PacketTraceCore.value_rename w V Fin.castSucc) (Derives.rename Fin.castSucc hv)
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (PacketTraceCore.member_iff w.castSucc V.castSucc (Fin.last m) hv1)

theorem affine_entry_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d q n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((tagEntry (PacketAffineRuleData.relation wide) w V d q n).iff (PacketAffineSyntax.affine w B d q n)) :=
  SyntaxTypeLocalTransfer.iff_trans (entry_iff (PacketAffineRuleData.relation wide) w V d q n hv)
    (PacketAffineAccepted.accepted_iff hZ wide w B d q n hw hB)

end PPAC.Migration.Internal.PacketTokenCanonicalEntry
