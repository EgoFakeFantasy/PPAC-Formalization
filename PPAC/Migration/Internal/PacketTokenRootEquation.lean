import PPAC.Migration.Internal.PacketTokenRootLarge

/-! The specified token root has exactly the original small and large recursive cases. -/
namespace PPAC.Migration.Internal.PacketTokenRootEquation
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokenRootSyntax

theorem condition_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V n t a r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V))
    (hr : Derives Γ (PacketTokenSyntax.row w n t a r)) :
    Derives Γ ((PacketTraceSyntax.condition w r).iff (criterion w B V n t a)) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketTokenDispatch.condition_iff_outcomes hZ w B C n t a r V hw hB hC hv hr)
    (SyntaxTypeLocalTransfer.disj_congr (PacketTokenRootSmall.small_iff hZ w B V n t a r hw hr)
      (PacketTokenRootLarge.large_iff hZ w B V n t a r hw hr))

theorem member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V n t a r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V))
    (hr : Derives Γ (PacketTokenSyntax.row w n t a r)) :
    Derives Γ ((Formula.mem r V).iff (criterion w B V n t a)) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketTraceCore.member_iff w V r hv) (condition_iff hZ w B C V n t a r hw hB hC hv hr)

end PPAC.Migration.Internal.PacketTokenRootEquation
