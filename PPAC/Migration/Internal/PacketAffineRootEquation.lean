import PPAC.Migration.Internal.PacketAffineRootStep

/-! Exact root predecessor equation, with actual finite application fields aligned to the queried root. -/
namespace PPAC.Migration.Internal.PacketAffineRootEquation
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem step_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((PacketTraceSyntax.step w r V).iff (PacketAffineRootSyntax.criterion wide w B V d t n)) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketAffineDispatch.step_iff_outcomes hZ wide w B d t n r V hw hB hr)
    (SyntaxTypeLocalTransfer.disj_congr (PacketAffineRootBase.base_iff hZ wide w B d t n r hw hr)
      (PacketAffineRootStep.step_iff hZ wide w B V d t n r hw hr))

theorem member_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t n r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) (hr : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((Formula.mem r V).iff (PacketAffineRootSyntax.criterion wide w B V d t n)) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketTraceCore.member_iff w V r hv)
    (SyntaxTypeLocalTransfer.iff_trans (PacketTraceCore.unfold_iff hZ w V r hw hv) (step_iff hZ wide w B V d t n r hw hB hr))

end PPAC.Migration.Internal.PacketAffineRootEquation
