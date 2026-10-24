import PPAC.Migration.Internal.PacketVarintCellSyntax

/-! Natural domains and actual small/continuation construction are original object derivations. -/
namespace PPAC.Migration.Internal.PacketVarintCell
open Source SourceAlgebra SourceLogic OmegaSyntax PacketVarintCellSyntax

theorem head_natural {m} {Γ : Context m} (w B x h u v : Fin m) (hc : Derives Γ (cell w B x h u v)) : Derives Γ (.mem h w) := .conjL hc

theorem prior_natural {m} {Γ : Context m} (w B x h u v : Fin m) (hc : Derives Γ (cell w B x h u v)) : Derives Γ (.mem u w) := .conjL (.conjR hc)

theorem output_guard {m} {Γ : Context m} (w B x h u v : Fin m) (hc : Derives Γ (cell w B x h u v)) : Derives Γ (.mem v w) := .conjL (.conjR (.conjR hc))

theorem terminal_cell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B x h z : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hx : Derives Γ (StructuralListSyntax.nilCode w x))
    (hz : Derives Γ (empty z)) (hh : Derives Γ (.mem h B)) : Derives Γ (cell w B x h z h) := by
  have hhN := StructuralListTraceOrder.member_member hZ w h B hw hB hh
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  exact .conjI hhN (.conjI hzN (.conjI hhN (.disjL (.conjI hx (.conjI hz (.conjI hh (.eqRefl h)))))))

theorem continuation_cell {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B x h u v d : Fin m)
    (hw : Derives Γ (omega w)) (hu : Derives Γ (empty u).neg) (ha : Derives Γ (PacketAffineSyntax.affine w B d u v))
    (hs : Derives Γ (NaturalAdditionSyntax.sum w d B h)) : Derives Γ (cell w B x h u v) := by
  have hd := PacketAffineCore.digit_natural hZ w B d u v hw ha
  have hh := NaturalAdditionCore.closure w d B h (ZFContext.arithmetic hZ).base.extensionality hw hd hs
  exact .conjI hh (.conjI (PacketAffineCore.tail_guard _ _ _ _ _ ha)
    (.conjI (PacketAffineCore.output_guard _ _ _ _ _ ha) (.disjR (intro_continuation w B h u v d hu ha hs))))

end PPAC.Migration.Internal.PacketVarintCell
