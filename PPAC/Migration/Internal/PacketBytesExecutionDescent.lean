import PPAC.Migration.Internal.PacketBytesExecutionAffine

/-! Real original Cons bounds prove strict child-code descent before any joint IH is invoked. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionDescent
open Source SourceAlgebra SourceLogic OmegaSyntax PacketBytesTraceSyntax PacketByteInputSyntax PacketBytesExecutionSyntax

theorem input_tail_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h x : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (hh : Derives Γ (byte h)) (hx : Derives Γ (byteList w x)) : Derives Γ (property w x) := by
  have hhW := PacketByteInputLaws.byte_natural hZ w h hw hh
  have hxW := PacketByteInputLaws.natural w x hx
  have hl := StructuralConsCore.components hZ w h x n hw hhW hxW hc
  exact earlier_at w n x hi hxW (.conjR hl)

theorem accepted_tail_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a h x u : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (hx : Derives Γ (bytes w x t u)) (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) : Derives Γ (property w x) := by
  have hh := Derives.conjL (PacketBytesExecutionAffine.data hZ w h u a hw ha)
  have hhW := PacketByteInputLaws.byte_natural hZ w h hw hh
  have hxW := PacketBytesExecutionAffine.bytes_input_natural w x t u hx
  have hl := StructuralConsCore.components hZ w h x n hw hhW hxW hc
  exact earlier_at w n x hi hxW (.conjR hl)

end PPAC.Migration.Internal.PacketBytesExecutionDescent
