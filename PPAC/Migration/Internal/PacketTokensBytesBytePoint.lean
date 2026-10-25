import PPAC.Migration.Internal.PacketTokensBytesByteSyntax
import PPAC.Migration.Internal.PacketVarintExecutionLiterals
import PPAC.Migration.Internal.PacketVarintExecutionHelpers

/-! Actual token Nil/Cons encodings preserve the original byte bound through independent canonical segments and actual splice. -/
namespace PPAC.Migration.Internal.PacketTokensBytesBytePoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokensBytesByteSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem nil_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n bytes : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) : Derives Γ (PacketByteInputSyntax.byteList w bytes) := by
  have hNil := Derives.impE (.conjL (PacketTokensBytes.nil_iff hZ w n bytes hw hn)) he
  exact PacketVarintExecutionHelpers.nil_input hZ w bytes hw hNil

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n bytes : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hn : Derives Γ (StructuralListSyntax.consCode w h t n)) (hIH : Derives Γ (property w t))
    (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) : Derives Γ (PacketByteInputSyntax.byteList w bytes) := by
  have hCase := Derives.impE (.conjL (PacketTokensBytes.cons_iff hZ w h t n bytes hw hh ht hn)) he
  let R := PacketTokensBytes.consBody w h t bytes
  let Δ := Context.add R (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 R _ hCase
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ2 := HornBinderRules.zf_body 2 hZ R
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw R)
  have hIH2 := of_eq (property_rename w t (old 2)) (HornBinderRules.under_body 2 hIH R)
  have hCanonical := PacketVarintExecutionLiterals.byte_input hZ2 (old 2 w) (old 2 h) (slot 2 0) hw2 (.conjL hR)
  have hTail := at_bytes (old 2 w) (old 2 t) (slot 2 1) hIH2 (.conjL (.conjR hR))
  exact of_eq (PacketByteInputSyntax.byteList_rename w bytes (old 2)).symm
    (StructuralListSpliceByte.byte_input hZ2 (old 2 w) (slot 2 0) (slot 2 1) (old 2 bytes) hw2 hCanonical hTail (.conjR (.conjR hR)))

end PPAC.Migration.Internal.PacketTokensBytesBytePoint
