import PPAC.Migration.Internal.StructuralListSpliceByteInduction

/-! Actual splice preserves the original independent ByteList predicate on all internal candidate lists. -/
namespace PPAC.Migration.Internal.StructuralListSpliceByte
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem byte_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C T L : Fin m)
    (hw : Derives Γ (omega w)) (hC : Derives Γ (PacketByteInputSyntax.byteList w C))
    (hT : Derives Γ (PacketByteInputSyntax.byteList w T))
    (hSplice : Derives Γ (StructuralListSpliceSyntax.splice w C T L)) :
    Derives Γ (PacketByteInputSyntax.byteList w L) := by
  have hp := StructuralListSpliceByteInduction.at_code hZ w C hw (PacketByteInputLaws.natural w C hC)
  have hCase := StructuralListSpliceByteSyntax.at_fields w C T L hp hC
  exact .impE (.impE hCase hT) hSplice

end PPAC.Migration.Internal.StructuralListSpliceByte
