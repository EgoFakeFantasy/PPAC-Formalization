import PPAC.Migration.Internal.PacketTokensBytesByteInduction

/-! Every actual independent token encoding satisfies the original global byte-list bound, including all internal nonstandard lengths. -/
namespace PPAC.Migration.Internal.PacketTokensBytesByte
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem byte_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n bytes : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) :
    Derives Γ (PacketByteInputSyntax.byteList w bytes) :=
  PacketTokensBytesByteSyntax.at_bytes w n bytes
    (PacketTokensBytesByteInduction.at_code hZ w n hw (StructuralListValidity.range w n (PacketTokensBytes.input_valid w n bytes he))) he

end PPAC.Migration.Internal.PacketTokensBytesByte
