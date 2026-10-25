import PPAC.Migration.Internal.PacketTokensBytesByte
import PPAC.Migration.Internal.PacketByteInputFields
import PPAC.Migration.Internal.PacketReaderTokensRoundtrip

/-! Independent token encodings have the original full byte range, all actual fields are bounded, and one unique bounded actual input carries every initialized reader return equation. -/
namespace PPAC.Migration.Internal.PacketTokensBytesByteConsequences
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem bounds_at_length {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n bytes C l : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (PacketTokensBytes.encoded w n bytes))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hl : Derives Γ (StructuralListLengthSyntax.hasLength w bytes l)) :
    Derives Γ (PacketByteInputSyntax.bounds w C bytes l) :=
  PacketByteInputFields.bounds_at_length hZ w C bytes l hw hC (PacketTokensBytesByte.byte_input hZ w n bytes hw he) hl

theorem byte_at_field {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n bytes l i y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (PacketTokensBytes.encoded w n bytes))
    (hl : Derives Γ (StructuralListLengthSyntax.hasLength w bytes l)) (hi : Derives Γ (.mem i l))
    (hy : Derives Γ (StructuralListFieldSyntax.field w bytes i y)) : Derives Γ (PacketByteInputSyntax.byte y) :=
  PacketByteInputFields.byte_at_field hZ w bytes l i y hw (PacketTokensBytesByte.byte_input hZ w n bytes hw he) hl hi hy

theorem at_encoded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n bytes : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (PacketTokensBytes.encoded w n bytes)) :
    Derives Γ ((PacketByteInputSyntax.byteList w bytes).conj (PacketReaderTokensRoundtrip.allReturns w n bytes)) :=
  .conjI (PacketTokensBytesByte.byte_input hZ w n bytes hw he) (PacketReaderTokensRoundtrip.all_returns hZ w n bytes hw he)

def boundedBody {m} (w n : Fin m) : Formula (m+1) :=
  (PacketReaderTokensRoundtrip.completeBody w n).conj (PacketByteInputSyntax.byteList w.castSucc (Fin.last m))

def boundedComplete {m} (w n : Fin m) : Formula m := .ex (boundedBody w n)

theorem boundedComplete_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (boundedComplete w n).rename ρ = boundedComplete (ρ w) (ρ n) := by
  simp only [boundedComplete,boundedBody,PacketReaderTokensRoundtrip.completeBody,Formula.rename,
    PacketTokensBytes.encoded_rename,PacketTokensBytes.uniqueAt_rename,PacketReaderTokensRoundtrip.allReturns_rename,
    PacketByteInputSyntax.byteList_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_bounded {m} {Γ : Context m} (w n bytes : Fin m)
    (hb : Derives Γ (.mem bytes w)) (he : Derives Γ (PacketTokensBytes.encoded w n bytes))
    (hu : Derives Γ (PacketTokensBytes.uniqueAt w n bytes)) (hr : Derives Γ (PacketReaderTokensRoundtrip.allReturns w n bytes))
    (hB : Derives Γ (PacketByteInputSyntax.byteList w bytes)) : Derives Γ (boundedComplete w n) := by
  apply Derives.exI bytes
  exact of_eq (by simp only [boundedBody,PacketReaderTokensRoundtrip.completeBody,Formula.instantiate,Formula.rename,
    PacketTokensBytes.encoded_rename,PacketTokensBytes.uniqueAt_rename,PacketReaderTokensRoundtrip.allReturns_rename,
    PacketByteInputSyntax.byteList_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq])
    (.conjI (.conjI (.conjI hb he) (.conjI hu hr)) hB)

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListTraceSyntax.valid w n)) : Derives Γ (boundedComplete w n) := by
  let R := PacketReaderTokensRoundtrip.completeBody w n
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (PacketReaderTokensRoundtrip.exists_unique hZ w n hw hn)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hByte := PacketTokensBytesByte.byte_input hZ1 w.castSucc n.castSucc (Fin.last m) hw1 (.conjR (.conjL hR))
  have hout := intro_bounded w.castSucc n.castSucc (Fin.last m) (.conjL (.conjL hR)) (.conjR (.conjL hR)) (.conjL (.conjR hR)) (.conjR (.conjR hR)) hByte
  simpa only [Formula.raise,boundedComplete_rename] using hout

end PPAC.Migration.Internal.PacketTokensBytesByteConsequences
